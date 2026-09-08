;;; test-m27-ring-storage.scm --- M27 imp-4 test corpus for the raw
;;; kbd_buffer[] ring storage + its Scheme store/get/dispatch path.
;;;
;;; Covers the M27 imp-4 ring-storage deliverable (brief.org M27 imp-4):
;;; the ring stays an opaque C buffer and its 11 raw-storage accessor
;;; DEFUNs stay C (see [[kbd-ring-stays-opaque-c-buffer]]), while the
;;; store/get/dispatch policy lives in (emacs kbd-buffer).  This corpus
;;; exercises store -> get -> dispatch through the C ring end to end:
;;;
;;;   - store: seed one ASCII keystroke through --kbd-store-buffered-event,
;;;     the real C entry kbd_buffer_store_buffered_event (the M13
;;;     dispatcher: C guard + ie_wrap + SCM_CALL_2 into
;;;     kbd-buffer-store-event!);
;;;   - ring state: read the raw ring with --kbd-buffer-nr-stored,
;;;     --kbd-event-kind and --kbd-event-ie (raw-storage accessors);
;;;   - get + dispatch: kbd-buffer-get-event, which dispatches through
;;;     dispatch-event! and returns the char code of the ASCII event;
;;;   - verify the dispatched event matches the stored key (code 97).
;;;
;;; Every seeded sub-test runs inside a dynamic-wind that saves and
;;; restores the fetch/store cursors and the process-global cells the
;;; dispatch touches (unread-command-events, last-event-frame,
;;; last-event-device, internal-last-event-frame), so nothing leaks into
;;; later corpora
;;; ([[shared-harness-cross-corpus-state-leak]]).
;;;
;;; The batch fast-path trap (same as test-kbd-wait-loop.scm): in batch
;;; noninteractive is t, so kbd-buffer-get-event's fast path would read
;;; getchar() (or fall through on DBus/file-notify/threads builds)
;;; instead of draining the ring.  The get/dispatch step binds the elisp
;;; `noninteractive` variable to nil so the wait loop is reached on
;;; every build and breaks on the stored queue event.
;;;
;;; Sourced by test/keyboard/test-m27-ring-storage.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp.  See brief.org M27 imp-4.

(use-modules (emacs kbd-buffer))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

;; Run THUNK with the elisp `noninteractive` variable bound to nil, so
;; the wait loop is reached even in batch.  Same save/restore idiom as
;; test-kbd-wait-loop.scm (set-symbol-value! is the C-backed one at
;; runtime and writes the DEFVAR_BOOL through).
(define (with-noninteractive-nil thunk)
  (let ((saved (symbol-value 'noninteractive)))
    (dynamic-wind
      (lambda () (set-symbol-value! 'noninteractive #nil))
      thunk
      (lambda () (set-symbol-value! 'noninteractive saved)))))

;; Kind constant — the authoritative value dispatch compares against
;; (no DEFUN exposes the enum; read via @@ like test-m13-store.scm).
(define ASCII-KEYSTROKE-EVENT (@@ (emacs kbd-buffer) ASCII-KEYSTROKE-EVENT))

(define KBD-BUFFER-SIZE 4096)

;;; --- 0. Registration: the raw-storage accessors resolve ---------------
;; Guards against a missing/renamed DEFUN (the
;; C-helper-masquerading-as-elisp trap, house rule).  These 8 are the
;; raw ring store/get/set/state DEFUNs the corpus drives; the rest of
;; the 11 raw accessors are exercised elsewhere (test-m13/m14 shims).
(for-each
 (lambda (n)
   (check (string-append "m27-ring/registered:" (symbol->string n))
          #t (not (eq? (%sym n) #nil))))
 '(--kbd-fetch-ptr-index --kbd-store-ptr-index --kbd-buffer-nr-stored
   --kbd-event-kind --kbd-event-ie --kbd-set-fetch-ptr-index
   --kbd-set-store-ptr-index --kbd-store-buffered-event))

;;; --- 1. Store -> ring state -> get/dispatch round trip ----------------

;; Seed one ASCII keystroke (code 97 = `a', modifiers 0) at a known
;; empty base on the ring, then drive it through the real C store entry,
;; read the raw ring, and dispatch it back out with kbd-buffer-get-event.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       ;; dispatch-event! / the get-event epilogue write these elisp/CF
       ;; globals (last-event-frame, last-event-device,
       ;; internal-last-event-frame) and the store side touches
       ;; unread-command-events — restore every one so this corpus never
       ;; leaks process-global state into later corpora
       ;; ([[shared-harness-cross-corpus-state-leak]]).
       (saved-uce (symbol-value 'unread-command-events))
       (saved-last-ev (symbol-value 'last-event-frame))
       (saved-last-dev (symbol-value 'last-event-device))
       (saved-int-frame ((%sym '--get-internal-last-event-frame)))
       ;; frame_or_window = the selected frame, so dispatch-event!'s
       ;; switch-frame synthesis sees frame == selected-frame and stays
       ;; silent (same shape test-kbd-wait-loop.scm §6 relies on).
       (ie ((%sym '--ie-test-event)
            ASCII-KEYSTROKE-EVENT 97 0 ((%sym 'selected-frame)))))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ;; Empty the ring at a known base (both cursors aligned).
      ((%sym '--kbd-set-fetch-ptr-index) 0)
      ((%sym '--kbd-set-store-ptr-index) 0)
      ;; (1) store through the real C ring entry (no hold-quit).
      ((%sym '--kbd-store-buffered-event) ie #nil)
      ;; (2) raw ring state reflects the stored event.
      (check "m27-ring/store-ptr-advances"
             (modulo (+ 0 1) KBD-BUFFER-SIZE)
             ((%sym '--kbd-store-ptr-index)))
      (check "m27-ring/nr-stored-after-store" 1
             ((%sym '--kbd-buffer-nr-stored)))
      (check "m27-ring/kind-at-slot0" ASCII-KEYSTROKE-EVENT
             ((%sym '--kbd-event-kind) 0))
      (let ((stored ((%sym '--kbd-event-ie) 0)))
        (check "m27-ring/stored-ie-code" 97 ((%sym '--ie-code) stored))
        (check "m27-ring/stored-ie-modifiers" 0
               ((%sym '--ie-modifiers) stored)))
      ;; (3) get + dispatch: disable the batch fast path, clear any
      ;; leftover Vunread, then drain the ring.  The dispatched event is
      ;; the char code of the ASCII keystroke -> it must match the key we
      ;; stored (97).
      (set-symbol-value! 'unread-command-events #nil)
      (with-noninteractive-nil
        (lambda ()
          (check "m27-ring/get-returns-stored-key" 97
                 (kbd-buffer-get-event #nil))
          (check "m27-ring/dequeued" #t
                 (= ((%sym '--kbd-fetch-ptr-index))
                    ((%sym '--kbd-store-ptr-index))))
          (check "m27-ring/nr-stored-after-get" 0
                 ((%sym '--kbd-buffer-nr-stored))))))
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
      ((%sym '--kbd-set-store-ptr-index) saved-store)
      (set-symbol-value! 'unread-command-events saved-uce)
      (set-symbol-value! 'last-event-frame saved-last-ev)
      (set-symbol-value! 'last-event-device saved-last-dev)
      ((%sym '--set-internal-last-event-frame) saved-int-frame)))

;;; --- 2. Leak guard ----------------------------------------------------

;; The unwind above restores every cell this corpus writes.  Assert the
;; process-global state is byte-for-byte back to what we found, so this
;; corpus can never leak into a later corpus in the shared (randomised)
;; keyboard emacs process (m23 default-value checks are sensitive to a
;; non-nil last-event-frame / last-event-device / ring pointer).
(check "m27-ring/leak-fetch-ptr" saved-fetch ((%sym '--kbd-fetch-ptr-index)))
(check "m27-ring/leak-store-ptr" saved-store ((%sym '--kbd-store-ptr-index)))
(check "m27-ring/leak-unread-command-events" saved-uce
       (symbol-value 'unread-command-events))
(check "m27-ring/leak-last-event-frame" saved-last-ev
       (symbol-value 'last-event-frame))
(check "m27-ring/leak-last-event-device" saved-last-dev
       (symbol-value 'last-event-device))
(check "m27-ring/leak-internal-last-event-frame" saved-int-frame
       ((%sym '--get-internal-last-event-frame))))
