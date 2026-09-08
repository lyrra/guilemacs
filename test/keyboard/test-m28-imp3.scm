;;; test-m28-imp3.scm --- M28 imp-3 test corpus for the batched ring
;;; cursor reads + the wait-path forwarder cut-overs.
;;;
;;; brief.org (M28 imp-3) reduces C↔Scheme crossings on the all-Scheme
;;; read path three ways.  This corpus asserts the deliverable that
;;; does NOT need the performance harness:
;;;
;;;   - the new batching subr --kbd-empty-p registers and behaves
;;;     (one atomic empty/non-empty test); an early --kbd-peek-event
;;;     sibling was REMOVED after it regressed the bench (cr.org F3 —
;;;     see dispatch-event! in kbd-buffer.scm), so the dispatch
;;;     prologue keeps its three scalar crossings;
;;;   - the queue-empty tests in kbd-buffer.scm now agree with
;;;     --kbd-empty-p (they no longer compare two index reads);
;;;   - dispatch-event! still dispatches a stored event correctly
;;;     through the scalar prologue (pipeline sanity, char code 0);
;;;   - some-mouse-moved / gobble-input! are exported from their home
;;;     modules and load together with (emacs kbd-buffer) /
;;;     (emacs main-queue) (the cut-over imports are cycle-free).
;;;
;;; Phase 3 (getctag bracket collapse via set-ctag-returns-old) is
;;; SKIPPED — --set-ctag documents "return TAG" (mirrors
;;; set-current-kboard) and test-m12-shims.scm pins that contract
;;; (ctag/set-returns-tag); set-and-return-old would break it.
;;; Recorded in docs/m28-plan.org §imp-3; no assertion here depends
;;; on it.
;;;
;;; Same harness as test-m27-ring-storage.scm: Sourced by the .el
;;; wrapper via eval-scheme; accumulates (NAME STATUS) pairs into
;;; test-results for readback from elisp.
;;;
;;; The batch fast-path trap (same as test-m27-ring-storage.scm): in
;;; batch `noninteractive' is t, so kbd-buffer-get-event's fast path
;;; would read getchar() instead of draining the ring.  The pipeline
;;; step binds `noninteractive' to nil so the wait loop is reached and
;;; breaks on the stored queue event.

(use-modules (emacs kbd-buffer))
(use-modules (emacs main-queue))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

(define (truthy? x)
  (not (eq? x #nil)))

(define ASCII-KEYSTROKE-EVENT (@@ (emacs kbd-buffer) ASCII-KEYSTROKE-EVENT))
(define KBD-BUFFER-SIZE 4096)

;; Run THUNK with the elisp `noninteractive' variable bound to nil, so
;; the wait loop is reached even in batch.
(define (with-noninteractive-nil thunk)
  (let ((saved (symbol-value 'noninteractive)))
    (dynamic-wind
      (lambda () (set-symbol-value! 'noninteractive #nil))
      thunk
      (lambda () (set-symbol-value! 'noninteractive saved)))))

;;; --- 0. Registration ------------------------------------------------
;; The new batching subr must resolve (guard against a missing /
;; renamed DEFUN).  --kbd-peek-event no longer exists (removed for the
;; bench regression, cr.org F3) — do not re-add a registration for it.
(check "m28-imp3/registered:--kbd-empty-p" #t
       (not (eq? (%sym '--kbd-empty-p) #nil)))

;;; --- 1. --kbd-empty-p agrees with (= fetch store) -------------------
;; Align both cursors (empty ring), then store one event (non-empty),
;; then drain (empty again).  --kbd-empty-p must agree with the
;; two-index comparison at every state.
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (ie ((%sym '--ie-test-event)
            ASCII-KEYSTROKE-EVENT 0 0 ((%sym 'selected-frame)))))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) 0)
      ((%sym '--kbd-set-store-ptr-index) 0)
      ;; Empty state.
      (check "m28-imp3/empty-p-empty" #t
             (truthy? ((%sym '--kbd-empty-p))))
      (check "m28-imp3/empty-p-agrees" #t
             (eq? (truthy? ((%sym '--kbd-empty-p)))
                  (= ((%sym '--kbd-fetch-ptr-index))
                     ((%sym '--kbd-store-ptr-index)))))
      ;; Non-empty state.
      ((%sym '--kbd-store-buffered-event) ie #nil)
      (check "m28-imp3/empty-p-nonempty" #f
             (truthy? ((%sym '--kbd-empty-p))))
      (check "m28-imp3/empty-p-agrees-nonempty" #t
             (eq? (truthy? ((%sym '--kbd-empty-p)))
                  (= ((%sym '--kbd-fetch-ptr-index))
                     ((%sym '--kbd-store-ptr-index))))))
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
      ((%sym '--kbd-set-store-ptr-index) saved-store))))

;;; --- 2. dispatch prologue scalar reads agree -------------------------
;; The dispatch prologue (cr.org F3) reads the current event as three
;; scalar crossings — fetch-ptr-index, event-kind(idx), event-ie(idx)
;; — NOT a batched --kbd-peek-event (removed; it regressed the bench).
;; After storing one ASCII event at a known base, the three scalar
;; reads must agree: idx = fetch-ptr-index, kind = event-kind(idx),
;; and the ie wraps the same slot (--ie-kind ie == kind).
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (saved-uce (symbol-value 'unread-command-events))
       (saved-last-ev (symbol-value 'last-event-frame))
       (saved-last-dev (symbol-value 'last-event-device))
       (saved-int-frame ((%sym '--get-internal-last-event-frame)))
       (ie ((%sym '--ie-test-event)
            ASCII-KEYSTROKE-EVENT 0 0 ((%sym 'selected-frame)))))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) 0)
      ((%sym '--kbd-set-store-ptr-index) 0)
      ((%sym '--kbd-store-buffered-event) ie #nil)
      ;; The exact read sequence dispatch-event! uses today.
      (let* ((idx ((%sym '--kbd-fetch-ptr-index)))
             (kind ((%sym '--kbd-event-kind) idx))
             (ie* ((%sym '--kbd-event-ie) idx)))
        (check "m28-imp3/dispatch-scalar/idx" 0 idx)
        (check "m28-imp3/dispatch-scalar/kind" ASCII-KEYSTROKE-EVENT kind)
        (check "m28-imp3/dispatch-scalar/ie-kind-matches" kind
               ((%sym '--ie-kind) ie*)))
      ;; the reads must not advance the fetch ptr.
      (check "m28-imp3/dispatch-scalar/no-advance" 0
             ((%sym '--kbd-fetch-ptr-index))))
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
      ((%sym '--kbd-set-store-ptr-index) saved-store)
      (set-symbol-value! 'unread-command-events saved-uce)
      (set-symbol-value! 'last-event-frame saved-last-ev)
      (set-symbol-value! 'last-event-device saved-last-dev)
      ((%sym '--set-internal-last-event-frame) saved-int-frame))))

;;; --- 3. Module wiring (cut-over imports are cycle-free) -------------
;; The direct Scheme calls now replace the C forwarders inside
;; (emacs kbd-buffer).  The home modules must load and export the
;; functions; (emacs kbd-buffer) / (emacs main-queue) must still load.
(let* ((rks (resolve-module '(emacs read-key-sequence)))
       (gob (resolve-module '(emacs gobble))))
  (check "m28-imp3/mod/read-key-sequence-exports-some-mouse-moved" #t
         (and rks (not (eq? (module-variable rks 'some-mouse-moved) #f))))
  (check "m28-imp3/mod/gobble-exports-gobble-input!" #t
         (and gob (not (eq? (module-variable gob 'gobble-input!) #f))))
  (check "m28-imp3/mod/kbd-buffer-loads" #t
         (not (eq? (resolve-module '(emacs kbd-buffer)) #f)))
  (check "m28-imp3/mod/main-queue-loads" #t
         (not (eq? (resolve-module '(emacs main-queue)) #f))))

;;; --- 4. Pipeline sanity: store -> read-decoded -> char code 0 -------
;; Store one ASCII keystroke of code 0 (NUL), disable the batch fast
;; path, clear any leftover Vunread, then read it back through the
;; full main-queue port (read-decoded-event-from-main-queue).  The
;; decoded event must be the char code we stored (0), and the ring must
;; be drained (empty-p true again).
(let* ((saved-fetch ((%sym '--kbd-fetch-ptr-index)))
       (saved-store ((%sym '--kbd-store-ptr-index)))
       (saved-uce (symbol-value 'unread-command-events))
       (saved-last-ev (symbol-value 'last-event-frame))
       (saved-last-dev (symbol-value 'last-event-device))
       (saved-int-frame ((%sym '--get-internal-last-event-frame)))
       (saved-ctag ((%sym '--get-ctag)))
       (ie ((%sym '--ie-test-event)
            ASCII-KEYSTROKE-EVENT 0 0 ((%sym 'selected-frame)))))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) 0)
      ((%sym '--kbd-set-store-ptr-index) 0)
      ((%sym '--kbd-store-buffered-event) ie #nil)
      (set-symbol-value! 'unread-command-events #nil)
      (with-noninteractive-nil
        (lambda ()
          (call-with-values
              (lambda ()
                (read-decoded-event-from-main-queue #nil 'tag #nil))
            (lambda (event umm)
              (check "m28-imp3/pipeline/returns-char-0" 0 event)
              (check "m28-imp3/pipeline/umm" #nil umm)))))
      ;; ring drained back to empty.
      (check "m28-imp3/pipeline/drained" #t
             (truthy? ((%sym '--kbd-empty-p))))
      (check "m28-imp3/pipeline/nr-stored-0" 0
             ((%sym '--kbd-buffer-nr-stored))))
    (lambda ()
      ((%sym '--kbd-set-fetch-ptr-index) saved-fetch)
      ((%sym '--kbd-set-store-ptr-index) saved-store)
      (set-symbol-value! 'unread-command-events saved-uce)
      (set-symbol-value! 'last-event-frame saved-last-ev)
      (set-symbol-value! 'last-event-device saved-last-dev)
      ((%sym '--set-internal-last-event-frame) saved-int-frame)
      ((%sym '--set-ctag) saved-ctag))))
