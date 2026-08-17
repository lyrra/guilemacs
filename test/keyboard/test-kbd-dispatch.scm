;;; test-kbd-dispatch.scm --- M11 imp-3 dispatch-switch test corpus for
;;; (emacs kbd-buffer)
;;;
;;; Sourced by test/keyboard/test-kbd-dispatch.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch
;;; stdout.
;;;
;;; Covers the dispatch-event! port of the C `switch (event->kind)`
;;; block (src/keyboard.c:5195-5480): pass-through kinds, the
;;; default-path (ASCII keystroke), the swallowed kinds (selection /
;;; monitors-changed / menu-bar-activate), multibyte decode +
;;; incremental, pinch coalescing, switch-frame synthesis, and the
;;; imp-5 F1 event-kboard write-back (--ie-kboard + dispatch).
;;;
;;; Events are stuffed via --kbd-buffer-store-fake-event (kind [arg]);
;;; it always stores frame_or_window = selected frame and device = Qt.
;;; For switch-frame and pinch, the frame_or_window field is rewritten
;;; with --set-ie-frame-or-window to a fixnum sentinel: this build
;;; cannot create a second frame in batch (make-frame /
;;; make-terminal-frame error), so the sentinel exercises the
;;; switch-frame comparison against selected_frame, and a non-live
;;; sentinel frame makes mle-pinch-event return nil early (skipping
;;; make-lispy-position, which segfaults on the batch termcap frame —
;;; a pre-existing M9 imp-6.3 issue, not imp-3).

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

;; dispatch-event! is module-private; reach it through @@ (same idiom
;; as test-kbd-wait-loop.scm's %daemonp rebinding).
(define dispatch-event! (@@ (emacs kbd-buffer) dispatch-event!))

;;; --- Helpers ----------------------------------------------------------

(define KBD-SIZE 4096)

(define (kind name)
  ((%sym '--ie-kind-from-name) name))

(define (drain-queue!)
  ;; Discard everything by moving the fetch ptr to the store ptr.
  ((%sym '--kbd-set-fetch-ptr-index) ((%sym '--kbd-store-ptr-index))))

(define (queue-empty?)
  (= ((%sym '--kbd-fetch-ptr-index))
     ((%sym '--kbd-store-ptr-index))))

(define (store-fake! k . maybe-arg)
  ((%sym '--kbd-buffer-store-fake-event) k
   (if (null? maybe-arg) #nil (car maybe-arg))))

(define (set-frame-or-window! idx val)
  ((%sym '--set-ie-frame-or-window)
   ((%sym '--kbd-event-ie) idx)
   val))

(define (get-last-event-frame)
  ((%sym '--get-internal-last-event-frame)))

(define (set-last-event-frame! f)
  ((%sym '--set-internal-last-event-frame) f))

;;; --- 1. Kind-name registration (no silent -1 misrouting) --------------

(for-each
 (lambda (nm)
   (check (string-append "kinds/" (symbol->string nm)) #t
          (>= (kind nm) 0)))
 '(save-session ascii-keystroke multibyte-char-keystroke pinch
   selection-clear-event monitors-changed menu-bar-activate-event))

;;; --- 2. Pass-through kind (SAVE_SESSION_EVENT) ------------------------

(drain-queue!)
(store-fake! (kind 'save-session) 7)
(check "pass-through/save-session-event" (list 'save-session 7)
       (dispatch-event!))
(check "pass-through/save-session-dequeued" #t (queue-empty?))

;;; --- 3. default-path ASCII keystroke (NOT pass-through) ---------------

(drain-queue!)
(store-fake! (kind 'ascii-keystroke))
(check "default/ascii-returns-code" 0 (dispatch-event!))
(check "default/ascii-dequeued" #t (queue-empty?))

;;; --- 4. Swallowed kinds (return 'wait, drain the queue) ---------------

;; Selection clear: --kbd-handle-selection-event advances itself.
(drain-queue!)
(store-fake! (kind 'selection-clear-event))
(check "swallow/selection-clear-returns-wait" 'wait (dispatch-event!))
(check "swallow/selection-clear-advanced" #t (queue-empty?))

;; Monitors changed: advance + run display-monitors-changed-functions.
(drain-queue!)
(store-fake! (kind 'monitors-changed) 'terminal-arg)
(check "swallow/monitors-changed-returns-wait" 'wait (dispatch-event!))
(check "swallow/monitors-changed-advanced" #t (queue-empty?))

;; Menu-bar activate: advance + --activate-menubar-hook (termcap no-op).
(drain-queue!)
(store-fake! (kind 'menu-bar-activate-event))
(check "swallow/menu-bar-activate-returns-wait" 'wait (dispatch-event!))
(check "swallow/menu-bar-activate-advanced" #t (queue-empty?))

;;; --- 5. Multibyte decode + incremental --------------------------------

;; A string arg is decoded, wrapped as (0 . "ab"), and the first
;; character is returned while the event is left in the queue; the
;; second pop returns the next character and drains the queue.
(drain-queue!)
(store-fake! (kind 'multibyte-char-keystroke) "ab")
(check "multibyte/first-char" 97 (dispatch-event!))
(check "multibyte/first-char-not-dequeued" #f (queue-empty?))
(check "multibyte/second-char" 98 (dispatch-event!))
(check "multibyte/second-char-dequeued" #t (queue-empty?))

;;; --- 6. Pinch coalescing ----------------------------------------------

;; make-lispy-event's PINCH handler (mle-pinch-event) calls
;; make-lispy-position, which segfaults on the batch termcap frame
;; (M9 imp-6.3, pre-existing).  Point frame_or_window at a non-live
;; sentinel so mle-pinch-event returns nil before reaching
;; make-lispy-position — this still runs pinch-coalesce! in full.
;; internal_last_event_frame is pre-set to the same sentinel so no
;; switch-frame is synthesized for the sentinel frame.
(let* ((sentinel 4242)
       (saved-last-frame (get-last-event-frame))
       (i0 ((%sym '--kbd-fetch-ptr-index))))
  (set-last-event-frame! sentinel)
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (store-fake! (kind 'pinch) (list 1.0 2.0 1.0 10.0))
      (store-fake! (kind 'pinch) (list 3.0 4.0 2.0 20.0))
      (store-fake! (kind 'pinch) (list 5.0 6.0 3.0 355.0))
      (for-each (lambda (off)
                  (set-frame-or-window!
                   (modulo (+ i0 off) KBD-SIZE) sentinel))
                '(0 1 2))
      (check "pinch/returns-nil" #nil (dispatch-event!))
      (check "pinch/collapsed-to-empty" #t (queue-empty?))
      ;; The coalesced totals are written into the last event's arg
      ;; (--ie-clear only resets kind, not arg): dx 1+3+5=9, dy
      ;; 2+4+6=12, angle fmod(10+20+355, 360)=25.
      (let ((arg ((%sym '--ie-arg)
                  ((%sym '--kbd-event-ie)
                   (modulo (+ i0 2) KBD-SIZE)))))
        (check "pinch/dx-sum" 9.0 (car arg))
        (check "pinch/dy-sum" 12.0 (cadr arg))
        (check "pinch/angle-fmod" 25.0 (car (cdr (cdr (cdr arg)))))))
    (lambda () (set-last-event-frame! saved-last-frame))))

;;; --- 7. Switch-frame synthesis ----------------------------------------

;; An event on a frame that is neither internal_last_event_frame nor
;; selected_frame synthesizes (switch-frame FRAME) and leaves the event
;; in the queue; the re-read then returns the real event.  A fixnum
;; sentinel stands in for a second frame (uncreatable in batch).
(let* ((sentinel 4242)
       (saved-last-frame (get-last-event-frame))
       (i0 ((%sym '--kbd-fetch-ptr-index))))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (store-fake! (kind 'ascii-keystroke))
      (set-frame-or-window! (modulo i0 KBD-SIZE) sentinel)
      (check "switch-frame/synthesized" (list 'switch-frame sentinel)
             (dispatch-event!))
      (check "switch-frame/not-dequeued" #f (queue-empty?))
      (check "switch-frame/last-event-frame-written" sentinel
             (get-last-event-frame))
      ;; Re-read: frame now equals internal_last_event_frame, so the
      ;; real ASCII event (code 0) comes through and drains the queue.
      (check "switch-frame/re-read-real-event" 0 (dispatch-event!))
      (check "switch-frame/re-read-dequeued" #t (queue-empty?)))
    (lambda () (set-last-event-frame! saved-last-frame))))

;;; --- 8. F1: event-kboard write-back (--ie-kboard + dispatch) --------

;; --ie-kboard (event_to_kboard wrapper) shape: a live-frame event
;; resolves to a kboard smob; the selection kinds resolve to nil (the C
;; event_to_kboard NULL special-case for SELECTION_*_EVENT).
(drain-queue!)
(store-fake! (kind 'ascii-keystroke))
(let ((ie ((%sym '--kbd-event-ie) ((%sym '--kbd-fetch-ptr-index)))))
  (check "ie-kboard/live-frame-is-kboard" #t
         (not (eq? ((%sym 'kboardp) ((%sym '--ie-kboard) ie)) #nil))))
(drain-queue!)

(drain-queue!)
(store-fake! (kind 'selection-clear-event))
(let ((ie ((%sym '--kbd-event-ie) ((%sym '--kbd-fetch-ptr-index)))))
  (check "ie-kboard/selection-clear-nil" #nil
         ((%sym '--ie-kboard) ie)))
(drain-queue!)

;; dispatch-event! must write *kbp = event_to_kboard (ie) on the queue
;; path, falling back to current_kboard when event_to_kboard returns
;; nil — exactly the deleted C prologue before the switch.  A real
;; KBOARD ** backs the rc-slot via the test-only storage; the reset
;; helper gives a known-null start so the write-through is observable.
(let* ((kb      ((%sym 'current-kboard)))
       (rec     ((%sym '--make-rc-state)))
       (push-f  (%sym '--rc-record-stack-push))
       (pop-f   (%sym '--rc-record-stack-pop))
       (set-f   (%sym '--rc-test-state-set!))
       (ptr-f   (%sym '--rc-test-kbp-storage-ptr))
       (val-f   (%sym '--rc-test-kbp-storage-value))
       (reset-f (%sym '--rc-test-kbp-storage-reset)))
  (set-f rec 'kbp (ptr-f))
  (push-f rec)
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ;; Live-frame event: event_to_kboard resolves the selected frame
      ;; to its kboard == current_kboard (single-kboard batch build).
      (reset-f)
      (check "dispatch/write-kbp-live-frame/initial-null" #nil (val-f))
      (drain-queue!)
      (store-fake! (kind 'ascii-keystroke))
      (dispatch-event!)
      (check "dispatch/write-kbp-live-frame/writes-through" #t
             (not (eq? ((%sym 'kboard-eq) (val-f) kb) #nil)))
      ;; Selection event: event_to_kboard returns nil, so the Scheme
      ;; fallback must still write current_kboard, not leave *kbp null.
      (reset-f)
      (check "dispatch/write-kbp-selection/initial-null" #nil (val-f))
      (drain-queue!)
      (store-fake! (kind 'selection-clear-event))
      (dispatch-event!)
      (check "dispatch/write-kbp-selection/fallback-writes-through" #t
             (not (eq? ((%sym 'kboard-eq) (val-f) kb) #nil))))
    (lambda () (pop-f))))
