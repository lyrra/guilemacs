;;; test-m25-imp1-user-signal.scm --- M25 imp-1 (emacs gobble) test corpus.
;;;
;;; Covers the M25 imp-1 cutover (brief.org M25): the user-signal drain
;;; *policy* moved out of src/keyboard.c into (emacs gobble) as
;;; store-user-signal-events!.  The raw C list and the primitives
;;; (--user-signal-list, --user-signal-pending,
;;; --user-signal-pending-decrement!, --ie-user-signal-event) stay C
;;; (handle_user_signal touches the list from a signal handler).  This
;;; corpus exercises the moved policy logic:
;;;
;;;   - store-user-signal-events! drains each pending count into exactly
;;;     one USER_SIGNAL_EVENT per pending signal and stops at zero;
;;;   - store-user-signal-events! is a no-op when nothing is pending.
;;;
;;; (cr.org Finding 1 removed the abandoned add-user-signal! registration
;;; dispatcher and its two primitives; the old add: checks were dropped.)
;;;
;;; gobble.scm references its C primitives through defelisp delays
;;; ((force %--...)), so these tests stub those delays by replacing them
;;; inside the (emacs gobble) module (module-set!), restoring after —
;;; the same stub mechanism test-m19-*.scm use.  kbd-buffer-store-event!
;;; is reached through gobble.scm's lazy %kbd-buffer-store-event! delay
;;; and stubbed the same way.  Every stub is restored in a dynamic-wind
;;; unwind, so nothing leaks into later
;;; corpora ([[shared-harness-cross-corpus-state-leak]]).
;;;
;;; Sourced by test/keyboard/test-m25-imp1-user-signal.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See brief.org M25 imp-1.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))
(use-modules (emacs gobble))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

;;; --- Stub helpers ----------------------------------------------------

(define gobble-mod (resolve-module '(emacs gobble)))

;; Replace the defelisp delay NAME in (emacs gobble) so that
;; (force NAME) yields PROC, restoring the original delay after THUNK.
(define (with-gobble-delay! name proc thunk)
  (let ((old (module-ref gobble-mod name)))
    (dynamic-wind
      (lambda () (module-set! gobble-mod name (delay proc)))
      thunk
      (lambda () (module-set! gobble-mod name old)))))

;; Override gobble.scm's delayed %kbd-buffer-store-event! reference for
;; the duration of THUNK (same mechanism as the other delays).
(define (with-store-stub! proc thunk)
  (with-gobble-delay! '%kbd-buffer-store-event! proc thunk))

;;; --- 1. store-user-signal-events!: drain loop -------------------------

;; Drain a signal with 2 pending events: exactly two USER_SIGNAL_EVENT
;; stores (and two --ie-user-signal-event fills), in order, then the
;; pending count reaches zero and the loop terminates.
(define drain-calls 0)
(define ie-fill-calls 0)
(define drain-pending 0)
(with-gobble-delay! '%--user-signal-list (lambda () (list 99))
  (lambda ()
    (with-gobble-delay! '%--user-signal-pending
        (lambda (sig) drain-pending)
      (lambda ()
        (with-gobble-delay! '%--user-signal-pending-decrement!
            (lambda (sig)
              (set! drain-pending (1- drain-pending))
              drain-pending)
          (lambda ()
            (with-gobble-delay! '%--ie-user-signal-event
                (lambda (sig) (set! ie-fill-calls (1+ ie-fill-calls)) (list 'ie sig))
              (lambda ()
                (with-store-stub!
                    (lambda (ie hq) (set! drain-calls (1+ drain-calls)) #nil)
                  (lambda ()
                    (set! drain-pending 2)
                    (store-user-signal-events!)
                    (check "store-user-signal-events!/drains-pending-stores"
                           2 drain-calls)
                    (check "store-user-signal-events!/drains-pending-ie-fills"
                           2 ie-fill-calls)
                    (check "store-user-signal-events!/drains-pending-zero"
                           0 drain-pending)))))))))))

;; No pending events -> no store, no event fill, loop no-op.
(define noop-calls 0)
(define noop-ie-calls 0)
(with-gobble-delay! '%--user-signal-list (lambda () (list 99))
  (lambda ()
    (with-gobble-delay! '%--user-signal-pending (lambda (sig) 0)
      (lambda ()
        (with-gobble-delay! '%--ie-user-signal-event
            (lambda (sig) (set! noop-ie-calls (1+ noop-ie-calls)) (list 'ie sig))
          (lambda ()
            (with-store-stub!
                (lambda (ie hq) (set! noop-calls (1+ noop-calls)) #nil)
              (lambda ()
                (store-user-signal-events!)
                (check "store-user-signal-events!/no-pending-is-noop"
                       0 noop-calls)
                (check "store-user-signal-events!/no-pending-no-ie-fill"
                       0 noop-ie-calls)))))))))

;;; --- 2. Cutover wiring ------------------------------------------------
;;; store_user_signal_events (C) must resolve the (emacs gobble) public
;;; ref.  Verify it is an exported procedure of the module (its body is
;;; exercised in section 1).
(check "gobble/exported-store-user-signal-events!" #t
       (procedure? (module-ref (resolve-interface '(emacs gobble))
                               'store-user-signal-events!)))
