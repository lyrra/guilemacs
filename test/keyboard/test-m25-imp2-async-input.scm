;;; test-m25-imp2-async-input.scm --- M25 imp-2 (emacs gobble) test corpus.
;;;
;;; Covers the M25 imp-2 cutover (brief.org M25): handle_async_input and
;;; process_pending_signals (src/keyboard.c) became thin dispatchers into
;;; (emacs gobble) as handle-async-input! and process-pending-signals!.
;;; The dropped-platform HAVE_ANDROID / DOS_NT arms were deleted, not
;;; ported; neither entry point has an early-init caller.  The C cells
;;; pending_signals and the atimer machinery stay C behind the
;;; single-purpose shims --pending-signals-clear! and --do-pending-atimers!.
;;; This corpus exercises the moved policy logic:
;;;
;;;   - handle-async-input! calls --gobble-input until it reports no more
;;;     input (0) or a blocked read (negative);
;;;   - handle-async-input! stops on a negative (blocked) return;
;;;   - process-pending-signals! runs the three steps in order: clear the
;;;     flag, then drain input, then run atimers once, last.
;;;
;;; gobble.scm references its C primitives through defelisp delays
;;; ((force %--...)), so these tests stub those delays by replacing them
;;; inside the (emacs gobble) module (module-set!), restoring after —
;;; the same stub mechanism test-m25-imp1-user-signal.scm uses (verified
;;; to take effect against this declarative module).  Every stub is
;;; restored in a dynamic-wind unwind, so nothing leaks into later
;;; corpora ([[shared-harness-cross-corpus-state-leak]]).
;;;
;;; Sourced by test/keyboard/test-m25-imp2-async-input.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See brief.org M25 imp-2.

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

;; A queue stub for --gobble-input: each call pops the next return value
;; from VALS (a closure-captured list) and records a 'gobble step into
;; the shared ORDER via RECORD!, returning the popped value.
(define (make-gobble-queue vals record!)
  (lambda ()
    (record! 'gobble)
    (let ((v (car vals)))
      (set! vals (cdr vals))
      v)))

;;; --- 1. handle-async-input!: drain until 0 ---------------------------

;; Queue (3 2 0): the drain loop calls --gobble-input once per positive
;; return, then sees 0 and stops.  Exactly three calls, and it stops on 0
;; (does not read past the queue).
(define drain-calls 0)
(define drain-extra-read 0)
(define drain-values '(3 2 0))
(define drain-gobble
  (lambda ()
    (if (null? drain-values)
        (set! drain-extra-read (1+ drain-extra-read)))
    (let ((v (if (null? drain-values) 0 (car drain-values))))
      (set! drain-values (if (null? drain-values) '() (cdr drain-values)))
      (set! drain-calls (1+ drain-calls))
      v)))
(with-gobble-delay! '%--gobble-input drain-gobble
  (lambda ()
    (handle-async-input!)
    (check "handle-async-input!/drains-until-zero-calls" 3 drain-calls)
    (check "handle-async-input!/drains-until-zero-no-extra"
           0 drain-extra-read)))

;; First call returns -1 (blocked input): the loop breaks immediately.
;; Exactly one call.
(define blocked-calls 0)
(with-gobble-delay! '%--gobble-input
    (lambda () (set! blocked-calls (1+ blocked-calls)) -1)
  (lambda ()
    (handle-async-input!)
    (check "handle-async-input!/stops-on-blocked-calls" 1 blocked-calls)))

;; Apply several with-gobble-delay! stubs at once (flattened to avoid
;; the paren imbalance of deep nesting): PAIRS is a list of (name proc)
;; pairs, all stubbed for the duration of THUNK.
(define (with-many-delays! pairs thunk)
  (if (null? pairs)
      (thunk)
      (with-gobble-delay! (caar pairs) (cadar pairs)
        (lambda () (with-many-delays! (cdr pairs) thunk)))))

;;; --- 2. process-pending-signals!: order of the three steps -----------

;; Record each dependency call in ORDER (a shared list, rebuilt and
;; assigned by every step's stub); --gobble-input drains a (2 0) queue so
;; the drain step makes two gobble calls.  Expected order: clear, gobble,
;; gobble, atimers.  atimers runs exactly once, last.
(define order '())
(define (record-step! step) (set! order (append order (list step))))
(with-many-delays!
 (list
  (list '%--pending-signals-clear!
        (lambda () (record-step! 'clear) #nil))
  (list '%--gobble-input
        (make-gobble-queue '(2 0) record-step!))
  (list '%--do-pending-atimers!
        (lambda () (record-step! 'atimers) #nil)))
 (lambda ()
   (process-pending-signals!)
   (check "process-pending-signals!/order"
          '(clear gobble gobble atimers) order)
   (check "process-pending-signals!/atimers-last"
          'atimers (list-ref order (1- (length order))))))

;;; --- 3. Cutover wiring ------------------------------------------------
;;; handle_async_input / process_pending_signals (C) must resolve the
;;; (emacs gobble) public refs.  Verify both are exported procedures of
;;; the module (their bodies are exercised in sections 1-2).
(check "gobble/exported-handle-async-input!" #t
       (procedure? (module-ref (resolve-interface '(emacs gobble))
                               'handle-async-input!)))
(check "gobble/exported-process-pending-signals!" #t
       (procedure? (module-ref (resolve-interface '(emacs gobble))
                               'process-pending-signals!)))
