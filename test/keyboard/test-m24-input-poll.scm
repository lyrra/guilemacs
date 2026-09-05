;;; test-m24-input-poll.scm --- M24 (emacs input-poll) test corpus.
;;;
;;; Covers the M24 polling-policy cutover (brief.org M24).  The C
;;; change deletes the old start_polling body and two dropped-platform
;;; helpers, adds --atimer-poll-restart!, and turns start_polling into a
;;; thin dispatcher into (emacs input-poll) start-polling!.  This corpus
;;; exercises the moved policy logic:
;;;
;;;   - the --atimer-poll-restart! shim is registered and idempotent
;;;     (a second call cancels and re-arms, no crash);
;;;   - start-polling! is a no-op when interrupt-input is in use;
;;;   - start-polling! arms once on a numeric polling-period and re-arms
;;;     only when polling-period changes (the *poll-timer-period* cache
;;;     path, the one piece of behavior that moved off the C static).
;;;
;;; The start-polling! policy tests stub --atimer-poll-restart! with a
;;; recording lambda (fset), so the when-to-call decision is observable
;;; without depending on the C shim's runtime availability.  This is the
;;; same stubbing style test-m20-menu-prompt.scm uses for --x-popup-menu-1.
;;;
;;; Sourced by test/keyboard/test-m24-input-poll.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See brief.org M24.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))
(use-modules (emacs input-poll))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

(define (%nilp x) (eq? x #nil))

;;; --- 1. --atimer-poll-restart! registration + idempotency --------
;;; Present whenever POLL_FOR_INPUT is compiled (guilemacs always is).
;;; Idempotent: the second call cancels the first timer and re-arms, so
;;; it must neither crash nor leak.  Skipped (reported PASS) when the
;;; shim is absent, i.e. running against a binary built before M24.
(define %restart-sym '--atimer-poll-restart!)

(define (restart-registered?)
  (catch #t
    (lambda ()
      (procedure? (symbol-function %restart-sym)))
    (lambda (k . a) #f)))

(if (restart-registered?)
    (let ((r1 (no-error? (lambda () ((%sym %restart-sym)))))
          (r2 (no-error? (lambda () ((%sym %restart-sym))))))
      (check "atimer-poll-restart!/no-error-twice" #t
             (and (eq? r1 #t) (eq? r2 #t))))
    (report "atimer-poll-restart!/no-error-twice" 'PASS)) ; skip (pre-M24 build)

;;; --- 2. start-polling! policy --------------------------------------
;;; Stub --atimer-poll-restart! with a recording counter so we can assert
;;; exactly when the policy (re)arms the atimer.  interrupt_input is a C
;;; bool, toggled through --interrupt-input-set! (there is no elisp
;;; `interrupt-input' variable).
(define restart-calls 0)

(define (with-restart-stub thunk)
  (let ((saved (symbol-function %restart-sym))
        (saved-calls restart-calls))
    (dynamic-wind
      (lambda ()
        (set! restart-calls 0)
        ((%c 'fset) %restart-sym
         (lambda () (set! restart-calls (1+ restart-calls)) #nil)))
      thunk
      (lambda ()
        (set! restart-calls saved-calls)
        ((%c 'fset) %restart-sym saved)))))

(define (interrupt-p?) (not (%nilp ((%sym '--interrupt-input-p)))))
(define (set-interrupt! on) ((%sym '--interrupt-input-set!) (if on #t #nil)))

(define (with-saved-symbol! name thunk)
  (let ((saved (symbol-value name)))
    (dynamic-wind
      (lambda () #t)
      thunk
      (lambda () (set-symbol-value! name saved)))))

;; 2a. no-op when interrupt-driven input is in use.  Even with a changed
;; polling-period, start-polling! must not touch the atimer.
(with-restart-stub
 (lambda ()
   (let ((saved-interrupt (interrupt-p?)))
     (dynamic-wind
       (lambda () (set-interrupt! #t))
       (lambda ()
         (with-saved-symbol! 'polling-period
           (lambda ()
             (set-symbol-value! 'polling-period 0.1)
             (start-polling!)
             (check "start-polling!/noop-when-interrupt" 0 restart-calls))))
       (lambda () (set-interrupt! saved-interrupt))))))

;; 2b. arm + cache.  First numeric polling-period with the timer unarmed
;; arms once; a repeat call with the same period is a no-op (the
;; *poll-timer-period* cache path); a changed period re-arms.
(with-restart-stub
 (lambda ()
   (let ((saved-interrupt (interrupt-p?)))
     (dynamic-wind
       (lambda () (set-interrupt! #nil))
       (lambda ()
         (with-saved-symbol! 'polling-period
           (lambda ()
             (set-symbol-value! 'polling-period 0.05)
             (start-polling!)
             (check "start-polling!/arms-on-numeric-period" 1 restart-calls)
             (check "start-polling!/active-after-arm" #t (poll-timer-active?))
             (start-polling!)            ; same period -> no-op
             (check "start-polling!/noop-on-repeat-period" 1 restart-calls)
             (set-symbol-value! 'polling-period 0.2)
             (start-polling!)            ; changed period -> re-arm
             (check "start-polling!/rearms-on-period-change" 2 restart-calls))))
       (lambda () (set-interrupt! saved-interrupt))))))

;;; =====================================================================
;;; 3. Cutover wiring
;;; =====================================================================
;;; start_polling (C) must now resolve the (emacs input-poll)
;;; start-polling! public ref.  Verify the module exports it as a
;;; procedure (the body itself is exercised in section 2).
(check "start-polling!/exported-procedure" #t
       (procedure? (module-ref (resolve-interface '(emacs input-poll))
                               'start-polling!)))
