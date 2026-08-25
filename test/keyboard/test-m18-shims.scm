;;; test-m18-shims.scm --- M18 imp-1 test corpus for the C shim DEFUNs in
;;; src/keyboard.c: --set-echoing!, --message3-nolog,
;;; --rc-pin-echo-kboard-to-current, --waiting-for-input-p,
;;; --truncate-echo-area.
;;;
;;; Sourced by test/keyboard/test-m18-shims.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp.  See docs/m18-plan.org §imp-1 and brief.org.

(use-modules (ice-9 rdelim))

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

;;; --- 0. Registration: all 5 shims resolve ---------------------------
(define shim-names
  '(--set-echoing! --message3-nolog
    --rc-pin-echo-kboard-to-current --waiting-for-input-p
    --truncate-echo-area))
(for-each
 (lambda (n)
   (check (string-append "registered:" (symbol->string n))
          #t (not (eq? (%sym n) #nil))))
 shim-names)

;;; --- 1. --set-echoing!: raw bool setter -----------------------------
;;; No direct getter exists to read `echoing` back (only handle_interrupt
;;; reads it, not test-reachable).  A plain no-error call check is the
;;; agreed contract; do not invent a getter (out of scope for imp-1).
(check "set-echoing!/t-no-error" #t (no-error? (lambda () ((%sym '--set-echoing!) #t))))
(check "set-echoing!/nil-no-error" #t (no-error? (lambda () ((%sym '--set-echoing!) #nil))))

;;; --- 2. --waiting-for-input-p: predicate on the C flag ---------------
;;; In batch there is no pending read, so the flag is clear.
(check "waiting-for-input-p/initially-nil" #nil ((%sym '--waiting-for-input-p)))
;;; Clearing an already-clear flag stays clear, and is safe (no signal).
(check "waiting-for-input-p/clear-noop" #nil
       ((%sym '--clear-waiting-for-input)))
(check "waiting-for-input-p/after-clear" #nil ((%sym '--waiting-for-input-p)))

;;; --- 3. --message3-nolog: thin xdisp.c wrapper -----------------------
;;; Call with a string, confirm no error.  Do not assert on echo-area
;;; display state (xdisp side effects are out of scope for this corpus
;;; family).
(check "message3-nolog/string-no-error" #t
       (no-error? (lambda () ((%sym '--message3-nolog) "M18 imp-1 test"))))

;;; --- 4. --rc-pin-echo-kboard-to-current: raw pointer pin -------------
;;; No direct getter exists for echo_kboard either; a no-error call
;;; check is enough, same reasoning as --set-echoing!.
(check "rc-pin-echo-kboard-to-current/no-error" #t
       (no-error? (lambda () ((%sym '--rc-pin-echo-kboard-to-current)))))

;;; --- 5. --truncate-echo-area: thin xdisp.c wrapper + CHECK_FIXNUM ----
;;; A fixnum argument must not signal.
(check "truncate-echo-area/fixnum-no-error" #t
       (no-error? (lambda () ((%sym '--truncate-echo-area) 0))))
;;; A non-fixnum argument must signal (CHECK_FIXNUM), not silently wrap.
(check "truncate-echo-area/non-fixnum-signals" #t
       (not (eq? (no-error? (lambda () ((%sym '--truncate-echo-area) #t)))
                 #t)))
(check "truncate-echo-area/string-signals" #t
       (not (eq? (no-error? (lambda () ((%sym '--truncate-echo-area) "x")))
                 #t)))
