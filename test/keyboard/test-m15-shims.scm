;;; test-m15-shims.scm --- M15 imp-1 test corpus for the C timer-fire
;;; shim DEFUNs in src/keyboard.c: --timer-check-2,
;;; --timer-get-pending-funcalls-drain!, --timer-fire-ripe,
;;; --timer-copy-window, and --timespec-diff-to-now (plus the two
;;; test-support pending_funcalls accessors used to seed the drain).
;;;
;;; Sourced by test/keyboard/test-m15-shims.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp.  See docs/m15-plan.org §imp-1 and brief.org.

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

(define (elist . items)
  (let loop ((i items))
    (if (null? i) #nil (cons (car i) (loop (cdr i))))))

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

;;; --- helper: build a 10-element timer vector ------------------------
;;; decode_timer reads slot0 (triggered), slot2 (low-secs, must be a
;;; fixnum), and slots 1/3/8 as the other three time parts
;;; (high, usec, psec) verbatim.  So for the C shims a timer's fire
;;; time is (slots 1 2 3 8) = (HIGH LOW USEC PSEC).
(define (make-timer high low usec psec)
  (vector #nil        ; slot0 triggered-p (nil = not yet fired)
          high        ; slot1 high-secs
          low         ; slot2 low-secs
          usec        ; slot3 usecs
          #nil        ; slot4 repeat-delay (nil = non-repeating timer)
          #nil        ; slot5 function
          #nil        ; slot6 args
          #nil        ; slot7 idle-delay
          psec        ; slot8 psecs (read as PSEC by decode_timer)
          #nil))      ; slot9 next

;;; --- 0. Registration: the 5 shims + 2 test-support accessors -------
(define shim-names
  '(--timer-check-2 --timer-get-pending-funcalls-drain!
    --timer-fire-ripe --timer-copy-window --timespec-diff-to-now
    --timer-pending-funcalls --timer-pending-funcalls-set!))
(for-each
 (lambda (n)
   (check (string-append "registered:" (symbol->string n))
          #t (not (eq? (%sym n) #nil))))
 shim-names)

;;; --- 1. --timer-check-2 three-way decode ---------------------------
;;; Contract: nil = invalid, t = {0,0} "fired, call again",
;;; (SEC . NSEC) = wait until the next timer is ripe.

;;; invalid: no ordinary or idle timer active.
(check "check-2/invalid" #nil
       ((%sym '--timer-check-2) #nil #nil))

;;; ripe: a timer whose time is already in the past (epoch) is fired.
(let* ((past (make-timer 0 0 0 0)))
  (check "check-2/ripe-again" #t
         ((%sym '--timer-check-2) (elist past) #nil))
  (check "check-2/ripe-marked" #t (truthy? (vector-ref past 0))))

;;; wait: a timer whose time is in the future returns (SEC . NSEC),
;;; positive, and is left unfired.
(let* ((future (make-timer 0 4102444800 0 0)))  ; year 2100
  (let* ((r ((%sym '--timer-check-2) (elist future) #nil)))
    (check "check-2/wait-pair" #t (pair? r))
    (check "check-2/wait-positive" #t (> (car r) 0))
    (check "check-2/wait-not-fired" #nil (vector-ref future 0))))

;;; --- 2. drain shim: seed pending_funcalls, drain, verify empty ------
;;; The drain runs each entry via elisp (apply FUN ARGS...), so FUN
;;; must be a symbol whose elisp function cell holds a callable
;;; procedure — bind one via set-symbol-function!.
(let ((calls 0))
  (set-symbol-function! 'm15-drain-mark
                        (lambda () (set! calls (1+ calls))))
  ((%sym '--timer-pending-funcalls-set!)
   (elist (cons 'm15-drain-mark #nil)))  ; one (FUN . ARGS) entry
  ((%sym '--timer-get-pending-funcalls-drain!))
  (check "drain/runs-once" 1 calls)
  (check "drain/queue-empty" #nil
         ((%sym '--timer-pending-funcalls))))

;;; --- 3. fire shim: handler runs, slot0 = t, timers_run bumps --------
;;; timer-event-handler records the last-run timer in timer-event-last
;;; before anything else, so we can observe that the handler was
;;; invoked without needing the timer registered in timer-list.
(let* ((before ((%sym '--timers-run)))
       (timer (make-timer 0 0 0 0)))
  ((%sym '--timer-fire-ripe) timer)
  (check "fire/handler-ran" timer (symbol-value 'timer-event-last))
  (check "fire/slot0-t" #t (truthy? (vector-ref timer 0)))
  (check "fire/timers-run-bumped" (1+ before) ((%sym '--timers-run))))

;;; --- 4. copy-window shim: returns the two lists unchanged ----------
;;; Snapshot Vtimer-list/Vtimer-idle-list at call time.  The ordinary
;;; copy must equal the live Vtimer-list value; the idle copy is nil
;;; when not idle (the usual test state).  Read-only: we do not mutate
;;; the live list, so timer machinery is never handed non-timers.
(let* ((r ((%sym '--timer-copy-window)))
       (timers (car r))
       (idle (cdr r)))
  (check "copy-window/returns-pair" #t (pair? r))
  (check "copy-window/timers-match" (symbol-value 'timer-list) timers)
  (check "copy-window/idle-nil-or-list"
         #t (or (eq? idle #nil) (pair? idle))))

;;; --- 5. --timespec-diff-to-now: (SEC . NSEC), sign by ripeness ------
;;; A past timer decodes to a past instant, so the diff is positive.
(let* ((past (make-timer 0 0 0 0))
       (r ((%sym '--timespec-diff-to-now) past)))
  (check "diff-to-now/pair" #t (pair? r))
  (check "diff-to-now/overdue-positive" #t (> (car r) 0)))
