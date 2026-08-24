;;; test-m15-timers.scm --- M15 imp-4 round-trip identity gate test
;;; corpus for the timer firing core cutover.
;;;
;;; Drives the two elisp-visible C entry points that now dispatch into
;;; (emacs timers): (--timer-check) (the M14 shim, keyboard.c:4931)
;;; and (current-idle-time) (its DEFUN, keyboard.c:5975).  This proves
;;; the *cutover* — that both C entry points reach the Scheme bodies
;;; through scm_c_public_ref + SCM_CALL_0 — which imp-1 (shim-level)
;;; and imp-2 (body-level) do not.  Mirrors test-m14-predicates.scm.
;;;
;;; Sourced by test/keyboard/test-m15-timers.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp.  See docs/m15-plan.org §imp-4 and brief.org.
;;;
;;; Seeding uses the imp-1 C shims (--timer-pending-funcalls[-set!],
;;; --rc-timer-start-idle/--rc-timer-stop-idle, --timers-run) and the
;;; same make-timer fixture vectors as test-m15-bodies.scm.  Every
;;; sub-test that mutates shared process state (timer-list,
;;; timer-idle-list, timer-event-last, current-time-list, idle state,
;;; pending_funcalls) runs inside a dynamic-wind that restores it —
;;; process-global state is shared with every other test in the suite
;;; (brief.org; same discipline as test-m15-bodies.scm).

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
;;; (high, usec, psec) verbatim.  So a timer's fire time is
;;; (slots 1 2 3 8) = (HIGH LOW USEC PSEC).
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

;;; --- 0. Registration: the two elisp-visible entry points ------------
;;; Guard against a missing/renamed DEFUN (the C-helper-masquerading-
;;; as-elisp trap, house rule).  --timer-check is the M14 shim whose
;;; body is `timer_check (); return Qnil;`; current-idle-time is the
;;; M15 imp-3 thin dispatcher.
(for-each
 (lambda (n)
   (check (string-append "registered:" (symbol->string n))
          #t (not (eq? (%sym n) #nil))))
 '(--timer-check current-idle-time))

;;; --- 1. Invalid, through the cutover --------------------------------
;;; Empty timer-list/timer-idle-list: (--timer-check) runs with no
;;; error and returns nil (the shim's fixed contract).
(let ((saved-timers (symbol-value 'timer-list))
      (saved-idle (symbol-value 'timer-idle-list)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'timer-list #nil)
               (set-symbol-value! 'timer-idle-list #nil))
    (lambda ()
      (check "timers/invalid-no-error" #t
             (no-error? (lambda () ((%sym '--timer-check)))))
      (check "timers/invalid-returns-nil" #nil
             ((%sym '--timer-check))))
    (lambda () (set-symbol-value! 'timer-list saved-timers)
               (set-symbol-value! 'timer-idle-list saved-idle))))

;;; --- 2. Wait, through the cutover -----------------------------------
;;; One future ordinary timer (year 2100): (--timer-check) runs with
;;; no error and leaves the timer unfired (slot 0 stays nil).  NOTE:
;;; from outside the shim this looks identical to case 1 — the shim
;;; always returns nil and fires nothing — intentional; see the
;;; "Important scoping note" in brief.org.  We assert only what is
;;; observable here, not a fake distinguishing signal.
(let ((saved-timers (symbol-value 'timer-list))
      (saved-idle (symbol-value 'timer-idle-list))
      (future (make-timer 0 4102444800 0 0)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'timer-list (elist future))
               (set-symbol-value! 'timer-idle-list #nil))
    (lambda ()
      (check "timers/wait-no-error" #t
             (no-error? (lambda () ((%sym '--timer-check)))))
      (check "timers/wait-not-fired" #nil (vector-ref future 0)))
    (lambda () (set-symbol-value! 'timer-list saved-timers)
               (set-symbol-value! 'timer-idle-list saved-idle))))

;;; --- 3. Ripe fire path, single call fires all ripe timers -----------
;;; Two ripe ordinary timers (epoch, slot 0 = nil).  A single
;;; (--timer-check) call fires *both*: the Scheme timer-check's
;;; do-while loop (fires the list head each pass) must survive the C
;;; round trip.  A raw t value would not prove this — firing more than
;;; one timer from one call is the real signal.  Assert slot 0 = t on
;;; both, timer-event-last set, and --timers-run bumped by exactly 2.
(let ((saved-timers (symbol-value 'timer-list))
      (saved-idle (symbol-value 'timer-idle-list))
      (saved-last (symbol-value 'timer-event-last))
      (before ((%sym '--timers-run)))
      (timer-a (make-timer 0 0 0 0))
      (timer-b (make-timer 0 0 0 0)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'timer-list (elist timer-a timer-b))
               (set-symbol-value! 'timer-idle-list #nil))
    (lambda ()
      (check "timers/ripe-no-error" #t
             (no-error? (lambda () ((%sym '--timer-check)))))
      (check "timers/ripe-a-fired" #t (truthy? (vector-ref timer-a 0)))
      (check "timers/ripe-b-fired" #t (truthy? (vector-ref timer-b 0)))
      (check "timers/ripe-event-last" #t
             (not (eq? (symbol-value 'timer-event-last) saved-last)))
      (check "timers/ripe-timers-run-bumped-2"
             (+ before 2) ((%sym '--timers-run))))
    (lambda () (set-symbol-value! 'timer-list saved-timers)
               (set-symbol-value! 'timer-idle-list saved-idle)
               (set-symbol-value! 'timer-event-last saved-last))))

;;; --- 4. Idle vs. ordinary ordering, through the cutover -------------
;;; Same fixture shape as test-m15-bodies.scm §4: wrap in
;;; --rc-timer-start-idle/--rc-timer-stop-idle, seed a ripe idle timer
;;; and a future ordinary timer, call (--timer-check), assert the idle
;;; timer fired and the ordinary one did not.
(let ((saved-timers (symbol-value 'timer-list))
      (saved-idle (symbol-value 'timer-idle-list))
      (saved-last (symbol-value 'timer-event-last)))
  (dynamic-wind
    (lambda () ((%sym '--rc-timer-start-idle))
               (set-symbol-value! 'timer-idle-list #nil)
               (set-symbol-value! 'timer-list #nil))
    (lambda ()
      (let ((idle-timer (make-timer 0 0 0 0))  ; elapsed-idle 0, ripe
            (future (make-timer 0 4102444800 0 0)))
        (set-symbol-value! 'timer-list (elist future))
        (set-symbol-value! 'timer-idle-list (elist idle-timer))
        (check "timers/idle-vs-ordinary-no-error" #t
               (no-error? (lambda () ((%sym '--timer-check)))))
        (check "timers/idle-vs-ordinary-fired-idle"
               #t (truthy? (vector-ref idle-timer 0)))
        (check "timers/idle-vs-ordinary-not-ordinary"
               #nil (vector-ref future 0))))
    (lambda ()
      ((%sym '--rc-timer-stop-idle))
      (set-symbol-value! 'timer-list saved-timers)
      (set-symbol-value! 'timer-idle-list saved-idle)
      (set-symbol-value! 'timer-event-last saved-last))))

;;; --- 5. pending_funcalls drain, through the cutover -----------------
;;; Seed one (FUN . ARGS) entry via --timer-pending-funcalls-set!,
;;; with both list globals nil (so the drain is the only observable
;;; effect — no timer firing to confound it).  Call (--timer-check).
;;; Assert the seeded function ran exactly once and the queue is empty
;;; afterward.
(let ((saved-queue ((%sym '--timer-pending-funcalls)))
      (saved-timers (symbol-value 'timer-list))
      (saved-idle (symbol-value 'timer-idle-list))
      (calls 0))
  (set-symbol-function! 'm15-timers-drain-mark
                        (lambda () (set! calls (1+ calls))))
  (dynamic-wind
    (lambda () ((%sym '--timer-pending-funcalls-set!)
                (elist (cons 'm15-timers-drain-mark #nil)))
               (set-symbol-value! 'timer-list #nil)
               (set-symbol-value! 'timer-idle-list #nil))
    (lambda ()
      ((%sym '--timer-check))          ; drains before the invalid check
      (check "timers/drain-runs-once" 1 calls)
      (check "timers/drain-queue-empty" #nil
             ((%sym '--timer-pending-funcalls))))
    (lambda () ((%sym '--timer-pending-funcalls-set!) saved-queue)
               (set-symbol-value! 'timer-list saved-timers)
               (set-symbol-value! 'timer-idle-list saved-idle))))

;;; --- 6. Copy-window smoke, through the cutover ----------------------
;;; Seed timer-list with one *unripe* timer (future fixture) so
;;; (--timer-check) does not mutate it.  Call (--timer-check).  Assert:
;;; no error, and the timer-list global itself is unchanged (eq? to
;;; what was set) — timer_check copies the list for internal use, it
;;; must not replace the live global.  (This is the imp-4 "smoke" level
;;; the plan asks for; it does not attempt to observe the atimers on/off
;;; toggle, which has no elisp-visible signal.)
(let* ((saved-timers (symbol-value 'timer-list))
       (saved-idle (symbol-value 'timer-idle-list))
       (future (make-timer 0 4102444800 0 0))
       (seeded (elist future)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'timer-list seeded)
               (set-symbol-value! 'timer-idle-list #nil))
    (lambda ()
      (check "timers/copy-window-no-error" #t
             (no-error? (lambda () ((%sym '--timer-check)))))
      ;; eq? identity, not structural equality — timer_check must not
      ;; replace the live global with a copy (brief.org:162).
      (check "timers/copy-window-list-unchanged" #t
             (eq? seeded (symbol-value 'timer-list)))
      (check "timers/copy-window-timer-unfired" #nil (vector-ref future 0)))
    (lambda () (set-symbol-value! 'timer-list saved-timers)
               (set-symbol-value! 'timer-idle-list saved-idle))))

;;; --- 7. current-idle-time, through the cutover -----------------------
;;; Mirror test-m15-bodies.scm §6 exactly, but call the elisp
;;; (current-idle-time) function instead of the Scheme procedure:
;;; - not idle -> nil.
;;; - idle (wrap in --rc-timer-start-idle/--rc-timer-stop-idle) ->
;;;   a 4-element list of integers.
;;; - idle with current-time-list set to nil -> a (TICKS . HZ) pair,
;;;   HZ = 1000000000.
;; Call the elisp DEFUN via its function cell (symbol-function), not the
;; Scheme procedure directly — this corpus proves the C entry point's
;; cutover, so the call must go through Fcurrent_idle_time.
(check "idle-time/not-idle-nil" #nil ((%sym 'current-idle-time)))
(let ()
  (dynamic-wind
    (lambda () ((%sym '--rc-timer-start-idle)))
    (lambda ()
      (let ((r ((%sym 'current-idle-time))))
        (check "idle-time/when-idle-list4" #t
               (and (pair? r) (pair? (cdr r)) (pair? (cddr r))
                    (pair? (cdddr r)) (eq? (cddddr r) #nil)))
        (check "idle-time/when-idle-integers" #t
               (and (integer? (car r)) (integer? (cadr r))
                    (integer? (caddr r)) (integer? (cadddr r))))))
    (lambda () ((%sym '--rc-timer-stop-idle)))))

;; current-time-list = nil -> make_lisp_time returns (TICKS . HZ) where
;; HZ = 1e9, not the 4-item list (cr.org Finding 1).
(let ((saved-ctl (symbol-value 'current-time-list)))
  (dynamic-wind
    (lambda () ((%sym '--rc-timer-start-idle))
               (set-symbol-value! 'current-time-list #nil))
    (lambda ()
      (let ((r ((%sym 'current-idle-time))))
        (check "idle-time/ticks-hz-pair" #t (pair? r))
        (check "idle-time/ticks-hz-ratio" 1000000000 (cdr r))
        (check "idle-time/ticks-integer" #t (integer? (car r)))))
    (lambda ()
      ((%sym '--rc-timer-stop-idle))
      (set-symbol-value! 'current-time-list saved-ctl))))
