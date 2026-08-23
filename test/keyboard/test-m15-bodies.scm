;;; test-m15-bodies.scm --- M15 imp-2 test corpus for the 4 Scheme
;;; timer procedures in (emacs timers): decode-timer, timer-check-2,
;;; timer-check, and current-idle-time.
;;;
;;; Sourced by test/keyboard/test-m15-bodies.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp.  See docs/m15-plan.org §imp-2 and brief.org.
;;;
;;; Seeding uses the imp-1 C shims (--timespec-diff-to-now,
;;; --timer-copy-window, --timer-fire-ripe, --timer-idleness-now,
;;; --timer-get-pending-funcalls-drain!) plus the test-support
;;; pending_funcalls accessors.  Every sub-test that mutates shared
;;; process state (pending_funcalls, timer-list, timer-idle-list,
;;; idle-start time, timer-event-last) runs inside a dynamic-wind that
;;; restores it — process-global state is shared with every other test
;;; in the suite (brief.org; same discipline as test-m14-bodies.scm).

(use-modules (emacs timers))

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

;;; --- 0. Registration: the module's 4 procedures + shims resolve -----
;;; Guards against a missing/renamed DEFUN (the C-helper-masquerading-
;;; as-elisp trap, house rule) and against the (emacs timers) module
;;; exporting nothing.
(for-each
 (lambda (n)
   (check (string-append "proc:" (symbol->string n))
          #t (procedure? (module-ref (resolve-module '(emacs timers)) n))))
 '(decode-timer timer-check-2 timer-check current-idle-time))
(for-each
 (lambda (n)
   (check (string-append "registered:" (symbol->string n))
          #t (not (eq? (%sym n) #nil))))
 '(--timer-idleness-now --timespec-diff-to-now --timer-copy-window
   --timer-fire-ripe --timer-get-pending-funcalls-drain!
   --timer-pending-funcalls --timer-pending-funcalls-set!
   --rc-timer-start-idle --rc-timer-stop-idle --timers-run))

;;; --- 1. decode-timer ------------------------------------------------
;;; Slot checks in order: not a 10-slot vector -> nil; slot 0 non-nil
;;; -> nil; slot 2 not a fixnum -> nil; else decode slots 1/3/8.
(check "decode/epoch" '(0 . 0)
       (decode-timer (make-timer 0 0 0 0)))
(check "decode/not-vector" #nil
       (decode-timer (list 1 2 3)))
(check "decode/not-10-slot" #nil
       (decode-timer (vector #nil 0 0 0)))
(let ((v (make-timer 0 0 0 0)))
  (vector-set! v 0 #t)                  ; already triggered
  (check "decode/slot0-t" #nil (decode-timer v)))
(let ((v (make-timer 0 0 0 0)))
  (vector-set! v 2 'x)                  ; slot2 not a fixnum
  (check "decode/slot2-not-fixnum" #nil (decode-timer v)))
(check "decode/high-carries-16" '(65536 . 0)
       (decode-timer (make-timer 1 0 0 0)))
(check "decode/low" '(65535 . 0)
       (decode-timer (make-timer 0 65535 0 0)))
(check "decode/usec" '(0 . 500000000)
       (decode-timer (make-timer 0 0 500000 0)))
(check "decode/usec-carry" '(1 . 0)
       (decode-timer (make-timer 0 0 1000000 0)))
(check "decode/psec" '(0 . 1)
       (decode-timer (make-timer 0 0 0 1000)))
;; C's decode_time_components requires slot3 (usec) and slot8 (psec) be
;; FIXNUMP and returns invalid otherwise; a non-numeric slot must not
;; throw a type error in the port (cr.org Finding 3).
(let ((v (make-timer 0 0 0 0)))
  (vector-set! v 3 'x)                  ; slot3 (usec) not a fixnum
  (check "decode/slot3-not-fixnum" #nil (decode-timer v)))
(let ((v (make-timer 0 0 0 0)))
  (vector-set! v 8 'x)                  ; slot8 (psec) not a fixnum
  (check "decode/slot8-not-fixnum" #nil (decode-timer v)))
(let ((v (make-timer 0 0 0 0)))
  (vector-set! v 1 'x)                  ; slot1 (high) not a fixnum
  (check "decode/slot1-not-fixnum" #nil (decode-timer v)))

;;; --- 2. timer-check-2 three-way contract ----------------------------
;;; nil = invalid (no active timer), t = {0,0} "fired, call again",
;;; (SEC . NSEC) = wait until the next timer is ripe.

;; invalid: no ordinary or idle timer active.
(check "check-2/invalid" #nil (timer-check-2 #nil #nil))

;; ripe ordinary (epoch, long past): fired -> t; slot0 marked; the
;; handler runs once (observed via timer-event-last); --timers-run bumps.
(let ((before ((%sym '--timers-run)))
      (saved-last (symbol-value 'timer-event-last))
      (timer (make-timer 0 0 0 0)))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (check "check-2/ripe-again" #t (timer-check-2 (elist timer) #nil))
      (check "check-2/ripe-marked" #t (truthy? (vector-ref timer 0)))
      (check "check-2/ripe-handler-ran" timer (symbol-value 'timer-event-last))
      (check "check-2/ripe-timers-run-bumped" (1+ before) ((%sym '--timers-run))))
    (lambda () (set-symbol-value! 'timer-event-last saved-last))))

;; wait ordinary (year 2100): returns a positive (SEC . NSEC) pair and
;; leaves the timer unfired.
(let* ((future (make-timer 0 4102444800 0 0))
       (r (timer-check-2 (elist future) #nil)))
  (check "check-2/wait-pair" #t (pair? r))
  (check "check-2/wait-positive" #t (> (car r) 0))
  (check "check-2/wait-not-fired" #nil (vector-ref future 0)))

;; invalid timers are skipped: a fired (slot0 = t) ordinary head is
;; advanced past, so an active tail timer is still considered.
(let ((saved-last (symbol-value 'timer-event-last))
      (fired (make-timer 0 0 0 0))
      (past (make-timer 0 0 0 0)))
  (vector-set! fired 0 #t)              ; slot0 = t -> decode invalid
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (check "check-2/skip-invalid" #t
             (timer-check-2 (elist fired past) #nil))
      (check "check-2/skip-invalid-marked" #t (truthy? (vector-ref past 0))))
    (lambda () (set-symbol-value! 'timer-event-last saved-last))))

;;; --- 3. pending_funcalls drain --------------------------------------
;;; timer-check-2 drains C's pending_funcalls first (the same live
;;; global --timer-get-pending-funcalls-drain! consumes).  Seed one
;;; (FUN . ARGS) entry and confirm it runs and the queue empties even
;;; with no timers to act on.
(let ((calls 0)
      (saved-queue ((%sym '--timer-pending-funcalls))))
  (set-symbol-function! 'm15-body-drain-mark
                        (lambda () (set! calls (1+ calls))))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((%sym '--timer-pending-funcalls-set!)
       (elist (cons 'm15-body-drain-mark #nil)))
      (timer-check-2 #nil #nil)         ; drains before the invalid check
      (check "check-2/drain-runs-once" 1 calls)
      (check "check-2/drain-queue-empty" #nil
             ((%sym '--timer-pending-funcalls))))
    (lambda () ((%sym '--timer-pending-funcalls-set!) saved-queue))))

;;; --- 4. idle-vs-ordinary ordering -----------------------------------
;;; Seed Emacs idle via --rc-timer-start-idle (makes timer_idleness_
;;; start_time valid), then hand timer-check-2 an ordinary future timer
;;; and an idle timer whose fire time (elapsed-idle coordinate) is tiny.
;;; The idle timer is ripe (idleness_now >= 0) and fires; the ordinary
;;; one is still in the future.  Restore idle state in the unwind.
(let ((saved-last (symbol-value 'timer-event-last)))
  (dynamic-wind
    (lambda () ((%sym '--rc-timer-start-idle)))
    (lambda ()
      (let ((idle-timer (make-timer 0 0 0 0))  ; elapsed-idle 0, ripe
            (future (make-timer 0 4102444800 0 0)))
        (let ((r (timer-check-2 (elist future) (elist idle-timer))))
          (check "check-2/idle-vs-ordinary-ripe" #t r)
          (check "check-2/idle-vs-ordinary-fired-idle"
                 #t (truthy? (vector-ref idle-timer 0)))
          (check "check-2/idle-vs-ordinary-not-ordinary"
                 #nil (vector-ref future 0)))))
    (lambda ()
      ((%sym '--rc-timer-stop-idle))
      (set-symbol-value! 'timer-event-last saved-last))))

;;; --- 4b. idle-vs-ordinary tie-break (cr.org Finding 2) ---------------
;;; The "choose next timer" 4-way OR (timers.scm) is the highest-risk
;;; ported line.  Test the two branches the existing section-4 case does
;;; not reach: idle waiting / ordinary ripe (C's idle_ripe < timer_ripe
;;; branch picks the ordinary timer), and a same-ripeness pair with a
;;; close non-equal difference (the timespec_cmp tie-break picks the
;;; nearer one).

;; idle waiting / ordinary ripe: the idle timer is far in the future
;; (idle-coordinate), the ordinary timer is long past, so the ordinary
;; timer must be chosen and fired.
(let ((saved-last (symbol-value 'timer-event-last)))
  (dynamic-wind
    (lambda () ((%sym '--rc-timer-start-idle)))
    (lambda ()
      (let ((idle-timer (make-timer 0 4102444800 0 0))  ; idle waiting
            (past (make-timer 0 0 0 0)))                ; ordinary ripe
        (let ((r (timer-check-2 (elist past) (elist idle-timer))))
          (check "check-2/ordinary-ripe-idle-waiting" #t r)
          (check "check-2/ordinary-ripe-idle-waiting-fired-ordinary"
                 #t (truthy? (vector-ref past 0)))
          (check "check-2/ordinary-ripe-idle-waiting-not-idle"
                 #nil (vector-ref idle-timer 0)))))
    (lambda ()
      ((%sym '--rc-timer-stop-idle))
      (set-symbol-value! 'timer-event-last saved-last))))

;; both waiting, idle nearer: neither timer is ripe; the timespec_cmp
;; tie-break (idle_ripe == timer_ripe == #f) must pick the idle timer's
;; ~1s wait (sec part 0) over the ordinary timer's ~4e9s wait.
(let ((saved-last (symbol-value 'timer-event-last)))
  (dynamic-wind
    (lambda () ((%sym '--rc-timer-start-idle)))
    (lambda ()
      (let ((idle-timer (make-timer 0 1 0 0))           ; idle fires in ~1s
            (future (make-timer 0 4102444800 0 0)))     ; ordinary far future
        (let ((r (timer-check-2 (elist future) (elist idle-timer))))
          (check "check-2/tiebreak-both-waiting-near-idle" #t
                 (and (pair? r) (< (car r) 100)))
          (check "check-2/tiebreak-both-waiting-neither-fired" #t
                 (and (eq? (vector-ref future 0) #nil)
                      (eq? (vector-ref idle-timer 0) #nil))))))
    (lambda ()
      ((%sym '--rc-timer-stop-idle))
      (set-symbol-value! 'timer-event-last saved-last))))

;;; --- 5. timer-check --------------------------------------------------
;;; Reads Vtimer-list/Vtimer-idle-list via --timer-copy-window, loops
;;; timer-check-2 until it stops returning the fired marker.  Seed both
;;; globals and restore them in the unwind.
(let ((saved-timers (symbol-value 'timer-list))
      (saved-idle (symbol-value 'timer-idle-list))
      (saved-last (symbol-value 'timer-event-last))
      (timer-a (make-timer 0 0 0 0))
      (timer-b (make-timer 0 0 0 0)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'timer-list (elist timer-a timer-b))
               (set-symbol-value! 'timer-idle-list #nil))
    (lambda ()
      ;; Two ripe ordinary timers: the do-while runs both and returns the
      ;; final wait/invalid — after firing, slot0 is t on both.
      (let ((r (timer-check)))
        (check "timer-check/both-fired-marked" #t
               (and (truthy? (vector-ref timer-a 0))
                    (truthy? (vector-ref timer-b 0))))
        (check "timer-check/returns-pair-or-nil" #t
               (or (eq? r #nil) (pair? r)))))
    (lambda () (set-symbol-value! 'timer-list saved-timers)
               (set-symbol-value! 'timer-idle-list saved-idle)
               (set-symbol-value! 'timer-event-last saved-last))))

;;; --- 6. current-idle-time -------------------------------------------
;;; nil when not idle; a (HIGH LOW USEC PSEC) timestamp when idle.
(check "idle-time/not-idle-nil" #nil (current-idle-time))
(let ()
  (dynamic-wind
    (lambda () ((%sym '--rc-timer-start-idle)))
    (lambda ()
      (let ((r (current-idle-time)))
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
      (let ((r (current-idle-time)))
        (check "idle-time/ticks-hz-pair" #t (pair? r))
        (check "idle-time/ticks-hz-ratio" 1000000000 (cdr r))
        (check "idle-time/ticks-integer" #t (integer? (car r)))))
    (lambda ()
      ((%sym '--rc-timer-stop-idle))
      (set-symbol-value! 'current-time-list saved-ctl))))
