;;; timers.scm --- M15 imp-2: Scheme timer firing core
;;;
;;; Ports the timer firing core of src/keyboard.c as four Scheme
;;; procedures, transliterated 1:1 from the C bodies (docs/m15-plan.org
;;; §"Goal"): decode-timer, timer-check-2, timer-check, and
;;; current-idle-time.  Coexistence-only: the C bodies stay active and
;;; unchanged until the imp-3 cutover (brief.org §"Coexistence only").
;;;
;;; The three-way timespec return contract crosses the FFI as
;;; {invalid | {0,0} | wait} -> {nil | t | (SEC . NSEC)}, the same
;;; encoding every M15 shim and the imp-2 body share (plan Risk 3).
;;; So timer-check-2/timer-check return #nil (no active timer), #t (a
;;; timer fired — call again), or a (SEC . NSEC) wait pair.
;;;
;;; Conventions (identical to M9-M14): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); #nil is elisp nil.  No module-level
;;; mutable state; shared state lives only in the C globals the shims
;;; touch (pending_funcalls, Vtimer-list/Vtimer-idle-list,
;;; timer_idleness_start_time, timers_run).
;;;
;;; Gap 1 (brief.org): the ordinary-timer branch reads "now" per timer
;;; via --timespec-diff-to-now, while the idle branch reads "idleness
;;; now" once via --timer-idleness-now.  The two clock reads can drift
;;; by sub-microsecond amounts the C single-snapshot code does not
;;; have; accepted per the kbd-buffer.scm:918-922 TOCTOU precedent —
;;; timer/idle resolution is not sub-microsecond-sensitive.  Decision
;;; recorded in milestone.org "M15 imp-2 done".

(define-module (emacs timers)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (decode-timer
            timer-check-2
            timer-check
            current-idle-time))

;;; --- C shim references ---------------------------------------------

(defelisp %--timer-get-pending-funcalls-drain! --timer-get-pending-funcalls-drain!)
(defelisp %--timer-copy-window            --timer-copy-window)
(defelisp %--timer-fire-ripe              --timer-fire-ripe)
(defelisp %--timespec-diff-to-now         --timespec-diff-to-now)
(defelisp %--timer-idleness-now           --timer-idleness-now)

;;; --- Timespec helpers -----------------------------------------------
;;; A timespec is a (SEC . NSEC) fixnum pair with NSEC in [0, 1e9).

(define TIMESPEC-HZ 1000000000)

(define (timespec-cmp a b)
  (let ((as (car a)) (bs (car b)))
    (cond ((< as bs) -1)
          ((> as bs) 1)
          (else (let ((an (cdr a)) (bn (cdr b)))
                  (cond ((< an bn) -1)
                        ((> an bn) 1)
                        (else 0)))))))

;; a - b, normalized.  Only used with a >= b in the idle branch.
(define (timespec-sub a b)
  (let ((s (- (car a) (car b)))
        (n (- (cdr a) (cdr b))))
    (if (< n 0)
        (cons (- s 1) (+ n TIMESPEC-HZ))
        (cons s n))))

;; Negate a (possibly negative, normalized) timespec: used to turn the
;; negative wait --timespec-diff-to-now reports for a future ordinary
;; timer into the positive wait value C returns.
(define (timespec-negate ts)
  (let ((s (car ts)) (n (cdr ts)))
    (if (= n 0)
        (cons (- s) 0)
        (cons (- (- s) 1) (- TIMESPEC-HZ n)))))

;;; --- decode-timer ---------------------------------------------------
;;; C: slot checks (10-slot vector, slot 0 nil, slot 2 fixnum), then
;;; list4_to_timespec (slot1 slot2 slot3 slot8) into a timespec pair.
;;; Returns #nil (invalid) or (SEC . NSEC).  Timer vectors store
;;; non-negative usec/psec in [0, 1e6), so the decode is exact.

(define (decode-timer timer)
  (if (or (not (vector? timer))
          (not (= (vector-length timer) 10)))
      #nil
      (let ((slot0 (vector-ref timer 0)))
        (if (not (eq? slot0 #nil))
            #nil
            ;; C's decode_timer + decode_time_components (timefns.c)
            ;; require slot1 (high), slot2 (low), slot3 (usec) and
            ;; slot8 (psec) all be FIXNUMP and return invalid otherwise.
            ;; Guarding all four also stops a type error in the
            ;; arithmetic below, the way C cleanly returns invalid for a
            ;; malformed vector (cr.org Finding 3).  Scheme integers do
            ;; not distinguish fixnum from bignum, but every real
            ;; timer.el slot is a small int, so `integer?' is the exact
            ;; port.
            (let ((high (vector-ref timer 1))
                  (slot2 (vector-ref timer 2))
                  (usec (vector-ref timer 3))
                  (psec (vector-ref timer 8)))
              (if (not (and (integer? high) (integer? slot2)
                            (integer? usec) (integer? psec)))
                  #nil
                  (let* (;; list4_to_timespec: sec = high*2^16 + low +
                         ;; usec's full-milliseconds carry; nsec =
                         ;; (usec mod 1e6)*1000 + psec/1000.
                         (sec (+ (* high 65536) slot2))
                         (nsec (+ (* usec 1000) (quotient psec 1000))))
                    (cons (+ sec (quotient nsec TIMESPEC-HZ))
                          (modulo nsec TIMESPEC-HZ)))))))))

;;; --- timer-check-2 --------------------------------------------------
;;; C body (keyboard.c:5785-5923), 1:1: drain pending_funcalls, reject
;;; when no list, snapshot idleness now, walk both lists skipping
;;; invalid timers, choose the next timer verbatim, then fire it
;;; (returning #t) or return the wait pair.

(define (timer-check-2 timers idle-timers)
  ;; First run the code that was delayed (C 5788-5793).
  ((force %--timer-get-pending-funcalls-drain!))

  ;; C 5798-5802: snapshot now / idleness_now once.  --timespec-diff-to-now
  ;; supplies the per-timer ordinary "now"; --timer-idleness-now supplies
  ;; idleness once (nil -> {0,0} when not idle, matching C 5800-5802).
  (let ((idleness-now (let ((r ((force %--timer-idleness-now))))
                        (if (eq? r #nil) (cons 0 0) r))))
    (let loop ((timers timers) (idle-timers idle-timers))
      (cond
        ;; No ordinary and no idle timer -> invalid (C 5795-5796, and the
        ;; do-while exit at 5919-5922 after advancing past all heads).
        ((and (eq? timers #nil) (eq? idle-timers #nil)) #nil)
        ;; Skip past an invalid ordinary timer, advance and retry (C 5820-5825).
        ((and (pair? timers) (eq? (decode-timer (car timers)) #nil))
         (loop (cdr timers) idle-timers))
        ;; Likewise for an invalid idle timer (C 5838-5843).
        ((and (pair? idle-timers) (eq? (decode-timer (car idle-timers)) #nil))
         (loop timers (cdr idle-timers)))
        (else
         (let ((timer-diff #nil) (idle-diff #nil)
               (timer-ripe #f) (idle-ripe #f))
           ;; Ordinary head (C 5817-5831).
           (when (pair? timers)
             (let* ((diff ((force %--timespec-diff-to-now) (car timers)))
                    (ripe (>= (car diff) 0)))
               (set! timer-ripe ripe)
               (set! timer-diff (if ripe diff (timespec-negate diff)))))
           ;; Idle head (C 5835-5850).
           (when (pair? idle-timers)
             (let* ((tt (decode-timer (car idle-timers)))
                    (ripe (<= (timespec-cmp tt idleness-now) 0)))
               (set! idle-ripe ripe)
               (set! idle-diff (if ripe
                                   (timespec-sub idleness-now tt)
                                   (timespec-sub tt idleness-now)))))
           ;; Choose the next timer (C 5856-5878), verbatim: ordinary wins
           ;; unless the idle timer is strictly earlier.
           (if (and (pair? timer-diff)
                    (or (eq? idle-diff #nil)
                        (and (not idle-ripe) timer-ripe)
                        (and (eq? idle-ripe timer-ripe)
                             (if timer-ripe
                                 (< (timespec-cmp idle-diff timer-diff) 0)
                                 (< (timespec-cmp timer-diff idle-diff) 0)))))
               ;; Ordinary timer chosen.
               (let ((chosen (car timers)) (diff timer-diff) (ripe timer-ripe))
                 (if ripe
                     (begin ((force %--timer-fire-ripe) chosen) #t)
                     diff))
               ;; Idle timer chosen.
               (let ((chosen (car idle-timers)) (diff idle-diff) (ripe idle-ripe))
                 (if ripe
                     (begin ((force %--timer-fire-ripe) chosen) #t)
                     diff)))))))))

;;; --- timer-check ----------------------------------------------------
;;; C body (keyboard.c:5936-5969): copy both lists atomically via the
;;; --timer-copy-window shim (atimers-off + input-blocked + inhibit-quit
;;; window, plan Risk 1), then loop timer-check-2 until it stops
;;; returning the {0,0} "fired, call again" marker.

(define (timer-check)
  (let* ((window ((force %--timer-copy-window)))
         (timers (car window))
         (idle-timers (cdr window)))
    (let loop ((result (timer-check-2 timers idle-timers)))
      (if (eq? result #t)
          (loop (timer-check-2 timers idle-timers))
          result))))

;;; --- current-idle-time ----------------------------------------------
;;; C DEFUN body (keyboard.c:5971-5987): return the elapsed idle
;;; duration as a Lisp timestamp when idle, else nil.  Shares the
;;; --timer-idleness-now clock read with timer-check-2's idle branch.

(define (current-idle-time)
  (let ((idle ((force %--timer-idleness-now))))
    (if (eq? idle #nil)
        #nil
        ;; make_lisp_time (timefns.c) branches on current-time-list:
        ;; t (default) -> (HIGH LOW USEC PSEC); nil -> (TICKS . HZ)
        ;; (timespec_to_lisp).  cr.org Finding 1.
        (if (not (eq? (symbol-value 'current-time-list) #nil))
            ;; make_lisp_time list branch: (HIGH LOW USEC PSEC) =
            ;; (hi_time(s) lo_time(s) ns/1000 (ns%1000)*1000), with
            ;; s = tv_sec, ns = tv_nsec.
            (let ((s (car idle))
                  (ns (cdr idle)))
              (elist (quotient s 65536)
                     (logand s 65535)
                     (quotient ns 1000)
                     (* (modulo ns 1000) 1000)))
            ;; timespec_to_lisp: ticks = sec*1e9 + nsec, hz = 1e9.
            (cons (+ (* (car idle) TIMESPEC-HZ) (cdr idle))
                  TIMESPEC-HZ)))))

;;; --- small list helper ----------------------------------------------
;;; Build an elisp list (proper list terminated by #nil) from the items.
(define (elist . items)
  (let loop ((i items))
    (if (null? i) #nil (cons (car i) (loop (cdr i))))))
