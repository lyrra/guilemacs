;;; test-m28-imp5-f4.scm --- M28 imp-5, family 4: reclaim --timer-check
;;; and the --tty- / --timer- / --read- / --reset- stay-C audit.
;;;
;;; brief.org (M28 imp-5 family 4) walks the 30 family-4 shims
;;; (--tty- 11, --timer- 8, --read- 5, --reset- 6).  Exactly one is
;;; reclaimable:
;;;
;;;   --timer-check  -> (emacs timers) timer-check
;;;
;;; Its C DEFUN was a thin double-hop: it called C timer_check (), which
;;; is itself a scm_c_public_ref + SCM_CALL_0 dispatcher into (emacs
;;; timers) timer-check.  So the live path was Scheme -> C DEFUN -> C
;;; timer_check () -> Scheme timer-check.  The reclaim removes the two
;;; middle hops: kbd-buffer.scm now imports (emacs timers) and calls the
;;; port directly, and the DEFUN is deleted.
;;;
;;; The other 29 shims read or write raw C state (a struct tty_display_info
;;; field, the TERMINAL_KEYBOARD_CODING flags, C globals like
;;; this_command_keys / read_key_sequence_cmd / timer_idleness_start_time,
;;; or C subroutines like read_key_sequence / reset_all_sys_modes), so
;;; they stay C.  Decisions and reasons: docs/kb.org "M28 imp-5 family-4
;;; --tty- / --timer- / --read- / --reset- decision audit".
;;;
;;; This corpus pins both sides of that decision:
;;;
;;;   - the deleted DEFUN reads back as nil (C subr gone);
;;;   - the (emacs timers) port the callers now use is present, is a
;;;     procedure, and returns nil with no timer active;
;;;   - (emacs kbd-buffer) loads, no longer binds the %--timer-check
;;;     alias, and routes timer-check through the (emacs timers) import;
;;;   - the 29 stay-C shims still register (symbol-function non-nil).
;;;
;;; Same harness as test-m28-imp5-f3.scm: Sourced by the .el wrapper via
;;; eval-scheme; accumulates (NAME STATUS) pairs into test-results.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))
(use-modules (emacs timers))
(use-modules (emacs kbd-buffer))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (%sym name)
  (symbol-function name))

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

;;; --- 1. The --timer-check DEFUN is gone -----------------------------
;;; A removed C DEFUN stops being registered, so symbol-function is nil
;;; (mirrors test-m28-imp5.scm §1).
(report "imp5/f4/no-defun/--timer-check"
        (if (eq? (%sym '--timer-check) #nil)
            'PASS
            (list 'FAIL 'still-bound '--timer-check)))

;;; --- 2. The port the callers now use still resolves ----------------
;;; (emacs timers) timer-check is the Scheme body the retired double-hop
;;; reached.  It must stay exported, be a procedure, and return #nil when
;;; no timer is active (its {invalid | {0,0} | wait} -> {nil | t | pair}
;;; contract; #nil is the "no active timer" case).
(report "imp5/f4/port/timer-check-present"
        (if (procedure? timer-check) 'PASS (list 'FAIL 'not-a-procedure)))
;; The port gives #nil only when timer-list and timer-idle-list are both
;; empty; a pending timer gives a (SEC . NSEC) pair.  The two lists are
;; process-global and shared with every other corpus in the suite, so this
;; check must clear them itself instead of trusting ambient state (cr.org
;; finding 2).  Save, clear, check, restore — same discipline as
;; test-m15-timers.scm.
(let ((saved-timers (symbol-value 'timer-list))
      (saved-idle (symbol-value 'timer-idle-list)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'timer-list #nil)
               (set-symbol-value! 'timer-idle-list #nil))
    (lambda ()
      (let ((r (no-error? (lambda () (timer-check)))))
        (report "imp5/f4/port/timer-check-no-error"
                (if (eq? r #t) 'PASS (list 'FAIL 'errored r)))
        (report "imp5/f4/port/timer-check-nil-contract"
                (if (eq? (timer-check) #nil)
                    'PASS
                    (list 'FAIL 'expected #nil 'got (timer-check))))))
    (lambda () (set-symbol-value! 'timer-list saved-timers)
               (set-symbol-value! 'timer-idle-list saved-idle))))

;; Positive contract under a *controlled* pending timer (finding 2's real
;; scenario): a future (year 2100) ordinary timer makes the port return a
;; (SEC . NSEC) pair instead of #nil.  This proves the corpus controls the
;; two lists rather than trusting ambient state.
(define (elist . items)
  (let loop ((i items))
    (if (null? i) #nil (cons (car i) (loop (cdr i))))))
(define (make-timer high low usec psec)
  (vector #nil high low usec #nil #nil #nil #nil psec #nil))
(let ((saved-timers (symbol-value 'timer-list))
      (saved-idle (symbol-value 'timer-idle-list))
      (future (make-timer 0 4102444800 0 0)))
  (dynamic-wind
    (lambda () (set-symbol-value! 'timer-list (elist future))
               (set-symbol-value! 'timer-idle-list #nil))
    (lambda ()
      (report "imp5/f4/port/timer-check-pending-pair"
              (let ((r (no-error? (lambda () (timer-check)))))
                (if (eq? r #t)
                    (if (pair? (timer-check))
                        'PASS
                        (list 'FAIL 'expected 'pair 'got (timer-check)))
                    (list 'FAIL 'errored r)))))
    (lambda () (set-symbol-value! 'timer-list saved-timers)
               (set-symbol-value! 'timer-idle-list saved-idle))))

;;; --- 3. (emacs kbd-buffer) routes to the (emacs timers) port --------
;;; The module must load; its %--timer-check alias must be gone (the
;;; reclaim deleted the defelisp) and the imported timer-check binding
;;; must be visible.  Report the load state explicitly so a load failure
;;; is not a silent skip.
(define kb (false-if-exception (resolve-module '(emacs kbd-buffer) #:ensure #t)))
(if kb
    (begin
      (report "imp5/f4/module/kbd-buffer/loadable" 'PASS)
      (report "imp5/f4/module/kbd-buffer/no-%--timer-check"
              (if (module-variable kb '%--timer-check)
                  (list 'FAIL 'still-bound '%--timer-check)
                  'PASS))
      (report "imp5/f4/module/kbd-buffer/imports-timer-check"
              (if (module-variable kb 'timer-check)
                  'PASS
                  (list 'FAIL 'missing 'timer-check)))
      ;; Behavioural: the DO_TIMERS_NOW arm must reach the port.  Drive
      ;; kbd-buffer-readable-events with that flag and require no error
      ;; (the port fires no timer and the ring is empty here).
      (report "imp5/f4/module/kbd-buffer/readable-do-timers-now-no-error"
              (let ((flag (@@ (emacs kbd-buffer)
                              READABLE-EVENTS-DO-TIMERS-NOW)))
                (let ((r (no-error? (lambda ()
                                      (kbd-buffer-readable-events flag)))))
                  (if (eq? r #t)
                      'PASS
                      (list 'FAIL 'errored r))))))
    (report "imp5/f4/module/kbd-buffer/loadable"
            (list 'FAIL 'not-loadable '(emacs kbd-buffer))))

;;; --- 4. All 29 stay-C shims still register --------------------------
;;; A stay-C DEFUN stays registered, so symbol-function is non-nil.
(define %stay-c
  '("--read-key-sequence"
    "--read-key-sequence-cmd"
    "--read-key-sequence-remapped"
    "--reset-redisplay-tick-state"
    "--read-char-handle-quit-preamble"
    "--timer-get-pending-funcalls-drain!"
    "--timer-pending-funcalls"
    "--timer-pending-funcalls-set!"
    "--timer-fire-ripe"
    "--timer-copy-window"
    "--timer-idleness-now"
    "--tty-keyboard-coding-requires-decoding-p"
    "--tty-keyboard-coding-raw-text-p"
    "--tty-decode-keyboard-bytes"
    "--read-key-sequence-and-vector"
    "--reset-this-command-keys"
    "--reset-kbd-ring-and-pending"
    "--timer-idleness-reset!"
    "--tty-flow-control"
    "--tty-flow-control-set!"
    "--tty-meta-key"
    "--tty-meta-key-set!"
    "--tty-bytes-readable"
    "--tty-read-nonblocking"
    "--tty-top-frame"
    "--reset-sys-modes"
    "--reset-all-sys-modes"
    "--tty-size"
    "--reset-controlling-tty-sys-modes"))

(for-each
 (lambda (name)
   (let ((sym (intern name)))
     (report (string-append "imp5/f4/stay-c/" name)
             (if (not (eq? (%sym sym) #nil))
                 'PASS
                 (list 'FAIL 'missing sym)))))
 %stay-c)
