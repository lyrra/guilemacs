;;; test-m26-imp2-quit-throw.scm --- M26 imp-2 (emacs interrupt) corpus.
;;;
;;; Covers the M26 imp-2 cutover (brief.org M26): the from_signal == false
;;; body of C quit_throw_to_read_char (src/keyboard.c) moved out of C into
;;; (emacs interrupt) as `quit-throw-to-read-char'.  The C function is now
;;; a two-branch dispatcher: from_signal == true keeps a straight-line C
;;; body (the SIGINT path), from_signal == false forwards to the Scheme
;;; function.  Two new C shims support the port:
;;; --clear-input-available-clear-time! (the other half of
;;; clear_waiting_for_input) and --switch-to-frame! (wraps
;;; do_switch_frame + make_lispy_switch_frame).
;;;
;;; Unlike suspend-emacs (imp-1), this function's full body is testable
;;; end-to-end in-process: it ends in abort-to-prompt, and Guile's
;;; call-with-prompt catches that abort without touching a real terminal
;;; or process.  The test binds getctag (via the M12 --set-ctag shim) to a
;;; fresh prompt tag, calls quit-throw-to-read-char under call-with-prompt,
;;; and observes which shims fired before the abort.
;;;
;;; quit-throw-to-read-char calls every shim through (%c '--name) on each
;;; call (not a defelisp delay), so the test fset-stubs each C shim by
;;; replacing its symbol's function cell for the duration of a call and
;;; restoring after (with-stubs!, dynamic-wind-protected).  The plain elisp
;;; variables (quit-flag, unread-command-events) are saved/restored the same
;;; way.  Nothing leaks into later corpora.
;;;
;;; NOTE: the batch harness has a single frame, so the real
;;; internal-last-event-frame always equals (selected-frame) and the frame
;;; switch would never fire against real shims.  The switch decision is
;;; exercised by stubbing --get-internal-last-event-frame / framep /
;;; selected-frame with sentinels (test-kbd-dispatch.scm documents the same
;;; batch limitation).  This still exercises the ported FRAMEP + EQ guard
;;; logic; the real do_switch_frame path is covered by the interactive
;;; smoke path (unchanged C callers), not by this corpus.
;;;
;;; Sourced by test/keyboard/test-m26-imp2-quit-throw.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See brief.org M26 imp-2.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))
(use-modules (emacs interrupt))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

;;; --- Local helpers ---------------------------------------------------

(define (%c name) (symbol-function name))

;; Stub one or more (SYM . PROC) function cells for the duration of
;; THUNK, restoring the original function cell afterwards.  Later entries
;; in STUB-ALIST win over earlier ones (they are applied in order).
(define (with-stubs! stub-alist thunk)
  (let ((saved (map (lambda (p) (cons (car p) (symbol-function (car p))))
                    stub-alist)))
    (dynamic-wind
      (lambda ()
        (for-each (lambda (p) (set-symbol-function! (car p) (cdr p)))
                  stub-alist))
      thunk
      (lambda ()
        (for-each (lambda (p) (set-symbol-function! (car p) (cdr p)))
                  saved)))))

;; Capture and restore a Lisp variable's value (tolerating unbound).
(define *unbound-sentinel* (list 'unbound))
(define (get-var sym)
  (if ((%c 'boundp) sym) (symbol-value sym) *unbound-sentinel*))
(define (restore-var! sym saved)
  (if (eq? saved *unbound-sentinel*)
      ((%c 'makunbound) sym)
      (set-symbol-value! sym saved)))

;; Run THUNK (which must end by aborting to getctag) with getctag bound to
;; a fresh prompt tag this corpus owns, and catch that abort.  Returns
;; 'aborted if THUNK reached the abort, 'no-abort otherwise.  Restores the
;; caller's getctag afterwards.
(define (with-abort-caught thunk)
  (let* ((tag (make-prompt-tag))
         (old-tag ((%c '--get-ctag))))
    (dynamic-wind
      (lambda () ((%c '--set-ctag) tag))
      (lambda ()
        (call-with-prompt tag
          (lambda () (thunk) 'no-abort)
          (lambda (k . _) 'aborted)))
      (lambda () ((%c '--set-ctag) old-tag)))))

;;; Spy counters -- reset before every scenario, observed after.
(define call-clear 0)         ; --clear-waiting-for-input call count
(define call-clear-time 0)    ; --clear-input-available-clear-time! count
(define call-input-pending '()) ; --input-pending-set! args (last call first)
(define call-switch '())      ; --switch-to-frame! args (last call first)
(define call-kill 0)          ; kill-emacs call count
(define (reset-spies!)
  (set! call-clear 0)
  (set! call-clear-time 0)
  (set! call-input-pending '())
  (set! call-switch '())
  (set! call-kill 0))

;; Standard shim set for a full quit-throw run.  Every shim is fset-stubbed
;; to a spy (or safe no-op); --get-internal-last-event-frame defaults to
;; #nil so the frame-switch guard is false.  EXTRA entries override the
;; defaults (appended last).  A quit-throw call never reaches a real
;; terminal-touching shim here.
(define (standard-stubs . extra)
  (append (list (cons '--clear-waiting-for-input
                      (lambda () (set! call-clear (1+ call-clear)) #nil))
                (cons '--clear-input-available-clear-time!
                      (lambda () (set! call-clear-time (1+ call-clear-time)) #nil))
                (cons '--input-pending-set!
                      (lambda (v) (set! call-input-pending (cons v call-input-pending)) #nil))
                (cons '--switch-to-frame!
                      (lambda (f) (set! call-switch (cons f call-switch)) #nil))
                (cons 'kill-emacs
                      (lambda (a b) (set! call-kill (1+ call-kill)) #nil))
                (cons '--get-internal-last-event-frame (lambda () #nil)))
          extra))

;; Run quit-throw-to-read-char end-to-end with QUIT-FLAG-VAL set, under
;; STUBS, catching the abort.  Returns the abort result.  Saves/restores
;; quit-flag and unread-command-events so nothing leaks to later corpora.
(define (run-quit! stubs quit-flag-val)
  (let ((old-qf (get-var 'quit-flag))
        (old-uce (get-var 'unread-command-events)))
    (dynamic-wind
      (lambda ()
        (reset-spies!)
        (set-symbol-value! 'quit-flag quit-flag-val))
      (lambda ()
        (with-stubs! stubs
          (lambda () (with-abort-caught (lambda () (quit-throw-to-read-char))))))
      (lambda ()
        (restore-var! 'quit-flag old-qf)
        (restore-var! 'unread-command-events old-uce)))))

;;; --- 1. Cutover wiring: module exports quit-throw-to-read-char --------
;; The C dispatcher (quit_throw_to_read_char, from_signal == false) does
;; scm_c_public_ref ("emacs interrupt", "quit-throw-to-read-char"); verify
;; the module exports it as a procedure.
(check "quit-throw/exported" #t
       (procedure? (module-ref (resolve-interface '(emacs interrupt))
                               'quit-throw-to-read-char)))

;;; --- 2. kill-emacs sentinel vs other non-nil quit-flag ----------------
;; quit-flag == kill-emacs (the batch-EOF sentinel) -> the kill-emacs shim
;; is called (stubbed, not the real one).  Any other non-nil quit value ->
;; kill-emacs is NOT called.
(run-quit! (standard-stubs) 'kill-emacs)
(check "quit-throw/kill-emacs-sentinel-calls-kill-emacs" 1 call-kill)

(run-quit! (standard-stubs) 'some-other-quit)
(check "quit-throw/non-kill-quit-flag-skips-kill-emacs" 0 call-kill)

;;; --- 3. Both clear-waiting-for-input halves called once each ----------
;; The Scheme body reproduces clear_waiting_for_input()'s full effect by
;; calling --clear-waiting-for-input AND --clear-input-available-clear-time!
;; exactly once each, per invocation.
(run-quit! (standard-stubs) #nil)
(check "quit-throw/clear-waiting-for-input-once" 1 call-clear)
(check "quit-throw/clear-input-available-clear-time-once" 1 call-clear-time)

;;; --- 4. --input-pending-set! called with nil --------------------------
(run-quit! (standard-stubs) #nil)
(check "quit-throw/input-pending-set-nil" #t
       (and (= 1 (length call-input-pending))
            (eq? (car call-input-pending) #nil)))

;;; --- 5. unread-command-events reset to nil ----------------------------
;; Set unread-command-events to a non-nil list first; a quit-throw run must
;; reset it to nil.  Observed before the variable is restored.
(let ((old-uce (get-var 'unread-command-events))
      (old-qf (get-var 'quit-flag)))
  (dynamic-wind
    (lambda ()
      (reset-spies!)
      (set-symbol-value! 'unread-command-events '(a b c))
      (set-symbol-value! 'quit-flag #nil))
    (lambda ()
      (with-stubs! (standard-stubs)
        (lambda ()
          (with-abort-caught (lambda () (quit-throw-to-read-char)))
          (check "quit-throw/unread-command-events-cleared" #nil
                 (symbol-value 'unread-command-events)))))
    (lambda ()
      (restore-var! 'unread-command-events old-uce)
      (restore-var! 'quit-flag old-qf))))

;;; --- 6. Frame-switch guard (FRAMEP arm + EQ arm) ----------------------
;; The guard is: (and (not nil? (framep frame))
;;                    (not (eq? frame (selected-frame))))  -> --switch-to-frame!
;; frame comes from --get-internal-last-event-frame.  With a sentinel frame
;; and stubbed framep/selected-frame we exercise both arms deterministically.
;; (a) frame differs from selected-frame -> switch fires with that frame.
(run-quit! (standard-stubs (cons '--get-internal-last-event-frame
                                 (lambda () 'sframe))
                           (cons 'framep (lambda (f) #t))
                           (cons 'selected-frame (lambda () #nil)))
           #nil)
(check "quit-throw/frame-switch-fires-on-different-frame" '(sframe) call-switch)

;; (b) frame EQUALS selected-frame -> EQ arm false -> no switch.
(run-quit! (standard-stubs (cons '--get-internal-last-event-frame
                                 (lambda () 'sframe))
                           (cons 'framep (lambda (f) #t))
                           (cons 'selected-frame (lambda () 'sframe)))
           #nil)
(check "quit-throw/frame-switch-skipped-when-eq" '() call-switch)

;; (c) frame is nil -> FRAMEP arm false -> no switch (also the default
;;     --get-internal-last-event-frame stub used in every other run).
(run-quit! (standard-stubs) #nil)
(check "quit-throw/frame-switch-skipped-when-nil" '() call-switch)

;;; --- 7. Full-body round-trip reaches abort-to-prompt ------------------
;; With every shim stubbed, a full quit-throw run must run to completion and
;; end by aborting to the bound prompt tag ('aborted), never returning.
(check "quit-throw/full-body-aborts-to-prompt" 'aborted
       (run-quit! (standard-stubs) #nil))

;;; --- 8. C DEFUN forwards into the Scheme body -------------------------
;; The C-exposed --quit-throw-to-read-char calls quit_throw_to_read_char(0),
;; which must dispatch to the Scheme quit-throw-to-read-char and end in
;; abort-to-prompt.  We catch that abort in-process: reaching it proves the
;; C cutover forwards (mirrors imp-1's c-defun-forwards check).  To keep the
;; real shims inert we clear internal-last-event-frame first (single-frame
;; batch would otherwise compare it to selected-frame).
(let ((old-ilef ((%c '--get-internal-last-event-frame))))
  (dynamic-wind
    (lambda () ((%c '--set-internal-last-event-frame) #nil))
    (lambda ()
      (check "quit-throw/c-defun-forwards-aborts" 'aborted
             (with-abort-caught (lambda () ((%c '--quit-throw-to-read-char))))))
    (lambda () ((%c '--set-internal-last-event-frame) old-ilef))))
