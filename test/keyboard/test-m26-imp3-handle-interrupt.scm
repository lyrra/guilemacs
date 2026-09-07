;;; test-m26-imp3-handle-interrupt.scm --- M26 imp-3 (emacs interrupt) corpus.
;;;
;;; Covers the M26 imp-3 cutover (brief.org M26): the in_signal_handler ==
;;; false (arm 2 + tail) body of C handle_interrupt (src/keyboard.c) moved
;;; out of C into (emacs interrupt) as `handle-interrupt'.  C handle_interrupt
;;; is now a three-way dispatcher: arm 1 (the emergency-escape prompt) stays
;;; C and is extracted into handle_interrupt_emergency_escape; arm 2 + tail
;;; stay a straight-line C copy for the real SIGINT path (in_signal_handler
;;; == true); arm 2 + tail on the normal path forward to this Scheme function.
;;; Four new C shims support the port: --echoing-p (the getter for the echoing
;;; flag), --force-quit-count / --set-force-quit-count! (the force_quit_count
;;; global), and --restore-signal-mask (pthread_sigmask SIG_SETMASK).
;;;
;;; The Scheme body is fully testable in-process.  The quit path ends in
;;; quit-throw-to-read-char -> abort-to-prompt, and Guile's call-with-prompt
;;; catches that abort without touching a real terminal (same technique as
;;; imp-2).  The non-quit path returns nil and is tested directly.
;;;
;;; handle-interrupt calls every shim through (%c '--name) on each call (not a
;;; defelisp delay), so the test fset-stubs each C shim for the duration of a
;;; call (with-stubs!, dynamic-wind-protected).  The plain elisp variables
;;; (quit-flag, inhibit-quit) are saved/restored the same way.
;;;
;;; Sourced by test/keyboard/test-m26-imp3-handle-interrupt.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from elisp.
;;; See brief.org M26 imp-3.

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

;; Stub one or more (SYM . PROC) function cells for the duration of THUNK,
;; restoring the original function cell afterwards.  Later entries in
;; STUB-ALIST win over earlier ones (they are applied in order).
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

;; Run THUNK (which must end by aborting to getctag) with getctag bound to a
;; fresh prompt tag this corpus owns, and catch that abort.  Returns 'aborted
;; if THUNK reached the abort, 'no-abort otherwise.  Restores getctag.
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

;;; --- Spy counters (handle-interrupt shims) ---------------------------
(define call-fqc 0)           ; --force-quit-count call count
(define call-set-fqc '())     ; --set-force-quit-count! args (last call first)
(define call-restore 0)       ; --restore-signal-mask call count
(define call-waiting #nil)    ; --waiting-for-input-p return value
(define call-echoing #nil)    ; --echoing-p return value
(define (reset-spies!)
  (set! call-fqc 0)
  (set! call-set-fqc '())
  (set! call-restore 0)
  (set! call-waiting #nil)
  (set! call-echoing #nil))

;; Standard shim set for handle-interrupt: every handle-interrupt shim is
;; fset-stubbed.  Waiting/echoing default to nil/nil so the tail condition
;; (waiting && !echoing) is false and the body returns nil (no abort).  EXTRA
;; entries override defaults (appended last).
(define (standard-stubs . extra)
  (append (list (cons '--force-quit-count
                      (lambda () (set! call-fqc (1+ call-fqc)) 2))
                (cons '--set-force-quit-count!
                      (lambda (v) (set! call-set-fqc (cons v call-set-fqc)) v))
                (cons '--restore-signal-mask
                      (lambda () (set! call-restore (1+ call-restore)) #nil))
                (cons '--waiting-for-input-p
                      (lambda () call-waiting))
                (cons '--echoing-p
                      (lambda () call-echoing)))
          extra))

;; Run handle-interrupt with QUIT-FLAG-VAL set under STUBS, plus the quit
;; path's extra shims so a real abort is safe.  Returns the body result.
;; Saves/restores quit-flag and inhibit-quit.
(define (run-hi! stubs quit-flag-val)
  (let ((old-qf (get-var 'quit-flag))
        (old-iq (get-var 'inhibit-quit)))
    (dynamic-wind
      (lambda ()
        (reset-spies!)
        (set-symbol-value! 'quit-flag quit-flag-val))
      (lambda ()
        (with-stubs! stubs
          (lambda () (handle-interrupt))))
      (lambda ()
        (restore-var! 'quit-flag old-qf)
        (restore-var! 'inhibit-quit old-iq)))))

;; The shims quit-throw-to-read-char touches when it actually runs (the tail
;; quit path).  Mirrors imp-2's standard-stubs.
(define quit-path-stubs
  (list (cons '--clear-waiting-for-input (lambda () #nil))
        (cons '--clear-input-available-clear-time! (lambda () #nil))
        (cons '--input-pending-set! (lambda (v) #nil))
        (cons '--switch-to-frame! (lambda (f) #nil))
        (cons '--get-internal-last-event-frame (lambda () #nil))))

;;; --- 1. Cutover wiring: module exports handle-interrupt --------------
(check "handle-interrupt/exported" #t
       (procedure? (module-ref (resolve-interface '(emacs interrupt))
                               'handle-interrupt)))

;;; --- 2. Arm 2 bump: quit-flag nil -> count 1 -------------------------
;; quit-flag nil -> count is 1 WITHOUT reading --force-quit-count.
(run-hi! (standard-stubs) #nil)
(check "handle-interrupt/nil-quit-count-is-1" '(1) call-set-fqc)
(check "handle-interrupt/nil-quit-skips-force-quit-count" 0 call-fqc)

;;; --- 3. Arm 2 bump: quit-flag set -> count N+1 via --force-quit-count ----
;; quit-flag non-nil -> reads --force-quit-count (stub returns 2), writes 3.
(run-hi! (standard-stubs) 'some-quit)
(check "handle-interrupt/set-quit-reads-force-quit-count" 1 call-fqc)
(check "handle-interrupt/set-quit-count-is-n-plus-1" '(3) call-set-fqc)

;;; --- 4. inhibit-quit cleared only when count reaches 3 ---------------
;; count 2 (stub --force-quit-count returns 1) with inhibit-quit set: NOT
;; cleared.  count 3 (stub returns 2): cleared to nil.
(define (run-with-inhibit! fqc-val iq-val)
  (let ((old-qf (get-var 'quit-flag))
        (old-iq (get-var 'inhibit-quit)))
    (dynamic-wind
      (lambda () (set-symbol-value! 'quit-flag 'some-quit))
      (lambda ()
        ;; Stub the FULL handle-interrupt shim set (standard-stubs) so no real
        ;; C shim runs and no process state is mutated; override --force-quit-count
        ;; to return FQC-VAL.  Also stub the tail shims so waiting/echoing cannot
        ;; abort out of the test (see the quit-path-aborts case).
        (with-stubs! (append (standard-stubs (cons '--force-quit-count
                                                   (lambda () fqc-val)))
                             quit-path-stubs)
                     (lambda ()
                       (set-symbol-value! 'inhibit-quit iq-val)
                       (handle-interrupt)
                       (check (format #f "handle-interrupt/inhibit-clear-count-~a" (1+ fqc-val))
                              (if (= (1+ fqc-val) 3) #nil 'still-set)
                              (symbol-value 'inhibit-quit)))))
      (lambda ()
        (restore-var! 'quit-flag old-qf)
        (restore-var! 'inhibit-quit old-iq)))))

(run-with-inhibit! 1 'still-set)    ; count 2, keep inhibit-quit
(run-with-inhibit! 2 'still-set)    ; count 3, clear inhibit-quit

;;; --- 5. quit-flag always set to t ------------------------------------
;; Observed DURING the run (run-hi! restores quit-flag when it returns).
(check "handle-interrupt/quit-flag-set-to-t" #t
       (let ((old-qf (get-var 'quit-flag)))
         (dynamic-wind
           (lambda ()
             (reset-spies!)
             (set-symbol-value! 'quit-flag #nil))
           (lambda ()
             (with-stubs! (standard-stubs)
               (lambda ()
                 (handle-interrupt)
                 (eq? (symbol-value 'quit-flag) #t))))
           (lambda () (restore-var! 'quit-flag old-qf)))))

;;; --- 6. tail: --restore-signal-mask always called --------------------
(run-hi! (standard-stubs) #nil)
(check "handle-interrupt/restore-signal-mask-once" 1 call-restore)

;;; --- 7. tail quit path: waiting && !echoing -> abort -----------------
;; waiting-for-input t, echoing nil -> the tail calls quit-throw-to-read-char,
;; which ends in abort-to-prompt (caught here).  Body never returns normally.
(check "handle-interrupt/quit-path-aborts" 'aborted
       (let ((old-qf (get-var 'quit-flag)))
         (dynamic-wind
           (lambda ()
             (reset-spies!)
             (set! call-waiting #t)
             (set! call-echoing #nil)
             (set-symbol-value! 'quit-flag #nil))
           (lambda ()
             (with-stubs! (append (standard-stubs) quit-path-stubs)
               (lambda ()
                 (with-abort-caught (lambda () (handle-interrupt))))))
           (lambda () (restore-var! 'quit-flag old-qf)))))

;;; --- 8. tail non-quit path: echoing true -> no abort, returns nil -----
(check "handle-interrupt/echoing-skips-quit" #nil
       (let ((old-qf (get-var 'quit-flag)))
         (dynamic-wind
           (lambda ()
             (reset-spies!)
             (set! call-waiting #t)
             (set! call-echoing #t)
             (set-symbol-value! 'quit-flag #nil))
           (lambda ()
             (with-stubs! (standard-stubs)
               (lambda () (handle-interrupt))))
           (lambda () (restore-var! 'quit-flag old-qf)))))

;;; --- 9. Real C shims (not fset-stubbed) ------------------------------
;;; cr.org Finding 1: the fset-stub cases above never run the real C DEFUNs.
;;; These cases call --force-quit-count / --set-force-quit-count! /
;;; --echoing-p / --set-echoing! / --restore-signal-mask for real and check
;;; the round-trip against the actual C state.  No handle_interrupt here, so
;;; no cancel_echoing / arm-1 / tail side effects.  State is saved/restored.

;; --force-quit-count / --set-force-quit-count! round-trip.
(check "handle-interrupt/real-force-quit-count-fixnum" #t
       (let ((old ((%c '--force-quit-count))))
         (dynamic-wind
           (lambda () #t)
           (lambda ()
             (let ((probe ((%c '--set-force-quit-count!) 7)))
               (and (eq? probe 7)
                    (eq? ((%c '--force-quit-count)) 7))))
           (lambda () ((%c '--set-force-quit-count!) old)))))

;; --echoing-p / --set-echoing! round-trip.
(check "handle-interrupt/real-echoing-round-trip" #t
       (let ((old ((%c '--echoing-p))))
         (dynamic-wind
           (lambda () #t)
           (lambda ()
             (and (begin ((%c '--set-echoing!) #t) (eq? ((%c '--echoing-p)) #t))
                  (begin ((%c '--set-echoing!) #nil) (eq? ((%c '--echoing-p)) #nil))))
           (lambda () ((%c '--set-echoing!) old)))))

;; --restore-signal-mask is callable and returns nil.
(check "handle-interrupt/real-restore-signal-mask" #nil
       ((%c '--restore-signal-mask)))

;;; --- 10. Real dispatch: --handle-interrupt-normal -> Scheme -----------
;;; cr.org Finding 1: no case runs the live dispatch chain.  The real C
;;; --handle-interrupt-normal DEFUN calls handle_interrupt (false), which
;;; forwards arm 2 + tail to (emacs interrupt) handle-interrupt via
;;; scm_c_public_ref.  With quit-flag nil the arm-1 emergency-escape test
;;; cannot fire even on a tty; pinning echoing true keeps the Scheme tail
;;; (waiting_for_input && !echoing) from aborting, so the call returns nil.
;;; quit-flag nil forces count = 1 deterministically, which proves the real
;;; C -> Scheme wiring bumped the real force_quit_count and set quit-flag.
(check "handle-interrupt/real-dispatch-arm2-bumps-count" #t
       (let ((old-fqc ((%c '--force-quit-count)))
             (old-echo ((%c '--echoing-p)))
             (old-qf (get-var 'quit-flag)))
         (dynamic-wind
           (lambda ()
             ((%c '--set-echoing!) #t)
             (set-symbol-value! 'quit-flag #nil))
           (lambda ()
             ;; Real dispatch: must return nil (no abort-to-prompt).
             (and (eq? ((%c '--handle-interrupt-normal)) #nil)
                  (eq? ((%c '--force-quit-count)) 1)
                  (eq? (symbol-value 'quit-flag) #t)))
           (lambda ()
             ((%c '--set-force-quit-count!) old-fqc)
             ((%c '--set-echoing!) old-echo)
             (restore-var! 'quit-flag old-qf)))))
