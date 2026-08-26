;;; test-m18-echo.scm --- M18 imp-3 cutover test corpus.
;;;
;;; Verifies the C static echo functions in src/keyboard.c now dispatch
;;; into the Scheme bodies in (emacs echo).  Each C static was replaced
;;; by a cached SCM proc + SCM_CALL_* into scm_c_public_ref("emacs
;;; echo", ...).  The only public entry points for these C statics from
;;; elisp are the 6 imp-1 shim DEFUNs (--echo-now, --echo-length,
;;; --echo-truncate, --echo-dash, --echo-keystrokes-p, --echo-update)
;;; and the kboard field accessors (current-kboard, kboard-echo-string,
;;; set-kboard-echo-string, --set-current-kboard-immediate-echo,
;;; --current-kboard-immediate-echo-p).
;;;
;;; So this corpus drives each shim and checks the observable kboard
;;; state changed the way the (emacs echo) body specifies.  That proves
;;; the C body no longer holds its own logic: a bug in the cutover
;;; (wrong module name, wrong proc name, wrong arity) would surface as a
;;; wrong result or a signal here, even though test-m18-bodies already
;;; covers the Scheme bodies in isolation.
;;;
;;; Sourced by test/keyboard/test-m18-echo.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See docs/m18-plan.org §imp-3 and brief.org.

(use-modules (emacs echo))
(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

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

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

;;; --- Echo-state access helpers --------------------------------------
(define (kb)         ((%sym 'current-kboard)))
(define (ges)        ((%sym 'kboard-echo-string) (kb)))
(define (ses v)      ((%sym 'set-kboard-echo-string) (kb) v))
(define (gprompt)    ((%sym 'kboard-echo-prompt) (kb)))
(define (sprompt v)  ((%sym 'set-kboard-echo-prompt) (kb) v))
(define (set-imm v)  ((%sym '--set-current-kboard-immediate-echo) v))
(define (imm-p)      ((%sym '--current-kboard-immediate-echo-p)))
(define (reset-keys!) ((%sym '--reset-this-command-keys)))
(define (add-key! k)  ((%sym '--add-command-key) k))

(define (with-echo-state thunk)
  (let ((saved-es  (ges))
        (saved-ep  (gprompt))
        (saved-imm (imm-p))
        (saved-ek  (symbol-value 'echo-keystrokes))
        (saved-ekh (symbol-value 'echo-keystrokes-help))
        (saved-ekp (symbol-function 'internal-echo-keystrokes-prefix))
        (saved-hah (symbol-function 'help--append-keystrokes-help)))
    (dynamic-wind
      (lambda ()
        (ses #nil) (sprompt #nil) (set-imm #nil) (reset-keys!)
        (set-symbol-value! 'echo-keystrokes 0)
        (set-symbol-value! 'echo-keystrokes-help #nil)
        (set-symbol-function! 'internal-echo-keystrokes-prefix
                              (lambda () #nil))
        (set-symbol-function! 'help--append-keystrokes-help
                              (lambda (s) (string-append s "!"))))
      thunk
      (lambda ()
        (ses saved-es) (sprompt saved-ep) (set-imm saved-imm)
        (set-symbol-value! 'echo-keystrokes saved-ek)
        (set-symbol-value! 'echo-keystrokes-help saved-ekh)
        (set-symbol-function! 'internal-echo-keystrokes-prefix saved-ekp)
        (set-symbol-function! 'help--append-keystrokes-help saved-hah)))))

;;; --- 1. --echo-keystrokes-p (echo_keystrokes_p) ----------------------
(with-echo-state
 (lambda ()
   (set-symbol-value! 'echo-keystrokes 1)
   (check "cut/ek-fixnum1" #t (truthy? ((%sym '--echo-keystrokes-p))))
   (set-symbol-value! 'echo-keystrokes 0)
   (check "cut/ek-zero" #f (truthy? ((%sym '--echo-keystrokes-p))))
   (set-symbol-value! 'echo-keystrokes 0.5)
   (check "cut/ek-float-positive" #t (truthy? ((%sym '--echo-keystrokes-p))))))

;;; --- 2. --echo-add-key (echo_add_key) --------------------------------
;;; No public shim for echo_add_key exists, so it is reached only
;;; transitively through --echo-update (echo_update calls echo-add-key).
;;; Exercise it through --echo-update below.

;;; --- 3. --echo-dash (echo_dash) --------------------------------------
(with-echo-state
 (lambda ()
   ;; guard: nil echo-string -> unchanged.
   (ses #nil)
   ((%sym '--echo-dash))
   (check "cut/dash-guard-nil" #nil (ges))
   ;; success path: appends `-'.
   (set-imm #t)
   (ses "abc")
   ((%sym '--echo-dash))
   (check "cut/dash-success" "abc-" (ges))))

;;; --- 4. --echo-update (echo_update -> echo-add-key) -------------------
(with-echo-state
 (lambda ()
   (set-imm #t)
   (reset-keys!) (add-key! 97) (add-key! 98)
   (sprompt "P>")
   ((%sym '--echo-update))
   (check "cut/update-prompt-and-keys" "P> a b" (ges))))

;;; --- 5. --echo-now (echo_now) ----------------------------------------
(with-echo-state
 (lambda ()
   (set-imm #nil)
   (ses "hello")
   ((%sym '--echo-now))
   ;; echo_now flips immediate-echo to true.
   (check "cut/now-immediate-echo" #t (imm-p))))

;;; --- 6. --echo-length (echo_length) ----------------------------------
(with-echo-state
 (lambda ()
   (ses "hello")
   (check "cut/length-string" 5 ((%sym '--echo-length)))
   (ses #nil)
   (check "cut/length-nil" 0 ((%sym '--echo-length)))))

;;; --- 7. --echo-truncate (echo_truncate) ------------------------------
(with-echo-state
 (lambda ()
   (ses "hello world")
   ((%sym '--echo-truncate) 5)
   (check "cut/truncate-shortens" "hello" (ges))
   ;; no-op when already short enough.
   (ses "ab")
   ((%sym '--echo-truncate) 5)
   (check "cut/truncate-noop" "ab" (ges))))
