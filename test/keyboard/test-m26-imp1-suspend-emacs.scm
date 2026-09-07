;;; test-m26-imp1-suspend-emacs.scm --- M26 imp-1 (emacs interrupt) corpus.
;;;
;;; Covers the M26 imp-1 cutover (brief.org M26): the suspend-emacs
;;; *policy* moved out of src/keyboard.c into (emacs interrupt) as
;;; `suspend-emacs'.  The C DEFUN is now a one-line dispatcher into the
;;; module.
;;;
;;; The raw terminal mechanics stay C behind the M26 shims
;;; (--multiple-tty-frames?, --tty-size, --sys-subshell,
;;; --change-frame-size) plus the pre-M26 --reset-all-sys-modes /
;;; --init-all-sys-modes / --sys-suspend shims.  This corpus exercises
;;; the moved policy logic:
;;;
;;;   - the module exports `suspend-emacs' (what the C dispatcher's
;;;     scm_c_public_ref needs);
;;;   - --multiple-tty-frames? is callable and reports the single/no-tty
;;;     case of the batch harness (so the multi-tty guard is inert here);
;;;   - a non-string stuffstring is rejected before any terminal call
;;;     (the CHECK_STRING-equivalent wrong-type-argument error);
;;;   - with every terminal-touching shim fset-stubbed, a full
;;;     suspend-emacs call runs `suspend-hook' and `suspend-resume-hook'
;;;     and takes the sys_suspend branch (cannot-suspend nil) vs the
;;;     sys_subshell branch (cannot-suspend non-nil);
;;;   - a tty-size change after resume triggers --change-frame-size.
;;;
;;; suspend-emacs calls its shims through (%c '--name) on every call
;;; (not a defelisp delay — see input-poll.scm Finding 2), so the test
;;; fset-stubs them by replacing each symbol's function cell for the
;;; duration of a call, restoring after (module-set! / set-symbol-value!
;;; pattern, same as test-m19-*/m25-*).  Every stub is restored in a
;;; dynamic-wind unwind, so nothing leaks into later corpora.
;;;
;;; NOTE (close-out): a real end-to-end suspend/resume cannot be
;;; automated here — sys_suspend would stop the runner and sys_subshell
;;; would fork it (see the --sys-suspend doc).  The real --tty-size is
;;; likewise not invoked: in batch CURTTY() may have no controlling
;;; terminal, so get_tty_size would read from a NULL/pipe fd.  That is
;;; why --tty-size is fset-stubbed below and the size-change logic is
;;; verified against a synthetic (old . new) pair.
;;;
;;; Sourced by test/keyboard/test-m26-imp1-suspend-emacs.el via
;;; eval-scheme.  Accumulates PASS/FAIL entries into `test-results` for
;;; readback from elisp.  See brief.org M26 imp-1.

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

;; #t iff THUNK raises an elisp wrong-type-argument signal (the condition
;; elisp `signal` produces: key elisp-condition, args (wrong-type-argument ...)).
;; #f if it returns normally or raises anything else.
(define (caught-wrong-type-argument? thunk)
  (catch #t
    (lambda () (thunk) #f)
    (lambda (key . args)
      (and (eq? key 'elisp-condition)
           (pair? args)
           (eq? (car args) 'wrong-type-argument)))))

;; Stub one or more (SYM . PROC) function cells for the duration of
;; THUNK, restoring the original function cell afterwards.
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

;; Hooks fire markers: a symbol whose function cell records the call.
(define hook-fired? #f)
(define resume-hook-fired? #f)
(set-symbol-function! 'm26-suspend-marker
                      (lambda () (set! hook-fired? #t) #nil))
(set-symbol-function! 'm26-resume-marker
                      (lambda () (set! resume-hook-fired? #t) #nil))

;;; --- 1. Cutover wiring: module resolves ------------------------------
;; The C dispatcher (Fsuspend_emacs) does
;; scm_c_public_ref ("emacs interrupt", "suspend-emacs"); verify the
;; module exports it as a procedure.
(check "interrupt/exported-suspend-emacs" #t
       (procedure? (module-ref (resolve-interface '(emacs interrupt))
                               'suspend-emacs)))

;;; --- 2. --multiple-tty-frames?: single/no-tty harness ----------------
;; Batch runs with a single (or no) controlling tty, so the guard must
;; report nil here.  A real multi-tty case cannot be arranged in the
;; harness without opening a second tty frame (would need a real second
;; terminal), so this asserts the callable + inert (nil) path only —
;; not a fabricated multi-tty pass.
(check "multiple-tty-frames?/callable-and-single" #nil
       ((%c '--multiple-tty-frames?)))

;;; --- 3. CHECK_STRING-equivalent: non-string stuffstring --------------
;; suspend-emacs with a non-string stuffstring must signal
;; wrong-type-argument before any terminal call.  The call never reaches
;; --sys-suspend / --tty-size, so it is safe un-stubbed.  42 is a
;; non-string (fixnum).
(let ((raised (catch #t
                (lambda () (suspend-emacs 42) #f)
                (lambda (key . args) (list 'error key args)))))
  (check "suspend-emacs/non-string-stuffstring-signals" #t
         (and (pair? raised)
              (eq? (car raised) 'error))))
;; Precise check: the signal is specifically wrong-type-argument (the
;; CHECK_STRING-equivalent), not any unrelated error.
(check "suspend-emacs/non-string-is-wrong-type-argument" #t
       (caught-wrong-type-argument?
        (lambda () (suspend-emacs 42))))

;;; --- 3b. C DEFUN cutover: dispatcher forwards to the Scheme body -----
;; Fsuspend_emacs (C) is now a thin forward into (emacs interrupt)
;; suspend-emacs via scm_c_public_ref.  Calling the *elisp* suspend-emacs
;; (the C DEFUN, resolved through %c) with a non-string stuffstring must
;; signal wrong-type-argument — proving the C dispatcher resolves the
;; Scheme module and the ported string check runs.  Safe: the error fires
;; before any terminal call.
(let ((raised (catch #t
                (lambda () ((%c 'suspend-emacs) 42) #f)
                (lambda (key . args) (list 'error key args)))))
  (check "suspend-emacs/c-defun-forwards-and-signals" #t
         (and (pair? raised) (eq? (car raised) 'error)))
  (check "suspend-emacs/c-defun-is-wrong-type-argument" #t
         (caught-wrong-type-argument?
          (lambda () ((%c 'suspend-emacs) 42)))))

;;; --- 4. Full policy run, terminal shims stubbed -----------------------
;; Exercise the whole ported body deterministically: stub every
;; terminal-touching shim, set the two hooks, and run suspend-emacs with
;; #nil stuffstring.  cannot-suspend is nil by default → sys_suspend
;; branch.  --tty-size returns the same (old = new) pair both times, so
;; --change-frame-size must NOT fire.
(define stubs
  (list (cons '--reset-all-sys-modes (lambda () #nil))
        (cons '--init-all-sys-modes  (lambda () #nil))
        (cons '--tty-size            (lambda () (cons 80 24)))
        (cons '--sys-suspend         (lambda () #nil))
        (cons '--sys-subshell        (lambda () #nil))
        (cons '--change-frame-size   (lambda (w h) #nil))))
(with-stubs!
 stubs
 (lambda ()
   (let ((old-sh (get-var 'suspend-hook))
         (old-rh (get-var 'suspend-resume-hook))
         (old-can (get-var 'cannot-suspend)))
     (dynamic-wind
       (lambda ()
         (set-symbol-value! 'suspend-hook '(m26-suspend-marker))
         (set-symbol-value! 'suspend-resume-hook '(m26-resume-marker))
         (set-symbol-value! 'cannot-suspend #nil))
       (lambda ()
         (suspend-emacs #nil)
         (check "suspend-emacs/hook-ran" #t hook-fired?)
         (check "suspend-emacs/resume-hook-ran" #t resume-hook-fired?))
       (lambda ()
         (restore-var! 'suspend-hook old-sh)
         (restore-var! 'suspend-resume-hook old-rh)
         (restore-var! 'cannot-suspend old-can))))))

;;; --- 5. cannot-suspend branch + size-change, shims stubbed -----------
;; (a) cannot-suspend = t → sys_subshell branch, not sys_suspend.
;; (b) first --tty-size returns (80 . 24), second returns (100 . 40):
;;     the size changed, so --change-frame-size fires with (100 40).
(define saw-suspend #f)
(define saw-subshell #f)
(define saw-resize #f)
(define resize-args #nil)
(with-stubs!
 (list (cons '--reset-all-sys-modes (lambda () #nil))
       (cons '--init-all-sys-modes  (lambda () #nil))
       (cons '--tty-size            (lambda () (cons 100 40)))
       (cons '--sys-suspend         (lambda () (set! saw-suspend #t) #nil))
       (cons '--sys-subshell        (lambda () (set! saw-subshell #t) #nil))
       (cons '--change-frame-size   (lambda (w h)
                                      (set! saw-resize #t)
                                      (set! resize-args (list w h))
                                      #nil)))
 (lambda ()
   (let ((old-sh (get-var 'suspend-hook))
         (old-rh (get-var 'suspend-resume-hook))
         (old-can (get-var 'cannot-suspend)))
     (dynamic-wind
       (lambda ()
         (set-symbol-value! 'suspend-hook '(m26-suspend-marker))
         (set-symbol-value! 'suspend-resume-hook '(m26-resume-marker))
         (set-symbol-value! 'cannot-suspend #t))
       (lambda ()
         ;; --tty-size is stubbed to (100 . 40) here but suspend-emacs
         ;; calls it twice (old-size then size).  With cannot-suspend t
         ;; the subshell branch runs; a resize fires because the *saved*
         ;; old pair must differ from the post pair.  To make old != new
         ;; deterministically we cannot use the same stub for both, so
         ;; instead this section asserts the subshell branch; the resize
         ;; is exercised separately in section 6.
         (suspend-emacs #nil)
         (check "suspend-emacs/subshell-branch" #t saw-subshell)
         (check "suspend-emacs/no-suspend-branch" #f saw-suspend))
       (lambda ()
         (restore-var! 'suspend-hook old-sh)
         (restore-var! 'suspend-resume-hook old-rh)
         (restore-var! 'cannot-suspend old-can))))))

;;; --- 6. tty-size change → --change-frame-size, shims stubbed ---------
;; A --tty-size stub that returns (80 . 24) on its first call and
;; (100 . 40) afterwards lets us observe the old != new path firing
;; --change-frame-size with the new size.
(define size-calls 0)
(define resized-calls 0)
(define resize-wh #nil)
(with-stubs!
 (list (cons '--reset-all-sys-modes (lambda () #nil))
       (cons '--init-all-sys-modes  (lambda () #nil))
       (cons '--tty-size            (lambda ()
                                      (set! size-calls (1+ size-calls))
                                      (if (= size-calls 1)
                                          (cons 80 24)
                                          (cons 100 40))))
       (cons '--sys-suspend         (lambda () #nil))
       (cons '--sys-subshell        (lambda () #nil))
       (cons '--change-frame-size   (lambda (w h)
                                      (set! resized-calls (1+ resized-calls))
                                      (set! resize-wh (list w h))
                                      #nil)))
 (lambda ()
   (let ((old-sh (get-var 'suspend-hook))
         (old-rh (get-var 'suspend-resume-hook))
         (old-can (get-var 'cannot-suspend)))
     (dynamic-wind
       (lambda ()
         (set-symbol-value! 'suspend-hook '(m26-suspend-marker))
         (set-symbol-value! 'suspend-resume-hook '(m26-resume-marker))
         (set-symbol-value! 'cannot-suspend #nil))
       (lambda ()
         (suspend-emacs #nil)
         (check "suspend-emacs/resize-on-size-change" #t
                (> resized-calls 0))
         (check "suspend-emacs/resize-with-new-size" '(100 40) resize-wh))
       (lambda ()
         (restore-var! 'suspend-hook old-sh)
         (restore-var! 'suspend-resume-hook old-rh)
         (restore-var! 'cannot-suspend old-can))))))
