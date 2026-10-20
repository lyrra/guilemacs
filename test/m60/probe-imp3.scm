;;; probe-imp3.scm --- M60 imp-3 plain-guile probe fixture.
;;;
;;; M60 imp-2 measured the standalone-load boundary of
;;; docs/m60-plan.org section 3 in a plain `guile' process.  This fixture
;;; does NOT load the C core and does NOT load loadup.el: it loads the
;;; Scheme modules of mod/ only.
;;;
;;; M60 imp-3 keeps the 5 modes of imp-2 without a semantic change and
;;; adds mode `language': the REGISTRATION observable of the split.  That
;;; mode calls Guile's own `lookup-language' for `emacs-elisp' and prints
;;; the object, its title, and its name.  A module that loads is not
;;; proof; the language object is.
;;;
;;; Usage (one MODE per process; a stub from one mode must not hide the
;;; next result):
;;;
;;;   GUILEMACS_ROOT=$PWD GUILE_AUTO_COMPILE=0 \
;;;     guile -L mod test/m60/probe-imp3.scm MODE
;;;
;;; MODE is one of `cells', `provide', `stubs', `negative', `noboot',
;;; `registration', or `language'.  The fixture prints `key: value'
;;; lines on stdout.  It reads the repo root from GUILEMACS_ROOT only, so
;;; a run from any working directory is the same run.  `negative' is the R4 negative
;;; control; it needs its own process, because it installs a faithful
;;; `provide' cell.  `noboot' skips the boot on purpose: it is the
;;; MEASUREMENT that shapes the control (M60 imp-4).
;;;
;;; `init-loader' leaves the current module at (emacs-elisp runtime), so
;;; the fixture restores (guile-user) after the call (measured: without
;;; the restore, the `load-elisp' of a real file resolves the wrong
;;; module).

(use-modules (ice-9 format))
(use-modules (emacs loader)
             (emacs-elisp runtime)
             (emacs utils))

(define (die msg)
  (format (current-error-port) "probe-imp3: ~a~%" msg)
  (exit 2))

(define root (getenv "GUILEMACS_ROOT"))
(unless (and root (not (string=? root "")))
  (die "GUILEMACS_ROOT must be set to the repo root"))

(define (arg-mode)
  (let ((args (command-line)))
    (if (>= (length args) 2) (cadr args) "cells")))

(define mode (arg-mode))

(define (show key fmt . args)
  (format #t "~a: ~a~%" key (apply format #f fmt args)))

(define (guarded-cell-empty? sym)
  (not (symbol-fbound? sym)))

;;; --- boot -----------------------------------------------------------

;; The prelude path is the same path that src/emacs takes at startup.  A
;; plain `guile' process has no C bootstrap, so `init-loader' is the only
;; registration wave that runs.  Mode `noboot' is the ONE exception: it
;; measures what a control WITHOUT the boot stops at, so the boot is
;; skipped there.
(unless (string=? mode "noboot")
  (init-loader (string-append root "/prelude"))
  (set-current-module (resolve-module '(guile-user))))

;;; --- helpers --------------------------------------------------------

(define guarded-names
  '(get-load-suffixes append symbol-value car expand-file-name
    file-directory-p cdr intern concat substring eval))

(define var-names
  '(load-path load-suffixes load-file-rep-suffixes load-read-function))

(define (empty-cells)
  (let loop ((names guarded-names) (acc '()))
    (cond ((null? names) (reverse acc))
          ((guarded-cell-empty? (car names))
           (loop (cdr names) (cons (car names) acc)))
          (else (loop (cdr names) acc)))))

;; One plain-value stub: a procedure that answers #t for every argument.
;; The stub is NOT a faithful elisp primitive; it only fills the function
;; cell so that the loader can pass the call.
(define (a-stub . _) #t)

(define (install-stub! sym)
  (set-symbol-function! sym a-stub))

(define (try-load rel)
  "Load REL (repo-root-relative) and return (ok VALUE), where VALUE is
the value that `load-elisp' returns, or (error KEY ARGS)."
  (catch #t
    (lambda ()
      ;; The elisp loader reads `%load-path', which `init-loader' filled
      ;; with the lisp/ dirs, so the base name is enough.
      (list 'ok (load-elisp (basename rel))))
    (lambda (key . args)
      (cons 'error (cons key args)))))

(define (describe result)
  (cond ((and (pair? result) (eq? (car result) 'ok))
         (format #f "~s" (cadr result)))
        ((and (pair? result) (eq? (car result) 'error))
         (format #f "ERROR ~a ~s" (cadr result) (cddr result)))
        (else (format #f "~s" result))))

(define (elisp-featurep feature)
  "The elisp `featurep' of FEATURE, as a plain Scheme test.  The real
`featurep' is a C DEFUN (src/fns.c) and its function cell is EMPTY in a
plain `guile' process (measured), so the fixture uses the elisp
definition itself: a `memq' over the `features' list."
  (and (symbol-bound? 'features)
       (and (memq feature (symbol-value 'features)) #t)))

(define (load-line rel)
  (show (string-append "LOAD " rel) "~a" (describe (try-load rel))))

;;; --- mode: cells ----------------------------------------------------

(define (mode-cells)
  ;; EMPTY-CELLS is the list of the 11 guarded names whose function cell
  ;; is empty after `init-loader'.  The M55 imp-3 result claims ().
  (show "EMPTY-CELLS" "~s" (empty-cells))
  (show "UNGUARDED" "load=~s autoload-do-load=~s"
        (symbol-fbound? 'load) (symbol-fbound? 'autoload-do-load))
  (show "VARS" "~a"
        (string-join (map (lambda (s)
                            (format #f "~a=~s" s (symbol-bound? s)))
                          var-names)
                     " "))
  (show "ASYM" "require=~s provide=~s"
        (symbol-fbound? 'require) (symbol-fbound? 'provide))
  (load-line "lisp/subdirs.el")
  (load-line "lisp/cdl.el")
  ;; M60 imp-4 acceptance: mode `cells' never installs the 2 cells, so
  ;; these 3 words come from the 2 guarded forms of `init-loader' and
  ;; from NOWHERE else.  `featurep' is a C DEFUN, so its own cell is
  ;; empty here and the plain-Scheme definition is used.
  (show "featurep-fbound" "~s" (symbol-fbound? 'featurep))
  (show "featurep cdl" "~s" (elisp-featurep 'cdl))
  (show "features" "~s" (symbol-value 'features))
  (load-line "lisp/obarray.el")
  (load-line "lisp/hex-util.el")
  (show "FEATURES-BOUND" "~s" (symbol-bound? 'features)))

;;; --- mode: provide --------------------------------------------------

(define (mode-provide)
  ;; M60 imp-4: `init-loader' already bound both cells, so these lines
  ;; are the state AT START, not the empty-cell state of imp-3.  This
  ;; mode is a FIXTURE: it installs both cells itself, so it measures the
  ;; LOAD, not the home.  The home is proven by mode `cells'.
  (show "features-bound-at-start" "~s" (symbol-bound? 'features))
  (show "provide-fbound-at-start" "~s" (symbol-fbound? 'provide))
  ;; The address in the sentinel changes between runs, so a check pins
  ;; only the words.
  (show "symbol-value features" "~s" (symbol-value 'features))
  ;; The faithful cell: the real elisp primitive of (emacs utils).
  (set-symbol-function! 'provide elisp-provide)
  (set-symbol-value! 'features nil-value)
  (show "LOAD cdl" "~a" (describe (try-load "lisp/cdl.el")))
  (show "featurep-fbound" "~s" (symbol-fbound? 'featurep))
  (show "featurep cdl" "~s" (elisp-featurep 'cdl))
  (show "features" "~s" (symbol-value 'features))
  (show "require-fbound" "~s" (symbol-fbound? 'require)))

;;; --- mode: stubs ----------------------------------------------------

;; One pure stub at a time, in this order.  The first stop that a pure
;; stub can NOT pass is the `defvar' evaluator branch: the minimal
;; evaluator has no branch for `defvar', so the variable cell stays
;; unbound and the load raises void-variable -- not void-function.

(define (mode-stubs)
  (install-stub! 'provide)
  (show "stub-provide / cdl" "~a" (describe (try-load "lisp/cdl.el")))
  (install-stub! 'defconst)
  (show "stub-defconst / obarray" "~a" (describe (try-load "lisp/obarray.el")))
  (install-stub! 'eval-when-compile)
  (show "stub-eval-when-compile / hex-util" "~a"
        (describe (try-load "lisp/hex-util.el")))
  (install-stub! 'normal-top-level-add-to-load-path)
  (show "stub-ntl / subdirs" "~a" (describe (try-load "lisp/subdirs.el")))
  ;; The faithful provide, with the `features' variable bound: the last
  ;; good point.
  (set-symbol-function! 'provide elisp-provide)
  (set-symbol-value! 'features nil-value)
  (show "faithful-provide / cdl" "~a" (describe (try-load "lisp/cdl.el")))
  (show "featurep-fbound" "~s" (symbol-fbound? 'featurep))
  (show "featurep cdl" "~s" (elisp-featurep 'cdl))
  (show "features" "~s" (symbol-value 'features)))

;;; --- mode: negative -------------------------------------------------

;; The R4 negative control, in its OWN process (L3): the faithful
;; `provide' cell is installed and the `features' variable is NOT bound.
;; The load of lisp/cdl.el must error, and the error must name the
;; unbound sentinel -- it is NOT a `void-function' stop.
;;
;; M60 imp-4: `init-loader' now binds `features' (row 19), so a control
;; that simply skips the boot would also lose the reader cells that
;; `init-loader' installs, and the load would stop with `Wrong type to
;; apply: #nil' before `provide' ever runs.  Mode `noboot' is the
;; REPEATABLE record of that measurement.  So this mode takes the FULL
;; boot, like every other mode, and then UNBINDS the value cell of
;; `features' again with `makunbound!' -- the exported helper that is
;; also the elisp primitive of mod/emacs/boot.scm:10.  No private
;; binding is touched: `symbol-bound?' (mod/emacs-elisp/runtime.scm
;; :388) reports the unset variable as UNBOUND, not as #nil.  Only
;; `features' is unbound; `provide' stays installed.
(define (mode-negative)
  (makunbound! 'features)
  (show "features-bound" "~s" (symbol-bound? 'features))
  (show "provide-fbound" "~s" (symbol-fbound? 'provide))
  (show "LOAD cdl" "~a" (describe (try-load "lisp/cdl.el"))))

;;; --- mode: noboot ---------------------------------------------------

;; M60 imp-4, F3 of the review of 174f0d2db: the MEASUREMENT behind the
;; shape of mode `negative'.  This mode takes NO boot, as brief.org
;; section 8 proposed, and installs `provide' only.  MEASURED 2026-10-20:
;; without `init-loader' the reader cells are gone too, so the load of
;; lisp/cdl.el stops with `Wrong type to apply: #nil'.  That error does
;; NOT name the unbound sentinel, so the control can not use this shape.
(define (mode-noboot)
  (set! %load-path (cons (string-append root "/lisp") %load-path))
  (set-current-module (resolve-module '(guile-user)))
  (set-symbol-function! 'provide elisp-provide)
  (show "features-bound" "~s" (symbol-bound? 'features))
  (show "provide-fbound" "~s" (symbol-fbound? 'provide))
  (show "LOAD cdl" "~a" (describe (try-load "lisp/cdl.el"))))

;;; --- mode: registration ---------------------------------------------

;; The named blocker.  The use-modules runs in THIS fresh process and the
;; error propagates: the backtrace names the Guile site, and the exit
;; status is not 0.  Nothing is caught, so a change that makes the
;; module load correctly shows up as exit status 0.
(define (mode-registration)
  (show "registration-attempt" "use-modules (emacs-elisp spec)")
  (force-output)
  (use-modules (emacs-elisp spec))
  (show "registration-result" "loaded"))

;;; --- mode: language -------------------------------------------------

;; The imp-3 acceptance observable, in a FRESH plain `guile' process: the
;; language object that Guile's own `lookup-language' returns.  The
;; module resolve of imp-2 is NOT proof -- (emacs-elisp spec) always
;; resolved.  Every line is caught, so a raise prints `ERROR key args'
;; and the check keeps a stable shape.
(define (mode-language)
  (catch #t
    (lambda ()
      (use-modules (system base language))
      (let ((lang (lookup-language 'emacs-elisp)))
        (show "LANGUAGE?" "~s" (language? lang))
        (show "LANGUAGE-TITLE" "~s" (language-title lang))
        (show "LANGUAGE-NAME" "~s" (language-name lang))))
    (lambda (key . args)
      (show "ERROR" "~a ~s" key args))))

;;; --- dispatch -------------------------------------------------------

(case (string->symbol mode)
  ((cells) (mode-cells))
  ((provide) (mode-provide))
  ((stubs) (mode-stubs))
  ((negative) (mode-negative))
  ((noboot) (mode-noboot))
  ((registration) (mode-registration))
  ((language) (mode-language))
  (else (die (format #f "unknown mode ~a (cells|provide|stubs|negative|noboot|registration|language)"
                     mode))))
