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
;;; `require', `defs', `macros', `registration', `language',
;;; `obsolete', `control', `arith', or `put'.  Mode `defs' is the M60 imp-6 record of
;;; rows 21 and 22 (`defconst', `defvar').  Mode `macros' is the M60
;;; imp-7 record of rows 23 and 24 (`defmacro' and
;;; `eval-when-compile').  Mode `control' is the M60 imp-9 record of row
;;; 28a (`cond', `let*', `while').  Mode `arith' is the M60 imp-10 record
;;; of row 29 (the comparison and arithmetic cells, `length' and
;;; `nreverse').  Mode `put' is the M60 imp-11 record of row 30 (the
;;; `put' symbol-property cell).  The
;;; fixture prints `key: value' lines on stdout.  It reads the repo root
;;; from GUILEMACS_ROOT only, so
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

; --- mode: require --------------------------------------------------

;; M60 imp-5 (row 20).  This mode needs its OWN process: it changes the
;; `features' list and the elisp `load-path' variable.  Every value comes
;; from the installed cell of `init-loader', so no cell is stubbed here.
(define (call-require . args)
  (apply (symbol-function 'require) args))

;; The formatted MESSAGE of the Guile `misc-error' that `error' raises, or
;; #f.  Guile stores the payload as (#f "~A ~S" (FORMAT . ARGS)).  NOTE: a
;; docstring on this procedure breaks the call (measured 2026-10-21: the
;; handler raised `Unbound variable: ~A' before the first body form), so
;; the explanation is a comment, not a docstring.
(define (misc-error-message key rest)
  (cond
   ((not (eq? key 'misc-error)) #f)
   ((< (length rest) 3) #f)
   ((not (list? (list-ref rest 2))) #f)
   (else
    (let ((fmt (car (list-ref rest 2)))
          (vals (cdr (list-ref rest 2))))
      (if (string? fmt) (apply format #f fmt vals) #f)))))

;; Run `require' on ARGS and format the value, or the error, as a line.  A
;; raise is caught, so the check keeps a stable shape.  A `misc-error'
;; prints its MESSAGE, not the raw argument list: that message is what the
;; C `error' of src/fns.c :3604 produces.
(define (describe-require . args)
  (catch #t
    (lambda () (describe (list 'ok (apply call-require args))))
    (lambda (key . rest)
      (let ((msg (misc-error-message key rest)))
        (if msg
            (format #f "ERROR ~a ~a" key msg)
            (format #f "ERROR ~a ~s" key rest))))))

(define (mode-require)
  (show "REQUIRE-FBOUND" "~s" (symbol-fbound? 'require))
  (show "features-at-start" "~s" (symbol-value 'features))
  ;; The acceptance observable of brief.org section 8: the feature is not
  ;; loaded, so the cell loads lisp/cdl.el and returns the symbol.
  (show "REQUIRE cdl" "~a" (describe-require 'cdl))
  (show "features" "~s" (symbol-value 'features))
  ;; Empty the ELISP variable, not %load-path: `search-elisp-load-path'
  ;; (:709) reads the variable, and it stops the loop only on #nil.  A
  ;; real load would now fail on the missing file, so this line proves
  ;; that no 2nd load runs.
  (set-symbol-value! 'load-path #nil)
  (show "REQUIRE-AGAIN" "~a" (describe-require 'cdl))
  ;; Step 6 of the cell: the file loads to the END and provides ANOTHER
  ;; feature, so the second `memq' fails and the cell raises the C message
  ;; "Required feature `%s' was not provided" (src/fns.c :3604).
  (show "REQUIRE-NOT-PROVIDED" "~a"
        (describe-require 'no-such-feature (string-append root "/lisp/cdl.el")))
  ;; No file of that name: the `load' protocol raises, and NOERROR is nil.
  (show "REQUIRE-MISSING" "~a" (describe-require 'no-such-feature))
  ;; NOERROR is t: the failed load returns the ELISP nil, never #t.
  (show "REQUIRE-NOERROR" "~a" (describe-require 'no-such-feature #nil #t)))

;;; --- mode: defs -----------------------------------------------------

;; M60 imp-6 (rows 21 and 22).  `elisp-loader-eval' is NOT in the
;; #:export list of (emacs loader), so the fixture resolves it with
;; `module-ref'.  The current module was restored to (guile-user) after
;; `init-loader', so the value cells are the ordinary elisp ones.
;;
;; These forms change neither `features' nor `load-path', so this mode
;; shares the boot of the other modes.
;;
;; The RETURN VALUE of every form is printed: `set-symbol-value!' returns
;; the VALUE, so a branch that ends with that call would hand a loaded
;; file the value, not the symbol.
(define (mode-defs)
  (let ((eval-form (module-ref (resolve-module '(emacs loader))
                               'elisp-loader-eval)))
    ;; Row 21: `defconst' stores ALWAYS.
    (show "defconst ret" "~s / ~s"
          (eval-form '(defconst m60-probe-c 1))
          (eval-form '(defconst m60-probe-c 2)))
    (show "defconst value" "~s" (symbol-value 'm60-probe-c))
    ;; The DOC element is IGNORED and NOT evaluated: `(/ 1 0)' would
    ;; raise if the branch evaluated the 3rd element.
    (show "defconst doc ret" "~s"
          (eval-form '(defconst m60-probe-d 1 (/ 1 0))))
    (show "defconst doc value" "~s" (symbol-value 'm60-probe-d))
    ;; Row 22: `defvar' stores ONCE and never overwrites a bound symbol.
    (show "defvar ret" "~s / ~s"
          (eval-form '(defvar m60-probe-v 1))
          (eval-form '(defvar m60-probe-v 2)))
    (show "defvar value" "~s" (symbol-value 'm60-probe-v))
    ;; No INIT keeps the cell EMPTY.  This is the observable that
    ;; separates the 2 rows: `defconst' BINDS the cell with #nil, even
    ;; with no INIT, and `defvar' does not.
    (show "defvar no-init ret" "~s" (eval-form '(defvar m60-probe-w)))
    (show "defvar no-init bound" "~s" (symbol-bound? 'm60-probe-w))
    ;; A1 of the review: `(defconst SYMBOL)' is NOT legal elisp (INIT is
    ;; required).  The branch is LENIENT and binds the cell to #nil.  The
    ;; line is pinned as a deviation, not as elisp behaviour.
    (show "defconst no-init bound (lenient)" "~s"
          (begin (eval-form '(defconst m60-probe-x))
                 (symbol-bound? 'm60-probe-x)))))

;;; --- mode: macros ---------------------------------------------------

;; M60 imp-7 (rows 23 and 24).  The elisp reader of (emacs reader) is
;; resolved LAZILY: no other mode imports it, so the import can not move
;; the lines of a mode that a corpus already pins.
(define (read-hex-util-form1)
  (let ((port (open-input-file (string-append root "/lisp/hex-util.el"))))
    (dynamic-wind
      (lambda () #t)
      (lambda ()
        ((module-ref (resolve-module '(emacs reader)) 'elisp-read-from-port)
         port))
      (lambda () (close-port port)))))

;; Row 23 stores the expander in a SCHEME table, so its lookup is NOT a
;; function cell.  Row 24 is a DECISION: the body of a
;; `eval-when-compile' runs at LOAD time, because a source-reading loader
;; has no compile phase.
(define (mode-macros)
  (let ((eval-form (module-ref (resolve-module '(emacs loader))
                               'elisp-loader-eval))
        (macro-ref (module-ref (resolve-module '(emacs loader))
                               'elisp-loader-macro-ref)))
    ;; The branch returns the SYMBOL, and the elisp FUNCTION cell stays
    ;; EMPTY: `symbol-function' and `symbol-fbound?' read that cell, and
    ;; a full Emacs owns it in C.
    (show "defmacro ret" "~s"
          (eval-form '(defmacro m60-probe-m (x) (quote 7))))
    (show "defmacro fbound" "~s" (symbol-fbound? 'm60-probe-m))
    ;; The stored expander is a procedure.  Print the stable token only:
    ;; the printed address changes between runs.
    (show "defmacro expander" "procedure=~s"
          (procedure? (macro-ref 'm60-probe-m)))
    ;; The call does NOT evaluate its argument: `(m60-probe-missing-fn)'
    ;; would raise if it ran.  `7' proves that it did not run.
    (show "defmacro call noeval" "~s"
          (eval-form '(m60-probe-m (m60-probe-missing-fn))))
    ;; M60 imp-7 fix (cr.org F3, limit L8): a later `defun' SHADOWS the
    ;; macro.  Emacs keeps the 2 forms in ONE cell, so the table entry is
    ;; dropped and the call reaches the function cell: `9'.
    (eval-form '(defun m60-probe-m (x) 9))
    (show "defun shadow expander" "~s" (macro-ref 'm60-probe-m))
    (show "defun shadow fbound" "~s" (symbol-fbound? 'm60-probe-m))
    (show "defun shadow call" "~s" (eval-form '(m60-probe-m 1)))
    ;; Row 24, on the REAL file: its form 1 is the `eval-when-compile'
    ;; block.  The branch returns the value of its LAST body form, that
    ;; is the SYMBOL `num-to-hex-char'.
    (show "eval-when-compile form1 ret" "~s"
          (eval-form (read-hex-util-form1)))
    ;; The 2 `defmacro' forms of that block are now in the table.
    (show "stored expanders" "hex-char-to-num=~s num-to-hex-char=~s"
          (procedure? (macro-ref 'hex-char-to-num))
          (procedure? (macro-ref 'num-to-hex-char)))
    ;; The whole file, on the real load path.
    (load-line "lisp/hex-util.el")
    (show "featurep hex-util" "~s" (elisp-featurep 'hex-util))))

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

;;; --- mode: obsolete -------------------------------------------------

;; M60 imp-8 (row 27).  The 2 observables that mode `cells' does NOT
;; print: the RETURN VALUE of the procedure and the MARK.  Both come from
;; the guarded install of `init-loader', so the call goes through the
;; elisp FUNCTION cell with the elisp evaluator, not through a Scheme
;; variable.  L15: `EMPTY-CELLS' is a FIXED 11-name list and does not hold
;; `make-obsolete-variable', so it is NOT the proof of row 27.
(define (mode-obsolete)
  ;; The whole file on the real load path: was `ERROR void-function
  ;; (make-obsolete-variable)' at imp-7.
  (load-line "lisp/obarray.el")
  (let ((eval-form (module-ref (resolve-module '(emacs loader))
                               'elisp-loader-eval)))
    ;; The return value must be the SYMBOL.  `elisp-put' returns the
    ;; VALUE, so a procedure that ended with that call prints the mark.
    (show "RETURN" "~a"
          (eval-form '(make-obsolete-variable
                       'obarray-default-size
                       "obarrays now grow automatically." "30.1")))
    ;; The mark keeps the SOURCE order of byte-run.el :576.  The 3-arity
    ;; form passes #nil, so field 2 is #nil and not ().
    (show "MARK" "~s"
          (elisp-get 'obarray-default-size 'byte-obsolete-variable))))

;;; --- mode: control --------------------------------------------------

;; M60 imp-9 (row 28a).  The 3 branches `cond', `let*' and `while' of
;; `elisp-loader-eval-form', plus the 3 recorded FIRST STOPS of real
;; `.el' files.  Every value comes from the live `guile' child, never
;; from a copied number.
;;
;; `elisp-loader-eval' is not exported, so the fixture gets it with
;; `module-ref'.  NOTE: in this evaluator `nil' is `#nil' and the reader
;; returns `()' for the empty list; `()' is TRUTHY for
;; `elisp-loader-truthy?' (a limit of the `if' branch that predates row
;; 28a).  So every loop below ends on `#nil' and NOT on `()': the
;; `while' counter walks a DOTTED list whose tail is `nil'.
(define (mode-control)
  (let ((eval-form (module-ref (resolve-module '(emacs loader))
                               'elisp-loader-eval)))
    ;; `cond': the catch-all `t' clause, the `otherwise' clause, no
    ;; match, an empty clause list, a clause with a TEST only, and the
    ;; first match that wins.
    (show "cond t-clause" "~s" (eval-form '(cond (nil 1) (t 2))))
    (show "cond otherwise-clause" "~s" (eval-form '(cond (nil 1) (otherwise 2))))
    (show "cond no-match" "~s" (eval-form '(cond (nil 1) (nil 2))))
    (show "cond empty" "~s" (eval-form '(cond)))
    (show "cond test-only-true" "~s" (eval-form '(cond ((quote yes)))))
    (show "cond test-only-false" "~s" (eval-form '(cond (nil))))
    (show "cond first-match-wins" "~s"
          (eval-form '(cond (t (quote a)) (t (quote b)))))
    ;; `let*': the 2nd INIT reads the 1st name, and the 1st name is
    ;; RESTORED after the form (dynamic binding, limit L18).
    (eval-form '(defconst m60-probe-o 1))
    (show "let* later-init-sees-earlier" "~s"
          (eval-form '(let* ((m60-probe-o 2) (m60-probe-p m60-probe-o))
                        (cons m60-probe-o m60-probe-p))))
    (show "let* restored-after" "~s" (symbol-value 'm60-probe-o))
    (show "let* no-init" "~s" (eval-form '(let* ((m60-probe-q)) m60-probe-q)))
    (show "let* body-last-value" "~s"
          (eval-form '(let* ((m60-probe-r 1)) (quote first) (quote last))))
    ;; `while': a counter that runs N times, a false FIRST test that runs
    ;; the body 0 times, a 0-form body, and the always-#nil value.
    (eval-form '(defconst m60-probe-rest (quote (1 2 . #nil))))
    (eval-form '(defconst m60-probe-steps nil))
    (show "while return" "~s"
          (eval-form '(while m60-probe-rest
                        (setq m60-probe-steps
                              (cons (car m60-probe-rest) m60-probe-steps))
                        (setq m60-probe-rest (cdr m60-probe-rest)))))
    (show "while steps" "~s" (symbol-value 'm60-probe-steps))
    (show "while rest-after" "~s" (symbol-value 'm60-probe-rest))
    (eval-form '(defconst m60-probe-zero nil))
    (show "while false-first-test return" "~s"
          (eval-form '(while m60-probe-zero
                        (setq m60-probe-zero (quote ran)))))
    (show "while false-first-test body-runs" "~s"
          (symbol-value 'm60-probe-zero))
    (show "while empty-body" "~s" (eval-form '(while nil)))
    ;; The 3 recorded FIRST STOPS of real `.el' files on the plain path.
    ;; None of the 3 is `cond', `let*' or `while': a real file stops on
    ;; an EARLIER missing cell (the deviation of brief.org section 3).
    (load-line "lisp/subr.el")
    (load-line "lisp/calendar/time-date.el")
    (load-line "lisp/color.el")
    ;; The cr.org fixes of the row-28a branches.  A raising INIT restores
    ;; the names that are bound already (F3), a DUPLICATE name gets the
    ;; OUTER value back (F4), and a BARE SYMBOL binding binds elisp nil
    ;; (F5).
    (eval-form '(defconst m60-probe-dup 0))
    (show "let* duplicate-value" "~s"
          (eval-form '(let* ((m60-probe-dup 1) (m60-probe-dup 2)) m60-probe-dup)))
    (show "let* duplicate-after" "~s" (symbol-value 'm60-probe-dup))
    (eval-form '(defconst m60-probe-dup 0))
    (show "let duplicate-value" "~s"
          (eval-form '(let ((m60-probe-dup 1) (m60-probe-dup 2)) m60-probe-dup)))
    (show "let duplicate-after" "~s" (symbol-value 'm60-probe-dup))
    ;; cr.org F4: `let' maps EVERY init BEFORE it binds any name, so the
    ;; 2nd INIT reads the OUTER value 1 and not the 1st binding 2.  This
    ;; is parallel binding.  Only the `let*' order was pinned before.
    (eval-form '(defconst m60-probe-par 1))
    (show "let parallel-init" "~s"
          (eval-form '(let ((m60-probe-par 2) (m60-probe-par-2 m60-probe-par))
                        m60-probe-par-2)))
    (eval-form '(defconst m60-probe-leak 'outer))
    (show "let* init-raises" "~s"
          (catch #t
            (lambda ()
              (eval-form '(let* ((m60-probe-leak 'inner)
                                 (m60-probe-leak-2 no-such-variable))
                            m60-probe-leak))
              'no-error)
            (lambda (key . args) key)))
    (show "let* leak-after" "~s" (symbol-value 'm60-probe-leak))
    (show "let* bare-symbol" "~s"
          (eval-form '(let* (m60-probe-bare) m60-probe-bare)))
    (show "let bare-symbol" "~s"
          (eval-form '(let (m60-probe-bare) m60-probe-bare)))
    ;; The REAL path (cr.org F8): a TRACKED fixture `.el' file goes
    ;; through the elisp reader and then the elisp evaluator, and the
    ;; `setq' side effects are the proof.  This is not hand-built datum.
    (let ((load-source (module-ref (resolve-module '(emacs loader))
                                   'elisp-load-source-file)))
      (show "real load" "~s"
            (catch #t
              (lambda ()
                (load-source (string-append root "/test/m60/fixture-imp9.el"))
                'done)
              (lambda (key . args) (cons key args))))
      (show "real cond t-clause" "~s" (symbol-value 'm60-fixture-cond-t))
      (show "real cond otherwise-clause" "~s"
            (symbol-value 'm60-fixture-cond-otherwise))
      (show "real cond no-match" "~s" (symbol-value 'm60-fixture-cond-none))
      (show "real cond test-only" "~s"
            (symbol-value 'm60-fixture-cond-test-only))
      (show "real let* later-init-sees-earlier" "~s"
            (symbol-value 'm60-fixture-let*))
      (show "real let* restored-after" "~s" (symbol-value 'm60-fixture-restored))
      (show "real let* bare-symbol" "~s" (symbol-value 'm60-fixture-bare))
      (show "real while steps" "~s" (symbol-value 'm60-fixture-steps))
      (show "real while return" "~s" (symbol-value 'm60-fixture-while)))))

;;; --- mode: arith ----------------------------------------------------

;; M60 imp-10 (row 29).  The comparison and arithmetic function cells,
;; plus `length' and `nreverse'.  Every name already had a pure-Scheme
;; definition, so the work is 1 GUARDED install per name, in
;; `init-loader'.  In a full Emacs the C DEFUN (src/data.c, src/fns.c)
;; owns the cell; `symbol-fbound?' keeps it.
;;
;; The list is MEASURED, not copied: `CELLS' prints the state of every
;; name after `init-loader' ran, and `COUNT' prints how many of them are
;; still EMPTY.  After the imp-10 installs, `COUNT' is 0.
;;
;; The 3 LOAD lines are the recorded FIRST STOPS of the 3 real `.el'
;; files of milestone.org section 2.  `lisp/color.el' stopped at `/'; it
;; must move past that form after this row.  The other 2 stop on rows 30
;; and 31 and stay.
;;
;; The CALL lines prove that the installed cell is a real elisp
;; primitive and not only a bound cell: every value is `#t' or `#nil'.
;; `(eq? '#nil #f)' is FALSE, so a caller must pass the value through
;; `elisp-loader-truthy?' (loader.scm :1062).  The 2 TRUTHY lines pin
;; that rule (F6 of the imp-10 cr.org review).
;;
;; L23 is MEASURED here too: `elisp-/` with 0 arguments, and
;; `check-number-coerce-marker' on a marker (L22), reach the `signal'
;; and `markerp' cells, and both are still EMPTY on the plain path.

(define arith-names
  '(eq eql equal null + - * / = < > 1+ 1- length nreverse))

(define (arith-empty-names)
  (let loop ((names arith-names) (acc '()))
    (cond ((null? names) (reverse acc))
          ((guarded-cell-empty? (car names))
           (loop (cdr names) (cons (car names) acc)))
          (else (loop (cdr names) acc)))))

(define (arith-call name . args)
  ;; Apply the INSTALLED function cell NAME to ARGS: the cell is what a
  ;; real elisp caller uses, not the Scheme binding.  An EMPTY cell
  ;; returns #nil, and `(apply #nil ARGS)' would abort the whole mode
  ;; (measured), so the empty state prints as `unbound'.
  (if (symbol-fbound? name)
      (apply (symbol-function name) args)
      'unbound))

(define (mode-arith)
  ;; F4 of the imp-10 cr.org review: the old format `~a=~s' is
  ;; AMBIGUOUS, because `=' and `<' are NAMES: the pair `< #t' printed as
  ;; `<==#t', which a reader can read as "the cell of `=' is bound to
  ;; #t".  `~s' quotes the name and ` -> ' separates it from the value,
  ;; so no name can absorb the separator.
  (show "CELLS" "~a"
        (string-join (map (lambda (s)
                            (format #f "~s -> ~s" s (symbol-fbound? s)))
                          arith-names)
                     " "))
  ;; The non-numeric cells.
  (show "CALL eq" "~s" (arith-call 'eq 'a 'a))
  (show "CALL eq-miss" "~s" (arith-call 'eq 'a 'b))
  (show "CALL eql" "~s" (arith-call 'eql 1 1))
  (show "CALL equal" "~s" (arith-call 'equal (list 1 2) (list 1 2)))
  (show "CALL null" "~s" (arith-call 'null '()))
  (show "CALL null-false" "~s" (arith-call 'null 1))
  (show "CALL length" "~s" (arith-call 'length (list 1 2 3)))
  (show "CALL nreverse" "~s" (arith-call 'nreverse (list 1 2 3)))
  ;; The arithmetic and comparison cells.
  (show "CALL +" "~s" (arith-call '+ 1 2 3))
  (show "CALL -" "~s" (arith-call '- 10 4))
  (show "CALL *" "~s" (arith-call '* 2 3))
  (show "CALL /" "~s" (arith-call '/ 8 2))
  (show "CALL 1+" "~s" (arith-call '1+ 41))
  (show "CALL 1-" "~s" (arith-call '1- 43))
  (show "CALL = " "~s" (arith-call '= 2 2))
  (show "CALL <" "~s" (arith-call '< 1 2))
  (show "CALL >" "~s" (arith-call '> 2 1))
  (show "CALL >-false" "~s" (arith-call '> 1 2))
  ;; F6 of the imp-10 cr.org review: a comparison cell answers `#nil',
  ;; not `#f'.  Guile 3 also treats `#nil' as FALSE in a plain `if'
  ;; (MEASURED), but `#nil' is NOT `#f', so a caller must not compare
  ;; with `#f' and must use `elisp-loader-truthy?' (loader.scm :1062).
  ;; The first line is the hazard, the second line is the required route.
  (show "TRUTHY #nil-is-not-#f" "~s" (eq? (arith-call '> 1 2) #f))
  (show "TRUTHY elisp-loader-truthy?" "~s"
        ((@@ (emacs loader) elisp-loader-truthy?) (arith-call '> 1 2)))
  ;; The 3 recorded first stops, in milestone.org section 2 order.
  (load-line "lisp/color.el")
  (load-line "lisp/calendar/time-date.el")
  (load-line "lisp/subr.el")
  ;; L15: this is the FIXED 11-name list, so it stays () and is NOT the
  ;; proof of row 29.  The proof is the CELLS line and COUNT above.
  (show "EMPTY-CELLS" "~s" (empty-cells))
  (show "COUNT" "~a" (length (arith-empty-names)))
  ;; L22 and L23: the 2 cells that a number-only caller does not reach.
  (show "signal-fbound" "~s" (symbol-fbound? 'signal))
  (show "markerp-fbound" "~s" (symbol-fbound? 'markerp)))


;;; --- mode: put ------------------------------------------------------

;; M60 imp-11 (row 30).  The `put' symbol-property cell.  The pure
;; definition `elisp-put' already exists (mod/emacs/utils.scm :164) and
;; (emacs utils) is imported as a WHOLE module (loader.scm :20), so this
;; row adds 1 GUARDED install in `init-loader' and NO procedure and NO
;; import.
;;
;; WHY `put' and not `get': `put' is the FIRST stop of a real file on the
;; plain path.  MEASURED with a tracing install: the caller is
;; lisp/emacs-lisp/macroexp.el :137,
;;
;;   (put 'macroexp--funcall-if-compiled 'byte-compile (lambda ...))
;;
;; lisp/calendar/time-date.el :39 does (require 'cl-lib) and
;; cl-lib.el :87 does (require 'macroexp), so the stop is 2 requires
;; below time-date.el.  time-date.el itself calls no `put' (measured:
;; grep -n '(put ' finds no call).
;;
;; The CALL lines pin the elisp semantics (MEASURED): `put' returns the
;; VALUE, not the plist; the elisp nil value is `#nil'; 2 properties on 1
;; symbol are both kept; and a STRING or a NUMBER first argument raises
;; `Wrong type argument: symbolp'.
;;
;; L26: the NEXT stop is `make-hash-table' (lisp/emacs-lisp/macroexp.el
;; :168).  `elisp-make-hash-table' is EXPORTED (utils.scm :28) but has NO
;; definition (measured: `module-ref' raises), so a later row must write
;; that procedure first.  This row does not fix that cell.

(define (put-call name . args)
  ;; Apply the INSTALLED `put' cell, so the call goes through the same
  ;; path as a real elisp caller.  An EMPTY cell would apply #nil.
  (if (symbol-fbound? name)
      (apply (symbol-function name) args)
      'unbound))

;; The MESSAGE of the Guile `misc-error' of an elisp `(error FMT . ARGS)'
;; call, or #f.  Guile stores the payload FLAT, so the format string and
;; its argument list are 2 ADJACENT elements.  The `misc-error-message'
;; helper above reads a DIFFERENT shape, so this mode uses its own walk.
;; MEASURED, not assumed:
;;   (error "Wrong type argument: symbolp" "x")
;;   => rest = (#f "Wrong type argument: symbolp ~S" ("x") #f)
(define (error-text rest)
  (let loop ((items rest))
    (cond ((null? items) #f)
          ((null? (cdr items)) #f)
          ((and (string? (car items)) (list? (cadr items)))
           (apply format #f (car items) (cadr items)))
          (else (loop (cdr items))))))

(define (describe-error thunk)
  ;; The stable token of a raise: the Guile key and the elisp message.
  ;; The address in an object never prints.
  (catch #t
    (lambda () (list 'ok (thunk)))
    (lambda (key . rest)
      (let ((text (error-text rest)))
        (if text
            (format #f "ERROR ~a ~a" key text)
            (format #f "ERROR ~a ~s" key rest))))))

(define (mode-put)
  ;; The subject cell, then the neighbour cells that the same `require'
  ;; chain needs.  The `get' cell is EMPTY here: row 30 installs `put'
  ;; only (F3 owns `get' and `featurep').
  (show "CELLS" "~s -> ~s ~s -> ~s ~s -> ~s"
        'put (symbol-fbound? 'put)
        'get (symbol-fbound? 'get)
        'make-hash-table (symbol-fbound? 'make-hash-table))
  (show "CALL put symbol-property" "~s"
        (put-call 'put 'm60-probe-prop 'm60-probe-key 42))
  ;; The VALUE is the return value, and (get) reads it back through the
  ;; PLIST, not through a Scheme variable.
  (show "CALL get after put" "~s" (elisp-get 'm60-probe-prop 'm60-probe-key))
  ;; The elisp nil value, not #f.
  (show "CALL put nil value" "~s" (put-call 'put 'm60-probe-prop 'm60-probe-nil #nil))
  (show "CALL get nil value" "~s" (elisp-get 'm60-probe-prop 'm60-probe-nil))
  ;; 2 different properties on 1 symbol are both kept.
  (put-call 'put 'm60-probe-prop 'm60-probe-2 'second)
  (show "CALL 2 properties" "~s ~s"
        (elisp-get 'm60-probe-prop 'm60-probe-key)
        (elisp-get 'm60-probe-prop 'm60-probe-2))
  ;; A non-symbol first argument raises, as elisp does.
  (show "CALL string first arg" "~a"
        (describe-error (lambda () (put-call 'put "m60-probe-str" 'k 1))))
  (show "CALL number first arg" "~a"
        (describe-error (lambda () (put-call 'put 7 'k 1))))
  ;; The 3 recorded FIRST STOPS.  `color.el' is done; `time-date.el'
  ;; moves from `put' to the NEXT empty cell of its require chain, and
  ;; `subr.el' stops on row 31.
  (load-line "lisp/color.el")
  (load-line "lisp/calendar/time-date.el")
  (load-line "lisp/subr.el"))

;;; --- dispatch -------------------------------------------------------

(case (string->symbol mode)
  ((cells) (mode-cells))
  ((provide) (mode-provide))
  ((stubs) (mode-stubs))
  ((negative) (mode-negative))
  ((noboot) (mode-noboot))
  ((require) (mode-require))
  ((defs) (mode-defs))
  ((macros) (mode-macros))
  ((registration) (mode-registration))
  ((language) (mode-language))
  ((obsolete) (mode-obsolete))
  ((control) (mode-control))
  ((arith) (mode-arith))
  ((put) (mode-put))
  (else (die (format #f "unknown mode ~a (cells|provide|stubs|negative|noboot|require|defs|macros|registration|language|obsolete|control|arith|put)"
                     mode))))
