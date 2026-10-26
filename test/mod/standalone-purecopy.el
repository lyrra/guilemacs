;;; M60 imp-22 fixture: `purecopy' is the IDENTITY (row 37).
;;;
;;; The ROW UNDER TEST is row 37 (`purecopy').  The cell is
;;; `elisp-purecopy' of (emacs types) :439, installed by the guarded
;;; block of `init-loader' (mod/emacs/loader.scm :1843 = the guard,
;;; :1844 = the install; cr.org F6 FIX, the OLD text said :1838).
;;; The C owner is `DEFUN ("purecopy", Fpurecopy,
;;; Spurecopy, 1, 1, 0)' at src/alloc.c :1513, and its body is
;;; `return obj;'.  The argument
;;; vector names NO type predicate, so a call raises no
;;; `wrong-type-argument'.  This host has no pure space, so
;;; `make_pure_c_string' (:1502) and `pure_cons' (:1508) are not
;;; reached.
;;; Limit L59: the answer of a MUTABLE object is the SAME object.  A
;;; dumping vanilla build copies it into pure space.
;;;
;;; The HELPER forms are all of CLOSED rows: `defconst', `defmacro',
;;; `quote' and `list'.  The row under test is named above, not here.

;; 1. A MACRO whose EXPANDER BODY calls `purecopy' on a list.  This is
;;    the shape of the REAL callers: `lisp/emacs-lisp/byte-run.el' :540
;;    and `lisp/custom.el' :169 call it inside an expander, not at top
;;    level.
(defmacro m60-purecopy-macro (x)
  (purecopy (list 'quote x)))

;; 2. The macro at top level, and its value in a variable.  A missing
;;    cell raises `void-function (purecopy)' HERE.
(defconst m60-purecopy-expanded (m60-purecopy-macro m60-purecopy-value))

;; 3. The identity for a string and for an integer.
(defconst m60-purecopy-string (purecopy "m60-purecopy-string"))
(defconst m60-purecopy-integer (purecopy 42))

;; 4. The load continues after the forms above.
(defconst m60-purecopy-tail t)
