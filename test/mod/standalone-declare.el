;;; M60 imp-20 fixture: `declare' is DATA, not a call (row 36).
;;;
;;; The loader branch is `((eq? head 'declare) #nil)' of
;;; `elisp-loader-eval-form' (mod/emacs/loader.scm).  The names below are
;;; NOT bound: the loader raises `void-function' if it evaluates an
;;; argument of the form.
;;;
;;; The macro body stays free of backquote: row 28b is OPEN, so a
;;; backquote in this fixture would test the wrong row.

;; 1. A top-level form with 0 arguments is legal.
(declare)

;; 2. The value of a 0-argument form is the elisp nil.
(defconst m60-declare-empty (declare))

;; 3. The argument is NOT evaluated: `m60-declare-must-not-run' is unbound.
(defconst m60-declare-value (declare (m60-declare-must-not-run)))

;; 4. A DOTTED shape is legal too: the branch reads NO element (L51).
(defconst m60-declare-dotted (declare a . b))

;; 5. The REACHABLE shape: a declaration is the FIRST body form of a
;;    macro.  `m60-declare-macro' returns the argument form, so the
;;    expansion is 42.
(defmacro m60-declare-macro (x)
  (declare (indent 1))
  x)

(defconst m60-declare-expand (m60-declare-macro 42))

;; 6. The load continues after the forms above.
(defconst m60-declare-tail t)

;; 7. L14: a declaration in the BODY of a `defun' is data at CALL time
;;    too.  `lisp/obarray.el' :35 is the real site, and a load does not
;;    evaluate a body, so the CALL is what must not raise.  The call
;;    answers the body value 7.
(defun m60-declare-obarray-size ()
  (declare (obsolete "use the vector length" "31.1"))
  7)

(defconst m60-declare-call (m60-declare-obarray-size))
