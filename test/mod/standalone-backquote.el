;;; M60 imp-21 fixture: `backquote' is a VALUE BUILDER (row 28b).
;;;
;;; The loader branch is the `backquote' branch of
;;; `elisp-loader-eval-form' (mod/emacs/loader.scm).  It calls
;;; `elisp-loader-backquote-walk' at depth 1.  The head that this reader
;;; makes is the 1-CHARACTER symbol `(intern "`")' (reader.scm :545), so
;;; the branch tests BOTH heads.
;;;
;;; Only forms of CLOSED rows are used here: `defconst', `defvar',
;;; `defmacro', `defun', `let', `cond', `setq' and `quote'.

;; 1. The 2 names that the unquotes read.
(defconst m60-bq-b 2)
(defconst m60-bq-c '(3 4))

;; 2. A `,' at depth 1 evaluates, and a `,@' at depth 1 splices the
;;    ELEMENTS of its proper list.  The value is (1 2 3 4 5).
(defconst m60-bq-basic `(1 ,m60-bq-b ,@m60-bq-c 5))

;; 3. The NESTED case: at depth 2 the `,' is NOT evaluated, so the inner
;;    form keeps the 1-character backquote head and the `,' head (L55).
(defconst m60-bq-nested `(a `(b ,m60-bq-c)))

;; 3b. The NESTED SPLICE case: a `,@' at depth 2 also keeps its structure
;;    and does NOT raise (L56, cr.org F2 of this round).
(defconst m60-bq-nested-splice `(a `(b ,@m60-bq-c)))

;; 3c. A VECTOR argument is walked too, so a `,' evaluates and a `,@'
;;    spreads inside it (cr.org F3 of this round).  The value is [1 2 3 4].
(defconst m60-bq-vector `[1 ,m60-bq-b ,@m60-bq-c])

;; 3d. The SHAPE of a DELAYED unquote: at depth 2 the argument is a FORM
;;    and it is not evaluated.  The `,' lands in the head of a pair whose
;;    tail is the processed cdr, so the result is the proper 2-element
;;    list (<,> (list 1 2)) and never a dotted pair (cr.org F6 of this
;;    round: lisp/emacs-lisp/backquote.el :121, :229).
(defconst m60-bq-nested-form `(a `(b ,(list 1 2))))

;; 4. The load continues after the forms above.
(defconst m60-bq-tail t)
