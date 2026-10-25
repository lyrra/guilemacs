;;; M60 imp-19 fixture: `&optional' and `&rest' in a parameter list (L4).
;;;
;;; The 3 parameter shapes of brief.org section 8.  The binder is
;;; `elisp-loader-bind-params!' (mod/emacs/loader.scm, branches B2 ... B4
;;; of the comment block above it), and the C peer is `funcall_lambda'
;;; (src/eval.c :2167).  A missing optional argument must bind the elisp
;;; nil `#nil' (brief.org D1), and the name after `&rest' must bind the
;;; WHOLE remaining list (brief.org D3).
;;;
;;; The macro body calls `list' and `quote' only: the backquote reader is
;;; row 28b and stays OPEN, so this fixture must not use `.
(defmacro standalone-optional-m (a &optional b) (list 'quote (list a b)))
(defun standalone-optional-f (a &rest r) (list a r))
(defun standalone-optional-g (a &optional b &rest c) (list a b c))

;; 1. Both arguments present: `b' is the second argument.
(setq standalone-optional-m-2 (standalone-optional-m 1 2))
;; 2. Short argument list: `b' is the elisp nil.
(setq standalone-optional-m-1 (standalone-optional-m 1))
;; 3. `&rest' takes the WHOLE remaining list, for 2, 1 and 0 extra
;; arguments.  The 0 case gives the empty Scheme list: the elisp `null'
;; cell answers #t for it, while `(eq? #nil REST)' is #f (D3, measured).
(setq standalone-optional-f-2 (standalone-optional-f 1 2 3))
(setq standalone-optional-f-1 (standalone-optional-f 1 2))
(setq standalone-optional-f-0 (standalone-optional-f 1))
;; 4. The 3 shapes in 1 call: required, optional, rest.
(setq standalone-optional-g-4 (standalone-optional-g 1 2 3 4))
