;;; faces.scm --- M59 imp-3: the face-attribute-relative-p DECISION
;;;                ((emacs faces))
;;;
;;; M59 imp-3 moves the DECISION of `face-attribute-relative-p' from C
;;; to Scheme.  The procedure below replaces the 3-branch combine of the
;;; C text at src/xfaces.c :4187 ... :4192 (the body of
;;; `Fface_attribute_relative_p').  That inline decision is DELETED: the
;;; decision is now in Scheme, not in C.
;;;
;;; C keeps the DEFUN registration, the doc string, the 3 keyword
;;; symbols (:height, `unspecified', :ignore-defface), and the 3 type
;;; tests.  A type test on a Lisp_Object is a C read; the combine of the
;;; 3 results is the decision, and that is here.
;;;
;;; Every value that crosses the layer is plain: 3 booleans in, 1
;;; boolean out.  No Lisp_Object, no struct, no hook, no descriptor
;;; crosses the layer (the M42 rule).  The procedure is pure: no
;;; defelisp, no FFI leaf, no set!, no I/O, no primitive-load.
;;;
;;; The rewrite of the old C text as 3 plain booleans:
;;;
;;;   a  the value is relative by keyword: it is `unspecified' or the
;;;      keyword :ignore-defface (NOT the symbol `ignore-defface')
;;;   b  the attribute is :height
;;;   c  the value is a fixnum
;;;
;;; The truth table of the old C text:
;;;
;;;   a  b  c  verdict
;;;   t  -  -  t        branch 1 wins before the :height test
;;;   f  t  t  f        a fixnum height is absolute
;;;   f  t  f  t        a float height is relative
;;;   f  f  -  f        branch 3
;;;
;;; So the combine is one expression: (if a #t (and b (not c))).

(define-module (emacs faces)
  #:export (face-attribute-relative-verdict))

;; The 3-branch combine of the C text at src/xfaces.c :4187 ... :4192.
;; C reads the 3 type tests; this procedure combines them.
(define (face-attribute-relative-verdict same-as-unspecified?
                                         height?
                                         fixnum?)
  (if same-as-unspecified? #t (and height? (not fixnum?))))
