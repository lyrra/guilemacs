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
  #:export (face-attribute-relative-verdict
            bitmap-spec-verdict))

;; The 3-branch combine of the C text at src/xfaces.c :4187 ... :4192.
;; C reads the 3 type tests; this procedure combines them.
(define (face-attribute-relative-verdict same-as-unspecified?
                                         height?
                                         fixnum?)
  (if same-as-unspecified? #t (and height? (not fixnum?))))

;; M59 imp-4: the accept rule of the C text at src/xfaces.c :825 ...
;; :860 at the imp-4 base (the body of `Fbitmap_spec_p'; after the MOVE
;; those lines hold the dispatcher and the new body).  C reads the CONSP
;; unpack, the type tests, and the BYTE length SBYTES (a Scheme
;; (string-length ...) counts characters and answers wrong on a multibyte
;; DATA string); this procedure combines the 4 plain values.
;; 2147483647 is INT_MAX and 7 is CHAR_BIT - 1: the C text uses both, so
;; both are stated here.
;;
;; (+ width 7) / 8 gives bytes-per-row >= 1 because width >= 1, so the
;; second quotient has no zero divisor.  A field that is not of the
;; expected type crosses as -1; the (>= data-bytes 0) test comes first
;; so the quotient never sees that sentinel.  Every clause is pure and
;; total, so the clause order does not change the value.  The -verdict
;; suffix matches face-attribute-relative-verdict.
(define (bitmap-spec-verdict file-name? width height data-bytes)
  (if file-name?
      #t
      (and (>= width 1) (<= width 2147483647)
           (>= height 1) (<= height 2147483647)
           (>= data-bytes 0)
           (let ((bytes-per-row (quotient (+ width 7) 8)))
             (<= height (quotient data-bytes bytes-per-row))))))
