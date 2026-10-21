;;; fixture-imp9.el --- real-path fixture of M60 imp-9 (row 28a).
;;;
;;; Loaded by test/m60/probe-imp3.scm mode `control' through the elisp
;;; READER and then the elisp EVALUATOR (`elisp-load-source-file'), so the
;;; 3 branches `cond', `let*' and `while' run on the REAL path and not on
;;; hand-built datum (cr.org F8).  The `setq' side effects are the proof.
;;;
;;; cr.org F2: the comparison and the arithmetic FUNCTION cells are EMPTY
;;; on the plain path, so this file uses no arithmetic and no comparison.
;;; `(cond (nil))' is the portable way to get elisp nil here: the reader
;;; form `(quote ())' is the empty list, and the empty list is TRUTHY for
;;; `elisp-loader-truthy?'.
(defconst m60-fixture-outer 'outer)
(setq m60-fixture-cond-t (cond (nil 'no) (t 'yes)))
(setq m60-fixture-cond-otherwise (cond (nil 'no) (otherwise 'other)))
(setq m60-fixture-cond-none (cond (nil 'no)))
(setq m60-fixture-cond-test-only (cond ('plain-test-value)))
;; `let*': the 2nd INIT reads the 1st name, and the OUTER value comes
;; back after the form (F3 restore, dynamic binding).
(setq m60-fixture-let* (let* ((m60-fixture-outer 'inner)
                              (m60-fixture-second m60-fixture-outer))
                         (cons m60-fixture-second m60-fixture-outer)))
(setq m60-fixture-restored m60-fixture-outer)
;; F5: a BARE SYMBOL binding binds elisp nil.
(setq m60-fixture-bare (let* (m60-fixture-q) m60-fixture-q))
;; `while': the test runs before the body and the value is always nil.
(defconst m60-fixture-steps '())
(defconst m60-fixture-rest (cons 1 (cons 2 (cond (nil)))))
(setq m60-fixture-while (while m60-fixture-rest
                          (setq m60-fixture-steps
                                (cons (car m60-fixture-rest) m60-fixture-steps))
                          (setq m60-fixture-rest (cdr m60-fixture-rest))))
