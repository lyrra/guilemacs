;;; test-m22-imp3.el --- M22 imp-3 parity test suite.
;;;
;;; imp-3: ports of adjust-point-for-property, the input-mode quartet
;;; (set-input-interrupt-mode / set-output-flow-control /
;;; set-input-meta-mode / set-quit-char), the track-mouse trio
;;; (some-mouse-moved / tracking-off / internal-track-mouse) and
;;; stuff-buffered-input to Scheme.
;;;
;;; Wraps test/keyboard/test-m22-imp3.scm — the Scheme test corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results`
;;; (list of (NAME STATUS) pairs) and reports each via princ.  Same
;;; harness as test-m22-input-pending.el.

(princ "=== m22 imp-3 test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m22-imp3.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M22-IMP3-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M22-IMP3-READBACK-ERROR: %S\n" e)) '())))
      (pass 0)
      (fail 0))
  (dolist (result results)
    (let* ((name (car result))
           (status (cadr result))
           (ok (eq status 'PASS)))
      (if ok
          (setq pass (1+ pass))
        (setq fail (1+ fail)))
      (princ (format "%s %s%s\n" (if ok "PASS" "FAIL") name
                     (if ok "" (format " %S" (cdr result)))))))
  (princ (format "=== %d passed, %d failed, %d total ===\n"
                 pass fail (+ pass fail))))
