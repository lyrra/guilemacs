;;; test-m28-imp4.el --- M28 imp-4 Steps 1-3: record-primitive, bucket-A,
;;; and bucket-C (keyremap) port suite.
;;;
;;; Verifies the M28 imp-4 Step 1 deliverable (brief.org): the five
;;; thin slot-index record primitives (--rks-record-get-int /
;;; --rks-record-set-int / --rks-record-get / --rks-record-set /
;;; --rks-record-set-bool) are deleted from src/keyboard.c and
;;; rks-sync-read / rks-sync-write now move <rks-state> fields with the
;;; srfi-9 accessors directly.  The corpus's later sections assert the
;;; Step 2 bucket-A DELETE set and the Step 3 bucket-C keyremap port.
;;;
;;; Wraps test/keyboard/test-m28-imp4.scm — the Scheme test corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results`
;;; (list of (NAME STATUS) pairs) and reports each via princ.  Same
;;; harness as test-m28-imp3.el.

(princ "=== m28-imp4 Step 1 record-primitive test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m28-imp4.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M28I4-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M28I4-READBACK-ERROR: %S\n" e)) '())))
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
