;;; test-m28-imp5-f5.el --- M28 imp-5 family 5 (--button-down-location
;;; pair reclaim + --menu- / --x- / --tool- / --tab- / --button- stay-C
;;; audit).
;;;
;;; Verifies the M28 imp-5 family-5 reclaim commit in brief.org:
;;; --button-down-location and --set-button-down-location (the dead
;;; whole-vector getter/setter over the C static button_down_location,
;;; both with zero callers) are deleted, and the other 31 family-5 shims
;;; stay C (raw C state).  The recorded reasons live in docs/kb.org.
;;;
;;; Wraps test/keyboard/test-m28-imp5-f5.scm — the Scheme test corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results`
;;; (list of (NAME STATUS) pairs) and reports each via princ.  Same
;;; harness as test-m28-imp5-f4.el.

(princ "=== m28-imp5 family-5 --button-down-location reclaim + audit test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m28-imp5-f5.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M28I5F5-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M28I5F5-READBACK-ERROR: %S\n" e)) '())))
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
