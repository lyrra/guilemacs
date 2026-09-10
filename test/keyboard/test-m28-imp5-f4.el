;;; test-m28-imp5-f4.el --- M28 imp-5 family 4 (--timer-check reclaim
;;; + --tty- / --timer- / --read- / --reset- stay-C audit).
;;;
;;; Verifies the M28 imp-5 family-4 reclaim commit in brief.org:
;;; --timer-check (a thin double-hop into C timer_check (), which already
;;; dispatches into (emacs timers) timer-check) is deleted, and the other
;;; 29 family-4 shims stay C (raw C state).  The recorded reasons live in
;;; docs/kb.org.
;;;
;;; Wraps test/keyboard/test-m28-imp5-f4.scm — the Scheme test corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results`
;;; (list of (NAME STATUS) pairs) and reports each via princ.  Same
;;; harness as test-m28-imp5-f3.el.

(princ "=== m28-imp5 family-4 --timer-check reclaim + audit test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m28-imp5-f4.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M28I5F4-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M28I5F4-READBACK-ERROR: %S\n" e)) '())))
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
