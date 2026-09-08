;;; test-m28-imp3.el --- M28 imp-3 (batched ring reads + forwarder cut-over) suite.
;;;
;;; Verifies the M28 imp-3 read-path crossing reduction (brief.org M28
;;; imp-3): the batching subr --kbd-empty-p registers and behaves and
;;; the queue-empty tests are rewired to it, the dispatch prologue keeps
;;; its three scalar crossings (an early --kbd-peek-event batch was
;;; removed for a bench regression, cr.org F3), the wait-path
;;; some-mouse-moved / gobble-input! forwarders are cut over to direct
;;; Scheme calls, and the store -> read-decoded pipeline still returns
;;; the stored char code.
;;;
;;; Wraps test/keyboard/test-m28-imp3.scm — the Scheme test corpus.
;;; Loads the Scheme file via eval-scheme, then reads back `test-results`
;;; (list of (NAME STATUS) pairs) and reports each via princ.  Same
;;; harness as test-m28-imp1.el / test-m27-ring-storage.el.

(princ "=== m28-imp3 read-path crossing test suite ===\n")

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m28-imp3.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M28I3-CORPUS-LOAD-ERROR: %S\n" err)))))

(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M28I3-READBACK-ERROR: %S\n" e)) '())))
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
