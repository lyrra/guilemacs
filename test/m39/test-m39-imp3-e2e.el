;;; test-m39-imp3-e2e.el --- M39 imp-3 end-to-end accessor suite.
;;;
;;; The companion corpus test/m39/test-m39-imp3.scm pins the static wire
;;; (the retired DEFUNs, the C bridge table, the module).  This file pins
;;; the live behaviour: it calls the moved accessors on a real pipe
;;; process and checks each result.  It is split from
;;; test/m39/test-m39-imp3.el because the guilemacs elisp loader is
;;; fragile with a large single test file (a corpus wrapper plus a full
;;; e2e block segfaults the loader); two small files load cleanly.
;;;
;;; Each check is printed as PASS/FAIL and turned into an ERT test so the
;;; harness counts it.

(princ "=== m39 imp-3 (process Group A accessors) e2e suite ===\n")

(require 'imp-ert-report)

(let* ((pipe (condition-case err
                 (make-pipe-process :name "m39-imp3-pipe" :noquery t)
               (error nil)))
       (made (processp pipe))
       (pass 0)
       (fail 0))
  (imp-register-bool-as-ert-test "m39-imp3/e2e/make-pipe-process" made)
  (if made (setq pass (1+ pass)) (setq fail (1+ fail)))
  (princ (format "%s m39-imp3/e2e/make-pipe-process\n"
                 (if made "PASS" "FAIL")))
  (when made
    (dolist (c (list
                (cons "m39-imp3/e2e/process-id-nil"
                      (lambda () (null (process-id pipe))))
                (cons "m39-imp3/e2e/set-process-plist-roundtrip"
                      (lambda ()
                        (and (equal (set-process-plist pipe '(:a 1 :b 2))
                                    '(:a 1 :b 2))
                             (equal (process-plist pipe) '(:a 1 :b 2)))))
                (cons "m39-imp3/e2e/query-on-exit-flag-roundtrip"
                      (lambda ()
                        (set-process-query-on-exit-flag pipe nil)
                        (let ((off (null (process-query-on-exit-flag pipe))))
                          (set-process-query-on-exit-flag pipe t)
                          (and off (process-query-on-exit-flag pipe) t))))
                (cons "m39-imp3/e2e/set-inherit-flag-returns-arg"
                      (lambda ()
                        (eq (set-process-inherit-coding-system-flag
                             pipe 'y)
                            'y)))
                (cons "m39-imp3/e2e/process-coding-system-cons"
                      (lambda () (consp (process-coding-system pipe))))
                (cons "m39-imp3/e2e/process-mark-marker"
                      (lambda () (markerp (process-mark pipe))))
                ;; Kept C DEFUN still works through the same process.
                (cons "m39-imp3/e2e/kept-process-status"
                      (lambda () (symbolp (process-status pipe))))))
      (let* ((name (car c))
             (res (condition-case err (funcall (cdr c)) (error nil))))
        (imp-register-bool-as-ert-test name res)
        (if res (setq pass (1+ pass)) (setq fail (1+ fail)))
        (princ (format "%s %s\n" (if res "PASS" "FAIL") name))))
    (ignore-errors (delete-process pipe)))
  (princ (format "=== %d passed, %d failed, %d total ===\n"
                 pass fail (+ pass fail))))
