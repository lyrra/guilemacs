;;; test-m38-imp1-fixture.el --- M38 imp-1 count-mismatch fixture.
;;;
;;; Normally all three ERT tests pass.  With GUILEMACS_M38_FIXTURE=middle
;;; the middle test fails; with GUILEMACS_M38_FIXTURE=last the last test
;;; fails.  Either way ERT prints "passed 3/3" for the last passing test
;;; while only two names passed -- the harness count mismatch that D1 must
;;; turn into a non-zero exit (brief.org M38 imp-1, Step 6 behavior check).
;;;
;;; The "last" mode pins review finding F1: the old guard used the index of
;;; the last "passed N/M" line, which stops at the last pass, so a failing
;;; LAST test left the guard quiet (false green).  The names a/m/z keep the
;;; failing test away from the last position in "middle" mode, and force it
;;; to the last position in "last" mode, under either definition order or
;;; name order.  GUILEMACS_M38_FIXTURE=1 is kept as an alias for "middle".
;;;
;;; This file is registered in its own group, outside the keyboard group,
;;; so the normal gate stays green.  The m38-imp1 corpus runs this fixture
;;; stressed (both modes) with GUILEMACS_M38_FIXTURE set.

(princ "=== m38 imp-1 count-mismatch fixture ===\n")

(let* ((mode (or (getenv "GUILEMACS_M38_FIXTURE") ""))
       (mid-fail (or (string= mode "1") (string= mode "middle")))
       (last-fail (string= mode "last"))
       ;; a/m/z order the cases so the failing test can be the middle one
       ;; (mid-fail) or the last one (last-fail); the others pass.  ERT runs
       ;; the tests in this definition order, so "last" puts the failure at
       ;; the last position.
       (cases `(("m38-imp1-fixture/a" . t)
                ("m38-imp1-fixture/m" . ,(not mid-fail))
                ("m38-imp1-fixture/z" . ,(not last-fail)))))
  (dolist (case cases)
    (eval `(ert-deftest ,(intern (car case)) ()
             (should ,(cdr case))))))
