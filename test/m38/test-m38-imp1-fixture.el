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
;;; Two more modes pin the TOT == 0 fix in run-tests-loadup-emacs (the
;;; empty-group blind spot found running a real full suite: a bare "0
;;; tests" result is ambiguous between "this group's tests are legitimately
;;; tag-excluded" and "the subprocess crashed before ERT ever ran"):
;;;
;;;   - GUILEMACS_M38_FIXTURE=empty registers no test at all, but loads
;;;     cleanly.  ERT still runs to completion and prints its own "Ran 0
;;;     tests, 0 results as expected, 0 unexpected" summary -- the same
;;;     shape a file whose only test is tagged :unstable/:expensive-test/
;;;     :nativecomp produces (e.g. test/lisp/cedet/srecode/fields-tests.el
;;;     in the real suite).  This must NOT be flagged: it is indistinguishable
;;;     from legitimate tag exclusion, and flagging it would make every such
;;;     file a permanent, unfixable false positive.
;;;   - GUILEMACS_M38_FIXTURE=crash raises an uncaught error while loading,
;;;     before any test registers.  This reproduces a real bug found in the
;;;     wild: test/m39/test-m39-imp5.el and test/m40/test-m40-imp0-audit.el
;;;     each read a docs/ file (milestone.org, docs/m40-plan.org) without
;;;     guarding its absence, so a checkout without those gitignored files
;;;     crashes the whole subprocess before ert-run-tests-batch-and-exit
;;;     ever runs -- no completion summary, no output from any other file
;;;     in the group, and (before this fix) a silent 0-passed/0-counted
;;;     "pass".  This MUST be flagged.
;;;
;;; Both modes report exactly one boolean via `boundp' to the .el wrapper's
;;; behavior-check hook: run-tests-loadup-emacs distinguishes them from the
;;; ERT completion banner's presence, not from TOT alone.
;;;
;;; This file is registered in its own group, outside the keyboard group,
;;; so the normal gate stays green.  The m38-imp1 corpus runs this fixture
;;; stressed (all modes) with GUILEMACS_M38_FIXTURE set.

(princ "=== m38 imp-1 count-mismatch fixture ===\n")

(require 'imp-ert-report)

(let* ((mode (or (getenv "GUILEMACS_M38_FIXTURE") ""))
       (mid-fail (or (string= mode "1") (string= mode "middle")))
       (last-fail (string= mode "last"))
       (empty (string= mode "empty"))
       (crash (string= mode "crash")))
  (cond
   (crash
    ;; Mirror the real bug: an uncaught error while loading, before any
    ;; test registers.  Nothing after this point in this file (or in any
    ;; later -l file, or the final --eval) runs.
    (insert-file-contents
     (expand-file-name "no-such-file-for-m38-imp1-fixture-crash-mode"
                        (file-name-directory (or load-file-name default-directory)))))
   (empty
    ;; Load cleanly; register nothing.  ERT still runs to completion.
    nil)
   (t
    ;; a/m/z order the cases so the failing test can be the middle one
    ;; (mid-fail) or the last one (last-fail); the others pass.  ERT runs
    ;; the tests in this definition order, so "last" puts the failure at
    ;; the last position.
    (let ((cases `(("m38-imp1-fixture/a" . t)
                   ("m38-imp1-fixture/m" . ,(not mid-fail))
                   ("m38-imp1-fixture/z" . ,(not last-fail)))))
      (dolist (case cases)
        (imp-register-bool-as-ert-test (car case) (cdr case)))))))
