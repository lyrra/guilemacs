;;; test-m38-imp4.el --- M38 imp-4 (close-out) suite.
;;;
;;; Pins the M38 imp-4 close-out (brief.org §8).  M38 is the test-harness
;;; integrity step: it ports no C code and changes no input asset.  imp-4
;;; re-measures the surface, re-confirms the keyboard gate, and records
;;; the accounting.  No C file changes.
;;;
;;; Source checks only (test/keyboard/test-m38-imp4.scm).  Prove the
;;; surface table (brief.org §6) and the accounting in the working
;;; documents (brief.org §8.2).
;;;
;;; This file used to also run a *behavior* check: shell out to
;;; tool/run-tests.sh --filter=keyboard via call-process TWICE (a
;;; recursion guard, GUILEMACS_M38_IMP4_GATE, kept the nested run from
;;; spawning another pair), to prove two full keyboard-suite runs both
;;; exit 0.  --filter=keyboard matches nearly every file in the keyboard
;;; group, so this meant every batch that includes this file re-ran
;;; almost the entire suite as a subprocess, twice, on top of whatever
;;; batch was already running it -- slow enough (tens of minutes) to be
;;; mistaken for a genuine hang.  Removed; the corpus's "two-run" checks
;;; (see test-m38-imp4.scm) now always report INFO-skipped instead of
;;; exercising a live two-run.  Run ./tool/run-tests.sh --filter=keyboard
;;; by hand (twice) if this needs re-proving.
;;;
;;; The .scm corpus is loaded via primitive-load with the repo root bound
;;; as %m38-root.  Each (NAME PASS|FAIL) pair is reported via princ AND
;;; turned into an ERT test so the harness counts it.  Each (NAME INFO
;;; VALUE) pair is printed as an INFO line and is NOT asserted.  A corpus
;;; load error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).

(princ "=== m38 imp-4 (close-out) test suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m38-imp4.scm" dir))
       (load-error nil))
  (eval-scheme (format "(define %%m38-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m38-imp4/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m38-imp4/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m38-imp4/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test name status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test name status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))
    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
