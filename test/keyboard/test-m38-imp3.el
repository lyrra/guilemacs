;;; test-m38-imp3.el --- M38 imp-3 (input-state leak isolation) suite.
;;;
;;; Pins the M38 imp-3 work (brief.org, defect D3): the keyboard corpora
;;; run in one emacs process, so an input-state name one corpus writes
;;; leaks into every corpus that follows.  imp-3 makes each writer clear
;;; its state back to the C/Scheme default, makes the two no-reset
;;; victims measure their own effect, and disposes the doc-anchor
;;; failure.  No C file changes.
;;;
;;; Source checks only (test/keyboard/test-m38-imp3.scm).  Prove the
;;; writer map, the shared helper (test-m38-imp3-reset.el), the Pattern B
;;; victims, the kbd_buffer drain, the doc-anchor skip, the unchanged
;;; victims and the unchanged C surface.
;;;
;;; This file used to also run a *behavior* check: shell out to
;;; tool/run-tests.sh --filter=keyboard via call-process TWICE (a
;;; recursion guard, GUILEMACS_M38_IMP3_GATE, kept the nested run from
;;; spawning another pair), to prove two full keyboard-suite runs both
;;; exit 0 and produce the same FAIL set.  --filter=keyboard matches
;;; nearly every file in the keyboard group, so this meant every batch
;;; that includes this file re-ran almost the entire suite as a
;;; subprocess, twice, on top of whatever batch was already running it --
;;; slow enough (tens of minutes) to be mistaken for a genuine hang.
;;; Removed; the corpus's "two-run" checks (§10 below) now always report
;;; INFO-skipped instead of exercising a live two-run.  Run
;;; ./tool/run-tests.sh --filter=keyboard by hand (twice, diff the FAIL
;;; sets) if this needs re-proving.
;;;
;;; The .scm corpus is loaded via primitive-load with the repo root bound
;;; as %m38-root.  Each (NAME PASS|FAIL) pair is reported via princ AND
;;; turned into an ERT test so the harness counts it.  Each (NAME INFO
;;; VALUE) pair is printed as an INFO line and is NOT asserted.  A corpus
;;; load error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).

(princ "=== m38 imp-3 (input-state leak isolation) test suite ===\n")

(require 'imp-ert-report)

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (root (expand-file-name "../.." dir))
       (corpus (expand-file-name "test-m38-imp3.scm" dir))
       (load-error nil))
  (eval-scheme (format "(define %%m38-root %S)" root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m38-imp3/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m38-imp3/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m38-imp3/readback"
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
