;;; test-m41-imp1.el --- M41 imp-1 (src/xdisp.c audit) suite.
;;;
;;; Pins the M41 imp-1 audit (brief.org).  imp-1 adds no C: it
;;; classifies the 24 src/xdisp.c DEFUNs, maps the live C callers, and
;;; confirms the target src/xdisp.c.
;;;
;;; Wraps test/m41/test-m41-imp1.scm -- the Scheme audit corpus.
;;; Binds the repo root as %m41-root, loads the Scheme file via
;;; eval-scheme, then reads back `test-results' (list of (NAME STATUS)
;;; pairs).  Each (NAME PASS|FAIL) pair is reported via princ AND turned
;;; into an ERT test so the harness counts it.  Each (NAME INFO VALUE)
;;; pair is printed as an INFO line and is NOT asserted.  A corpus load
;;; error, a readback error or an empty corpus is reported as a real
;;; FAIL (never a silent 0 failed).
;;;
;;; It adds the base-number pins that need a directory scan (the
;;; tree-wide scm_c_public_ref count) and the cross-file numbers, plus
;;; a guarded check on the gitignored docs/m41-plan.org.

(princ "=== m41 imp-1 (src/xdisp.c audit) test suite ===\n")

(require 'imp-ert-report)

(defvar m41-imp1--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m41-imp1--lines (rel)
  "Count the lines of REL (repo-root-relative) the way `wc -l' does."
  (with-temp-buffer
    (insert-file-contents (expand-file-name rel m41-imp1--root))
    (goto-char (point-min))
    (let ((n 0))
      (while (search-forward "\n" nil t) (setq n (1+ n)))
      n)))

(defun m41-imp1--count (rel regexp)
  "Count the matches of REGEXP in REL (repo-root-relative)."
  (with-temp-buffer
    (insert-file-contents (expand-file-name rel m41-imp1--root))
    (goto-char (point-min))
    (let ((n 0))
      (while (re-search-forward regexp nil t) (setq n (1+ n)))
      n)))

(defun m41-imp1--check (name ok)
  "Report and register one check.  OK is a boolean."
  (princ (format "%s m41/imp1/%s\n" (if ok "PASS" "FAIL") name))
  (imp-register-bool-as-ert-test (format "m41-imp1/%s" name) ok))

(defun m41-imp1--tree-wide-scm-public-ref ()
  "Count scm_c_public_ref over src/*.c and src/*.h."
  (let ((n 0))
    (dolist (f (directory-files (expand-file-name "src" m41-imp1--root)
                                t "\\.[ch]\\'"))
      (with-temp-buffer
        (insert-file-contents f)
        (goto-char (point-min))
        (while (search-forward "scm_c_public_ref" nil t) (setq n (1+ n)))))
    n))

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m41-imp1.scm" dir))
       (load-error nil))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m41-root %S)" m41-imp1--root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m41-imp1/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m41-imp1/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m41-imp1/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m41-imp1/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m41-imp1/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))

    ;; --- Basline cross-file numbers (brief.org §7) -------------------
    (m41-imp1--check "process.c-lines-9030"
                     (eql 9030 (m41-imp1--lines "src/process.c")))
    (m41-imp1--check "process.c-defuns-50"
                     (eql 50 (m41-imp1--count "src/process.c" "^DEFUN (\"")))
    (m41-imp1--check "keyboard.c-lines-11233"
                     ;; M43 imp-2 added the --tty-fd accessor: 11,221 -> 11,233.
                     (eql 11233 (m41-imp1--lines "src/keyboard.c")))
    (m41-imp1--check "keyboard-globals.c-lines-490"
                     (eql 490 (m41-imp1--lines "src/keyboard-globals.c")))
    (m41-imp1--check "tree-wide-scm-public-ref-258"
                     (eql 258 (m41-imp1--tree-wide-scm-public-ref)))

    ;; --- The gitignored plan (guarded: skip when absent) ------------
    (if (not (file-exists-p (expand-file-name "docs/m41-plan.org"
                                              m41-imp1--root)))
        (princ "INFO m41/imp1/plan-checks skipped (docs/m41-plan.org absent, untracked)\n")
      (m41-imp1--check "plan-target-xdisp.c"
                       (with-temp-buffer
                         (insert-file-contents
                          (expand-file-name "docs/m41-plan.org"
                                            m41-imp1--root))
                         (goto-char (point-min))
                         (and (search-forward "#+target: src/xdisp.c" nil t) t)))
      (m41-imp1--check "plan-records-keep-option-a"
                       (with-temp-buffer
                         (insert-file-contents
                          (expand-file-name "docs/m41-plan.org"
                                            m41-imp1--root))
                         (goto-char (point-min))
                         (and (search-forward "Choice: keep =src/xdisp.c="
                                              nil t)
                              t))))

    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
