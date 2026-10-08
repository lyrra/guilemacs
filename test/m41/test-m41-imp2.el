;;; test-m41-imp2.el --- M41 imp-2 (src/xdisp.c decision predicates) suite.
;;;
;;; Pins the M41 imp-2 port (brief.org): the long-line-optimizations-p
;;; and invisible-p decisions move to (emacs xdisp).  Each DEFUN keeps
;;; its name and gets a static C dispatcher; C computes the buffer
;;; field, the property lookup, and TEXT_PROP_MEANS_INVISIBLE.  No C
;;; fallback.
;;;
;;; Wraps test/m41/test-m41-imp2.scm -- the Scheme corpus.  Binds the
;;; repo root as %m41-root, loads the Scheme file via eval-scheme, then
;;; reads back `test-results' (list of (NAME STATUS) pairs).  Each
;;; (NAME PASS|FAIL) pair is reported via princ AND turned into an ERT
;;; test so the harness counts it.  Each (NAME INFO VALUE) pair is
;;; printed as an INFO line and is NOT asserted.  A corpus load error, a
;;; readback error or an empty corpus is reported as a real FAIL (never
;;; a silent 0 failed).
;;;
;;; It adds the tree-wide scm_c_public_ref pin that needs a directory
;;; scan, plus the cross-file numbers.

(princ "=== m41 imp-2 (src/xdisp.c decision predicates) test suite ===\n")

(require 'imp-ert-report)

(defvar m41-imp2--root
  (file-name-as-directory
   (expand-file-name "../.." (file-name-directory (or load-file-name
                                                       default-directory)))))

(defun m41-imp2--count (rel regexp)
  "Count the matches of REGEXP in REL (repo-root-relative)."
  (with-temp-buffer
    (insert-file-contents (expand-file-name rel m41-imp2--root))
    (goto-char (point-min))
    (let ((n 0))
      (while (re-search-forward regexp nil t) (setq n (1+ n)))
      n)))

(defun m41-imp2--check (name ok)
  "Report and register one check.  OK is a boolean."
  (princ (format "%s m41/imp2/%s\n" (if ok "PASS" "FAIL") name))
  (imp-register-bool-as-ert-test (format "m41-imp2/%s" name) ok))

(defun m41-imp2--tree-wide-scm-public-ref ()
  "Count scm_c_public_ref over src/*.c and src/*.h."
  (let ((n 0))
    (dolist (f (directory-files (expand-file-name "src" m41-imp2--root)
                                t "\\.[ch]\\'"))
      (with-temp-buffer
        (insert-file-contents f)
        (goto-char (point-min))
        (while (search-forward "scm_c_public_ref" nil t) (setq n (1+ n)))))
    n))

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m41-imp2.scm" dir))
       (load-error nil))
  ;; The corpus reads the build tree, so tell it where the root is.
  (eval-scheme (format "(define %%m41-root %S)" m41-imp2--root))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (setq load-error err)))
  (let* ((results
          (cond
           (load-error
            (list (list "m41-imp2/corpus-load"
                        (cons 'FAIL (format "%S" load-error)))))
           (t
            (condition-case e
                (let ((r (eval-scheme "(reverse test-results)")))
                  (if (or (not (listp r)) (null r))
                      (list (list "m41-imp2/corpus-empty"
                                  (cons 'FAIL "corpus produced no results")))
                    r))
              (error
               (list (list "m41-imp2/readback"
                           (cons 'FAIL (format "%S" e)))))))))
         (pass 0)
         (fail 0))
    (dolist (result results)
      (let* ((name (car result))
             (status (cadr result))
             (ok (eq status 'PASS)))
        (cond
         (ok
          (imp-register-check-as-ert-test (format "m41-imp2/%s" name) status)
          (setq pass (1+ pass))
          (princ (format "PASS %s\n" name)))
         ((and (consp status) (eq (car status) 'INFO))
          (princ (format "INFO %s %s\n" name (cadr status))))
         (t
          (imp-register-check-as-ert-test (format "m41-imp2/%s" name) status)
          (setq fail (1+ fail))
          (princ (format "FAIL %s %S\n" name (cdr result)))))))

    ;; --- Cross-file number: the tree-wide scm_c_public_ref re-pin ----
    ;; The imp-2 and imp-3 sites move the count 172 -> 177.
    (m41-imp2--check "tree-wide-scm-public-ref-235"
                     (eql 235 (m41-imp2--tree-wide-scm-public-ref)))

    ;; --- End-to-end: the live DEFUN through the C boundary (cr.org F6) -
    ;; The .scm corpus checks the module return only.  These calls reach
    ;; the C DEFUN `invisible-p' live, so the C -> module path runs for
    ;; real: the C computes prop and TEXT_PROP_MEANS_INVISIBLE, the
    ;; module maps the code to the elisp value.  Each call uses a fresh
    ;; temp buffer, so no state leaks between checks.
    (let ((e2e (lambda (name thunk)
                 (m41-imp2--check name
                                  (condition-case nil (funcall thunk)
                                    (error nil))))))
      ;; invis == 1 -> t: the invisible prop is set and the spec is t.
      (funcall e2e "e2e/invisible-p/means-invisible-t"
               (lambda ()
                 (with-temp-buffer
                   (insert "abc")
                   (put-text-property 1 2 'invisible t)
                   (let ((buffer-invisibility-spec t))
                     (eq (invisible-p 1) t)))))
      ;; invis == 0 -> nil: no invisible prop on the character.
      (funcall e2e "e2e/invisible-p/no-prop-nil"
               (lambda ()
                 (with-temp-buffer
                   (insert "abc")
                   (let ((buffer-invisibility-spec t))
                     (eq (invisible-p 2) nil)))))
      ;; invis == 2 -> the fixnum 2 (ellipsis): the spec element has a
      ;; non-nil cdr, so TEXT_PROP_MEANS_INVISIBLE returns 2 and the
      ;; module returns the integer, which reads back as an elisp fixnum.
      (funcall e2e "e2e/invisible-p/ellipsis-fixnum"
               (lambda ()
                 (with-temp-buffer
                   (insert "abc")
                   (put-text-property 1 2 'invisible 'invisible)
                   (let ((buffer-invisibility-spec '((invisible . t))))
                     (eql (invisible-p 1) 2))))))

    (princ (format "=== %d passed, %d failed, %d total ===\n"
                   pass fail (+ pass fail)))))
