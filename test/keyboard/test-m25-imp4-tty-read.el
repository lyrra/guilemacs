;;; test-m25-imp4-tty-read.el --- M25 imp-4 (emacs gobble) test suite.
;;;
;;; Covers the M25 imp-4 cutover (brief.org M25): the TTY read path body
;;; of tty_read_avail_input moved out of src/keyboard.c into (emacs
;;; gobble) as tty-read-avail-input!.  tty_read_avail_input is now a thin
;;; dispatcher guarded by four raw-pointer checks and the GPM drain in C.
;;;
;;; Wraps test/keyboard/test-m25-imp4-tty-read.scm -- the Scheme test
;;; corpus.  Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each via
;;; princ.  Same harness as test-m25-imp3-gobble-input.el.  See
;;; brief.org M25 imp-4.

(princ "=== m25-imp4-tty-read test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root and from the harness, which loads
;; this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m25-imp4-tty-read.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M25TR-CORPUS-LOAD-ERROR: %S\n" err)))))

;; Read each result back and report PASS/FAIL.
(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M25TR-READBACK-ERROR: %S\n" e)) '())))
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
