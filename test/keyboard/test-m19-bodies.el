;;; test-m19-bodies.el --- M19 imp-1 test suite for the Scheme mlp_*
;;; geometry-body ports
;;;
;;; Wraps test/keyboard/test-m19-bodies.scm — the Scheme test corpus
;;; for the (emacs lispy-position) procedures, native Scheme ports of
;;; the C mlp_* bodies in src/keyboard.c (mlp_image_hotspot_check,
;;; mlp_mode_header_line, mlp_scroll_border, mlp_fringes,
;;; mlp_buffer_posn_pass, mlp_margins, mlp_internal_border,
;;; mlp_frame_preamble).  See docs/m19-plan.org §imp-1 and brief.org.
;;;
;;; Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each via
;;; princ.  Each check in the corpus compares the Scheme port's output
;;; against the pre-cutover C --mlp-dispatch path for the same
;;; window/frame state and part, so the exit condition is byte-for-byte
;;; agreement, not just "does not crash".

(princ "=== m19-bodies test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root (run-all-tests.el) and from the
;; harness, which loads this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m19-bodies.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M19B-CORPUS-LOAD-ERROR: %S\n" err)))))

;; Read each result back and report PASS/FAIL.
(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M19B-READBACK-ERROR: %S\n" e)) '())))
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
