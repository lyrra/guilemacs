;;; kbd-pipeline-profile.el --- M28 imp-2 profile driver
;;;
;;; Loads bench/kbd-pipeline-profile.scm via eval-scheme and prints the
;;; statprof flat profile.  Scheme output does not reach emacs --batch
;;; stdout, so the .scm builds `profile-report' and this driver prints
;;; it.  Run with:
;;;   ./src/emacs --batch --load bench/kbd-pipeline-profile.el
;;;
;;; Self-check: profile-sanity must be 0 (ASCII keystroke flowing
;;; through the pipeline) and the sample count must be non-zero
;;; (statprof actually sampled).  Either failure signals an error and a
;;; non-zero exit, like the sanity line in kbd-pipeline-bench.el.

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "kbd-pipeline-profile.scm" dir)))
  (eval-scheme (format "(primitive-load %S)" corpus))
  (let ((sanity (eval-scheme "profile-sanity"))
        (sample-count (eval-scheme "profile-sample-count"))
        (report (eval-scheme "profile-report")))
    (princ (format "sanity=%S N=%d samples=%d\n"
                   sanity 100000 sample-count))
    (unless (eq sanity 0)
      (princ (format "PROFILE-FAIL: sanity=%S, event not flowing\n" sanity))
      (kill-emacs 1))
    (unless (and (integerp sample-count) (> sample-count 0))
      (princ "PROFILE-FAIL: no samples recorded\n")
      (kill-emacs 1))
    (princ report)))
