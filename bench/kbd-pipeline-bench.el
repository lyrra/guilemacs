;;; kbd-pipeline-bench.el --- M11 pre-imp-5 latency baseline driver
;;;
;;; Loads bench/kbd-pipeline-bench.scm via eval-scheme and prints the
;;; latency summary.  Run with:
;;;   ./src/emacs --batch --load bench/kbd-pipeline-bench.el

(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "kbd-pipeline-bench.scm" dir)))
  (eval-scheme (format "(primitive-load %S)" corpus))
  (let ((s (eval-scheme "bench-summary"))
        (sanity (eval-scheme "bench-sanity")))
    (princ (format "sanity=%S N=%d median=%.1f us p99=%.1f us mean=%.1f us total=%.3f s\n"
                   sanity
                   (nth 0 s)
                   (/ (float (nth 1 s)) 1000.0)
                   (/ (float (nth 2 s)) 1000.0)
                   (/ (float (nth 3 s)) 1000.0)
                   (/ (float (nth 4 s)) 1e9)))))
