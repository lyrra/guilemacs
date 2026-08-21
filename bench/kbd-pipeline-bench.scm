;;; kbd-pipeline-bench.scm --- M11 pre-imp-5 latency baseline
;;;
;;; Measures the kbd_buffer_get_event pipeline: for N synthetic ASCII
;;; keystroke events, store one via --kbd-buffer-store-fake-event and
;;; time the read via the (emacs main-queue)
;;; read-decoded-event-from-main-queue Scheme port (M12 imp-3), which
;;; calls kbd-buffer-get-event directly.  Before imp-4 the timed entry
;;; was the --rc-read-decoded-event-from-main-queue C seam; the rewire
;;; (M12 imp-5, landed with imp-4) makes the Scheme port the thinnest
;;; wrapper, so this same script is the before/after measurement
;;; point.  The store is outside the timed region (it is unchanged).
;;;
;;; Sourced by bench/kbd-pipeline-bench.el via eval-scheme; the
;;; summary is read back from `bench-summary' (Scheme format output
;;; does not reach emacs --batch stdout).

(use-modules (srfi srfi-19))
(use-modules (emacs main-queue))

(define %sym symbol-function)

(define (now-ns)
  (let ((t (current-time time-monotonic)))
    (+ (* 1000000000 (time-second t)) (time-nanosecond t))))

(define N 100000)
(define WARMUP 2000)

(define (store-fake!)
  ((%sym '--kbd-buffer-store-fake-event) 1 #nil))   ; ASCII_KEYSTROKE_EVENT

;; Untimed (end-time #nil); tag/prev-event are inert for the bench.
(define (read-event)
  (read-decoded-event-from-main-queue #nil 'bench-tag #nil))

;; Warm-up: prime caches / first-touch allocations.
(let loop ((i 0))
  (when (< i WARMUP)
    (store-fake!)
    (read-event)
    (loop (+ i 1))))

;; Sanity: one non-timed read must return the char code 0 (ASCII
;; keystroke, code/modifiers zeroed) — proves the synthetic event is
;; actually going through the pipeline, not being swallowed/nil.
(store-fake!)
(define bench-sanity (read-event))

;; Timed samples (nanoseconds per read).
(define samples (make-vector N 0))
(let loop ((i 0))
  (when (< i N)
    (store-fake!)
    (let ((t0 (now-ns)))
      (read-event)
      (vector-set! samples i (- (now-ns) t0)))
    (loop (+ i 1))))

(define sorted-ns (sort (vector->list samples) <))

(define bench-total-ns
  (let sum ((l sorted-ns) (acc 0))
    (if (null? l) acc (sum (cdr l) (+ acc (car l))))))

(define (percentile lst p)
  ;; p in [0,1); nearest-rank index of the p-th quantile.
  (list-ref lst (min (- (length lst) 1)
                     (inexact->exact (floor (* p (length lst)))))))

(define bench-median-ns
  (quotient (+ (list-ref sorted-ns (quotient N 2))
               (list-ref sorted-ns (- (quotient N 2) 1)))
            2))
(define bench-p99-ns (percentile sorted-ns 0.99))
(define bench-mean-ns (quotient bench-total-ns N))

;; (N median-ns p99-ns mean-ns total-ns) — all fixnums.
(define bench-summary
  (list N bench-median-ns bench-p99-ns bench-mean-ns bench-total-ns))
