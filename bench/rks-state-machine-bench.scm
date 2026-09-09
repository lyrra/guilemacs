;;; rks-state-machine-bench.scm --- M28 imp-4 Step 4 bucket-B baseline
;;;
;;; Measures the full read-key-sequence state machine: for N synthetic
;;; ASCII keystrokes (enqueue ASCII 'x' via unread-command-events) it
;;; times one (read-key-sequence nil) call per iteration.  This is the
;;; path the three bucket-B file-statics serve (rks_t,
;;; rks_current_binding, rks_mock_input) — the before/after measurement
;;; point for a stay-C vs port decision.
;;;
;;; Sourced by bench/rks-state-machine-bench.el via eval-scheme; the
;;; summary is read back from `bench-summary' (Scheme format output
;;; does not reach emacs --batch stdout).  Same now-ns / srfi-19
;;; time-monotonic clock as bench/kbd-pipeline-bench.scm.

(use-modules (srfi srfi-19))

(define %sym symbol-function)

(define (now-ns)
  (let ((t (current-time time-monotonic)))
    (+ (* 1000000000 (time-second t)) (time-nanosecond t))))

(define N 100000)
(define WARMUP 2000)

;; Enqueue ASCII 'x' (120) on unread-command-events.  The brief keeps
;; this step *outside* the timed region: it is per-iteration setup that
;; read-key-sequence consumes, not part of the call being measured.
(define (enqueue-x!)
  (set-symbol-value! 'unread-command-events (list (char->integer #\x))))

;; Drive one full (read-key-sequence nil).  The subr Fread_key_sequence
;; (src/keyboard.c:9957) dispatches to read-key-sequence-vs-string, so
;; this is the whole state machine, the path the bucket-B statics serve.
(define (read-one!)
  ((%sym 'read-key-sequence) #nil))

;; Warm-up: prime caches / first-touch allocations.
(let loop ((i 0))
  (when (< i WARMUP)
    (enqueue-x!)
    (read-one!)
    (loop (+ i 1))))

;; Sanity: one non-timed read must return the string "x" (the
;; read-key-sequence subr returns a string for a plain ASCII key; the
;; bucket-B statics must actually be exercised, not swallowed/nil).
(enqueue-x!)
(define bench-sanity (read-one!))

;; Timed samples (nanoseconds per read).  Only the read-key-sequence
;; call is timed; the enqueue happens before t0.
(define samples (make-vector N 0))
(let loop ((i 0))
  (when (< i N)
    (enqueue-x!)
    (let ((t0 (now-ns)))
      (read-one!)
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
