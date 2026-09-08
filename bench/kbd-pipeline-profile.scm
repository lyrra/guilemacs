;;; kbd-pipeline-profile.scm --- M28 imp-2 store→read→dispatch profiler
;;;
;;; Profiles the all-Scheme read pipeline (docs/m28-plan.org §imp-2,
;;; brief.org M28 imp-2) under (statprof).  Same driver as
;;; bench/kbd-pipeline-bench.scm: for N synthetic ASCII keystrokes,
;;; store one via --kbd-buffer-store-fake-event and read it through the
;;; (emacs main-queue) read-decoded-event-from-main-queue Scheme port.
;;; The store is included because brief.org imp-2's baseline is the
;;; whole store→read→dispatch path.
;;;
;;; statprof is a SIGPROF sampler: it attributes VM time to the Scheme
;;; procedure that owns each sampled frame.  C DEFUN bodies are not VM
;;; frames, so time spent inside a C shim is charged to the Scheme
;;; wrapper that called it (brief.org Traps).  Attribute C-side time by
;;; the wrapper name (read-event-from-main-queue /
;;; read-decoded-event-from-main-queue / kbd-buffer-get-event and the
;;; per-event shim wrappers like --selected-frame-tty-p).
;;;
;;; Sourced by bench/kbd-pipeline-profile.el via eval-scheme.  Scheme
;;; output does not reach emacs --batch stdout, so the report is built
;;; into the `profile-report' string and printed by the .el driver.
;;;
;;; Expected output: profile-sanity = 0 (ASCII keystroke), a positive
;;; profile-sample-count, and a flat table of self seconds and %time by
;;; procedure.  The merged <C> row's cum-sec is meaningless (anonymous C
;;; frames double-count on merge) and prints '-'.  A trailing line states
;;; the sample-count resolution (1 sample = 100/count % of self time);
;;; rows at or below that share are noise.  A non-0 sanity means the
;;; synthetic event does not flow through the pipeline.

(use-modules (statprof))
(use-modules (srfi srfi-19))

(use-modules (emacs main-queue))

(define %sym symbol-function)

(define (store-fake!)
  ((%sym '--kbd-buffer-store-fake-event) 1 #nil))   ; ASCII_KEYSTROKE_EVENT

;; Untimed (end-time #nil); tag/prev-event are inert for the bench.
(define (read-event)
  (read-decoded-event-from-main-queue #nil 'bench-tag #nil))

(define N 100000)
(define WARMUP 2000)

;; Warm-up: prime caches / first-touch allocations before profiling.
(let loop ((i 0))
  (when (< i WARMUP)
    (store-fake!)
    (read-event)
    (loop (+ i 1))))

;; Sanity: one non-timed read must return the char code 0 (ASCII
;; keystroke) — proves the event goes through the pipeline.
(store-fake!)
(define profile-sanity (read-event))

;; Profile the timed region.  1 ms sampling (exact-integer
;; microseconds).  Call counting is left OFF: instrumenting every call
;; (~5M defelisp `force' derefs per run) inflates wall time ~12× and
;; adds its own frames, distorting the attribution.  Flat-report self/
;; cumulative % come from pure SIGPROF sampling (statprof conventions).
(statprof-reset 0 1000 #f)
(statprof-start)
(let loop ((i 0))
  (when (< i N)
    (store-fake!)
    (read-event)
    (loop (+ i 1))))
(statprof-stop)

(define profile-accumulated-secs (statprof-accumulated-time))
(define profile-sample-count  (statprof-sample-count))

;; Flat report (statprof flat-profile conventions): each sampled frame's
;; own procedure gets %time (self seconds / total), cumulative seconds
;; (itself + callees, from full-stack sampling), and self seconds.
;; Cumulative minus self = child time.  Call counting is off, so there
;; is no calls column (brief.org lists "calls" only when measured).
(define profile-report
  (if (zero? profile-sample-count)
      "No samples recorded.\n"
      (let* ((all-samples (statprof-sample-count))
             (total-secs (statprof-accumulated-time))
             (secs-per-sample (/ total-secs all-samples))
             (rows
              ;; Fold call-data into (name self-secs cum-secs) rows,
              ;; merging closures that share a name.  A frame with no
              ;; program name is a C call (shim body / primitive); label
              ;; it <C> so C-side time is visible instead of dropped.
              (statprof-fold-call-data
               (lambda (data prior)
                 (let* ((self (* (statprof-call-data-self-samples data)
                                 secs-per-sample))
                        (cum  (* (statprof-call-data-cum-samples data)
                                 secs-per-sample))
                        (name (or (statprof-call-data-name data) "<C>"))
                        (entry (assoc name prior)))
                   (if entry
                       (begin
                         (set-cdr! entry
                                   (list (+ (cadr entry) self)
                                         (+ (caddr entry) cum)))
                         prior)
                       (cons (list name self cum) prior))))
               '()))
             (sorted (sort rows
                           (lambda (a b)
                             (> (cadr a) (cadr b)))))
             (sbuf (open-output-string)))
        (format sbuf "  %time  cum-sec  self-sec  procedure\n")
        (for-each
         (lambda (row)
           (let ((name (car row)) (self (cadr row)) (cum (caddr row)))
             ;; The merged <C> row aggregates many anonymous C frames, so
             ;; its cum count double-counts on merge and is meaningless
             ;; (see docs/m28-plan.org §imp-2).  Print '-' for it; only
             ;; named rows have a trustworthy cum-sec.  self-sec/%time
             ;; are valid for every row.
             (format sbuf "~6,2f ~8a ~8,2f  ~a\n"
                     (* 100.0 (/ self total-secs))
                     (if (equal? name "<C>") "-" (number->string cum))
                     self name)))
         sorted)
        (format sbuf "---\nSample count: ~A\nTotal time: ~A seconds\n"
                all-samples total-secs)
        (format sbuf
                "Sample resolution: 1 sample = ~4,2f% of self time; rows at or below that share are noise.\n"
                (/ 100.0 all-samples))
        (get-output-string sbuf))))
