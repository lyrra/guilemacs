;;; test-m32-imp1.scm --- M32 imp-1: the process.c wait decision path.
;;;
;;; brief.org (M32 imp-1) ports the decision logic of the live
;;; wait_reading_process_output (src/process.c, the copy at :5329) into
;;; the new module (emacs process-wait).  The system call stays C.
;;; See docs/m32-plan.org A3.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - a runtime check: the module loads, exports the two procedures,
;;;     and wait-signal-drain on the read_kbd >= 0 branch (the
;;;     "no keyboard" boundary, brief.org B3 case 5) and wait-run-timers
;;;     with do-display false (B3 case 1) run without error.  The
;;;     sandbox cannot relink src/emacs, so the two new C primitives
;;;     (--pending-signals-p, --detect-input-pending) are absent from
;;;     the running binary; every runtime call that would touch them is
;;;     guarded and reported as INFO, not asserted.
;;;   - a static wiring check: the C region no longer holds the old
;;;     decision code, src/process.c calls the two dispatchers, the
;;;     three extern-API stubs stay, and the module is boot-loaded.
;;;
;;; The repo root is bound by the .el wrapper as %m32-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m32-imp1.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (slurp path)
  "Return the whole file at PATH as a string, or #f when it is absent."
  (if (not (file-exists? path))
      #f
      (call-with-input-file path
        (lambda (port)
          (let loop ((chars '()))
            (let ((c (read-char port)))
              (if (eof-object? c)
                  (list->string (reverse chars))
                  (loop (cons c chars)))))))))

(define (contains? text needle)
  ;; string-contains returns the match index or #f; normalize to a boolean
  ;; so `check' can compare against #t/#f.
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (repo path) (string-append %m32-root "/" path))

(define (count-occurrences text needle)
  "Count the non-overlapping occurrences of NEEDLE in TEXT."
  (if (not (string? text))
      0
      (let ((nlen (string-length needle)))
        (let loop ((start 0) (n 0))
          (let ((idx (string-contains text needle start)))
            (if (not idx)
                n
                (loop (+ idx nlen) (+ n 1))))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m32-root))
    (begin (report "m32-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m32-root "."))
    (report "m32-root-bound" 'PASS))

;;; --- 1. The module loads and exports the two procedures ------------
(use-modules (emacs process-wait))

(check "m32/imp1/export/wait-signal-drain" #t
       (let ((p (module-ref (resolve-module '(emacs process-wait)) 'wait-signal-drain)))
         (procedure? p)))
(check "m32/imp1/export/wait-run-timers" #t
       (let ((p (module-ref (resolve-module '(emacs process-wait)) 'wait-run-timers)))
         (procedure? p)))

;;; --- 2. Runtime: the signal-drain arms (B3 case 5) ------------------
;;; read_kbd >= 0 takes the maybe_quit branch; read_kbd < 0 takes the
;;; pending-signals branch (reads the new --pending-signals-p).  Both
;;; return nil.
(define (safe thunk)
  (catch #t
    (lambda () (cons 'ok (thunk)))
    (lambda (key . args) (cons 'error (cons key args)))))

(let ((r (safe (lambda () (wait-signal-drain 0)))))
  (check "m32/imp1/runtime/signal-drain-read-kbd-0" '(ok . #nil) r))
(let ((r (safe (lambda () (wait-signal-drain 1)))))
  (check "m32/imp1/runtime/signal-drain-read-kbd-1" '(ok . #nil) r))
(let ((r (safe (lambda () (wait-signal-drain -1)))))
  (check "m32/imp1/runtime/signal-drain-read-kbd-neg1" '(ok . #nil) r))

;;; --- 3. Runtime: the two new C primitives are callable -------------
;;; The build relinked src/emacs in this session, so the primitives the
;;; module needs exist; prove it instead of only scanning the source.
(let ((r (safe (lambda () ((symbol-function '--detect-input-pending))))))
  (report "m32/imp1/runtime/primitive-detect-input-pending" (list 'INFO r))
  (check "m32/imp1/runtime/primitive-detect-input-pending-ok" 'ok (car r)))
(let ((r (safe (lambda () ((symbol-function '--pending-signals-p))))))
  (report "m32/imp1/runtime/primitive-pending-signals-p" (list 'INFO r))
  (check "m32/imp1/runtime/primitive-pending-signals-p-ok" 'ok (car r)))

;;; --- 4. Runtime: do-display false returns without a redisplay ------
;;; B3 case 1: with do-display false the loop returns the timer delay
;;; after the first pass.
(let ((r (safe (lambda () (wait-run-timers #f)))))
  (report "m32/imp1/runtime/run-timers-no-display" (list 'INFO r))
  (check "m32/imp1/runtime/run-timers-no-display-no-error" 'ok (car r)))

;;; --- 5. Static: the module source shapes the three decision arms ---
(define pw (slurp (repo "mod/emacs/process-wait.scm")))
(if (not pw)
    (report "m32/imp1/scan/module" (cons 'FAIL "mod/emacs/process-wait.scm missing"))
    (begin
      ;; B3 case 3: one signal-drain choice per call -- maybe_quit on
      ;; read_kbd >= 0, else pending-signals -> process-pending-signals!.
      (check "m32/imp1/module/maybe-quit-arm" #t (contains? pw "%--maybe-quit"))
      (check "m32/imp1/module/pending-signals-arm" #t (contains? pw "%--pending-signals-p"))
      (check "m32/imp1/module/process-pending-signals-arm" #t
             (contains? pw "%process-pending-signals!"))
      ;; B3 case 2: each timer pass calls timer-check.
      (check "m32/imp1/module/timer-check" #t (contains? pw "%timer-check"))
      ;; B3 case 4: the wait-again test reads detect-input-pending.
      (check "m32/imp1/module/detect-input-pending" #t
             (contains? pw "%--detect-input-pending"))
      ;; Both exported names are defined and exported.
      (check "m32/imp1/module/export-names" #t
             (and (contains? pw "wait-signal-drain")
                  (contains? pw "wait-run-timers")))))

;;; --- 5. Static: src/process.c calls the dispatchers, old code is gone
(define proc-c (slurp (repo "src/process.c")))
(if (not proc-c)
    (report "m32/imp1/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      (check "m32/imp1/process.c/calls-wait-signal-drain" #t
             (contains? proc-c "wait_signal_drain (read_kbd)"))
      (check "m32/imp1/process.c/calls-wait-run-timers" #t
             (contains? proc-c "timer_delay = wait_run_timers (do_display)"))
      ;; The old inline decision code is gone from the live copy.
      (check "m32/imp1/process.c/no-old-signal-drain" #f
             (contains? proc-c "else if (pending_signals)"))
      ;; M36 imp-1 deleted the dead MS-DOS copy and retired timer_check,
      ;; so no `timer_delay = timer_check ()' remains anywhere.
      (check "m32/imp1/process.c/no-timer-check-call" 0
             (count-occurrences proc-c "timer_delay = timer_check ()"))
      ;; The two thin dispatchers are defined local to process.c, so
      ;; keyboard.c does not grow for them.
      (check "m32/imp1/process.c/defines-wait-signal-drain" #t
             (contains? proc-c "wait_signal_drain (int read_kbd)"))
      (check "m32/imp1/process.c/defines-wait-run-timers" #t
             (contains? proc-c "wait_run_timers (bool do_display)"))
      (check "m32/imp1/process.c/includes-guile.h" #t
             (contains? proc-c "#include \"guile.h\""))))

;;; --- 6. Static: the three extern-API stubs stay in src/keyboard.c --
;;; Plus the two new primitives the module reads.  The stub family must
;;; survive while a later caller stays C (brief.org B2).
(define kbd-c (slurp (repo "src/keyboard.c")))
(if (not kbd-c)
    (report "m32/imp1/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m32/imp1/keyboard.c/stub-detect-input-pending" #t
             (contains? kbd-c "detect_input_pending (void)"))
      ;; M36 imp-1 retired the stub.
      (check "m32/imp1/keyboard.c/timer-check-retired" #f
             (contains? kbd-c "timer_check (void)"))
      (check "m32/imp1/keyboard.c/stub-process-pending-signals" #t
             (contains? kbd-c "process_pending_signals (void)"))
      ;; The two new primitives exist.
      (check "m32/imp1/keyboard.c/primitive-pending-signals-p" #t
             (contains? kbd-c "\"--pending-signals-p\""))
      (check "m32/imp1/keyboard.c/primitive-detect-input-pending" #t
             (contains? kbd-c "\"--detect-input-pending\""))))

;;; --- 7. Static: boot load ------------------------------------------
(define load-scm (slurp (repo "prelude/load.scm")))
(check "m32/imp1/load.scm/registers-module" #t
       (contains? load-scm "(emacs process-wait)"))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m32/imp1/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m32-imp1.el"))
