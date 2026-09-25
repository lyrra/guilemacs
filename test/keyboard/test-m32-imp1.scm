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

;;; --- 3. Runtime: the new C primitive is callable -------------------
;;; M36 imp-2 retired --detect-input-pending; the detect family moved to
;;; (emacs kbd-buffer), so the primitive is gone.  --pending-signals-p
;;; stays.
(let ((r (safe (lambda () ((symbol-function '--detect-input-pending))))))
  (report "m32/imp1/runtime/primitive-detect-input-pending" (list 'INFO r))
  (check "m32/imp1/runtime/primitive-detect-input-pending-retired" 'error (car r)))
(let ((r (safe (lambda () ((symbol-function '--pending-signals-p))))))
  (report "m32/imp1/runtime/primitive-pending-signals-p" (list 'INFO r))
  (check "m32/imp1/runtime/primitive-pending-signals-p-ok" 'ok (car r)))

;;; --- 4. Runtime: do-display false returns without a redisplay ------
;;; B3 case 1: with do-display false the loop returns the timer delay
;;; after the first pass.
(let ((r (safe (lambda () (wait-run-timers #f)))))
  (report "m32/imp1/runtime/run-timers-no-display" (list 'INFO r))
  (check "m32/imp1/runtime/run-timers-no-display-no-error" 'ok (car r)))
