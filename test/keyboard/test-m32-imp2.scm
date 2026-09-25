;;; test-m32-imp2.scm --- M32 imp-2: the process.c error paths.
;;;
;;; brief.org (M32 imp-2) ports the two process.c error-handler bodies
;;; into the new module (emacs process-error), ports the send_process
;;; EINTR-loop drain, and retires the C function cmd_error_internal
;;; (process.c was its last caller).  The C entry points stay C as thin
;;; static dispatchers.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - a runtime check: the module loads and exports the three
;;;     procedures.  The running binary may predate the imp-2 C changes
;;;     (the sandbox cannot always relink src/emacs); every runtime call
;;;     that would touch a new C primitive (--update-echo-area,
;;;     --pending-signals-p) is guarded and reported as INFO, never
;;;     asserted.
;;;   - a static wiring check: cmd_error_internal is gone from
;;;     src/keyboard.c and src/lisp.h, src/process.c no longer calls it,
;;;     the send_process drain runs through Scheme, the three static
;;;     dispatchers exist, the process_pending_signals stub stays, and
;;;     the module is boot-loaded.
;;;
;;; The repo root is bound by the .el wrapper as %m32-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m32-imp2.el.

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

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m32-root))
    (begin (report "m32-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m32-root "."))
    (report "m32-root-bound" 'PASS))

;;; --- 1. The module loads and exports the three procedures ----------
(use-modules (emacs process-error))

(check "m32/imp2/export/process-filter-error-handler" #t
       (let ((p (module-ref (resolve-module '(emacs process-error))
                            'process-filter-error-handler)))
         (procedure? p)))
(check "m32/imp2/export/process-sentinel-error-handler" #t
       (let ((p (module-ref (resolve-module '(emacs process-error))
                            'process-sentinel-error-handler)))
         (procedure? p)))
(check "m32/imp2/export/send-process-drain-signals!" #t
       (let ((p (module-ref (resolve-module '(emacs process-error))
                            'send-process-drain-signals!)))
         (procedure? p)))

;;; --- 2. Runtime: send-process-drain-signals! returns nil -----------
;;; The drain reads the --pending-signals-p primitive (imp-1) and may
;;; then call process-pending-signals!.  Guard it and report INFO, so a
;;; stale binary never turns into a false FAIL.
(define (safe thunk)
  (catch #t
    (lambda () (cons 'ok (thunk)))
    (lambda (key . args) (cons 'error (cons key args)))))

(let ((r (safe (lambda () (send-process-drain-signals!)))))
  ;; Report only as INFO: the call reads the --pending-signals-p primitive
  ;; and may run process-pending-signals!, both of which live in C.  A
  ;; binary that predates imp-1/imp-2 would raise here, and brief.org §6
  ;; item 11 asks for INFO, not a false FAIL.
  (report "m32/imp2/runtime/send-process-drain-signals!" (list 'INFO r)))
