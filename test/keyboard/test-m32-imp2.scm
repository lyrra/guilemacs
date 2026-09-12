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

;;; --- 3. Static: cmd_error_internal is fully retired ----------------
(define kbd-c (slurp (repo "src/keyboard.c")))
(if (not kbd-c)
    (report "m32/imp2/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m32/imp2/keyboard.c/no-cmd-error-internal" #f
             (contains? kbd-c "cmd_error_internal"))
      (check "m32/imp2/keyboard.c/primitive-update-echo-area" #t
             (contains? kbd-c "\"--update-echo-area\""))
      ;; The process_pending_signals stub must survive (xdisp.c calls it).
      (check "m32/imp2/keyboard.c/stub-process-pending-signals" #t
             (contains? kbd-c "process_pending_signals (void)"))))

(define lisp-h (slurp (repo "src/lisp.h")))
(if (not lisp-h)
    (report "m32/imp2/scan/lisp.h" (cons 'FAIL "src/lisp.h missing"))
    (check "m32/imp2/lisp.h/no-cmd-error-internal-decl" #f
           (contains? lisp-h "cmd_error_internal")))

;;; --- 4. Static: src/process.c rewires to the module ----------------
(define proc-c (slurp (repo "src/process.c")))
(if (not proc-c)
    (report "m32/imp2/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      (check "m32/imp2/process.c/no-cmd-error-internal-call" #f
             (contains? proc-c "cmd_error_internal"))
      ;; Brief §6 item 4: process.c resolves the module through
      ;; scm_c_public_ref ("emacs process-error", ...), not just by name.
      (check "m32/imp2/process.c/refs-module-public-ref" #t
             (contains? proc-c "scm_c_public_ref (\"emacs process-error\""))
      ;; The old C handler bodies are gone: the context strings moved
      ;; into the module.
      (check "m32/imp2/process.c/no-filter-context-string" #f
             (contains? proc-c "error in process filter: "))
      (check "m32/imp2/process.c/no-sentinel-context-string" #f
             (contains? proc-c "error in process sentinel: "))
      ;; The three static dispatchers resolve the module procedures.
      (check "m32/imp2/process.c/refs-filter-handler" #t
             (contains? proc-c "process-filter-error-handler"))
      (check "m32/imp2/process.c/refs-sentinel-handler" #t
             (contains? proc-c "process-sentinel-error-handler"))
      (check "m32/imp2/process.c/refs-drain" #t
             (contains? proc-c "send-process-drain-signals!"))
      (check "m32/imp2/process.c/defines-filter-dispatcher" #t
             (contains? proc-c "read_process_output_error_handler (Lisp_Object error_val)"))
      (check "m32/imp2/process.c/defines-sentinel-dispatcher" #t
             (contains? proc-c "exec_sentinel_error_handler (Lisp_Object error_val)"))
      (check "m32/imp2/process.c/defines-drain-dispatcher" #t
             (contains? proc-c "send_process_drain_signals (void)"))
      (check "m32/imp2/process.c/calls-drain-dispatcher" #t
             (contains? proc-c "send_process_drain_signals ();"))
      ;; Job 3: no bare `if (pending_signals)' test remains in send_process.
      (check "m32/imp2/process.c/no-bare-pending-signals-test" #f
             (contains? proc-c "if (pending_signals)"))))

;;; --- 5. Static: the module owns the context strings + the drain ----
(define pe (slurp (repo "mod/emacs/process-error.scm")))
(if (not pe)
    (report "m32/imp2/scan/module" (cons 'FAIL "mod/emacs/process-error.scm missing"))
    (begin
      (check "m32/imp2/module/filter-context-string" #t
             (contains? pe "error in process filter: "))
      (check "m32/imp2/module/sentinel-context-string" #t
             (contains? pe "error in process sentinel: "))
      (check "m32/imp2/module/calls-cmd-error-internal" #t
             (contains? pe "cmd-error-internal!"))
      (check "m32/imp2/module/inhibits-quit" #t
             (contains? pe "inhibit-quit"))
      (check "m32/imp2/module/reads-pause-time" #t
             (contains? pe "process-error-pause-time"))
      (check "m32/imp2/module/drain-arm" #t
             (contains? pe "%--pending-signals-p"))
      (check "m32/imp2/module/process-pending-signals-arm" #t
             (contains? pe "%process-pending-signals!"))
      (check "m32/imp2/module/export-names" #t
             (and (contains? pe "process-filter-error-handler")
                  (contains? pe "process-sentinel-error-handler")
                  (contains? pe "send-process-drain-signals!")))))

;;; --- 6. Static: boot load + test registration ----------------------
(define load-scm (slurp (repo "prelude/load.scm")))
(check "m32/imp2/load.scm/registers-module" #t
       (contains? load-scm "(emacs process-error)"))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m32/imp2/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m32-imp2.el"))
