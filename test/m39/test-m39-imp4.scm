;;; test-m39-imp4.scm --- M39 imp-4: the process.c signal family.
;;;
;;; brief.org (M39 imp-4) moves the decision of the src/process.c signal
;;; family into the module (emacs process-signal).  The mechanism stays
;;; C: the kill(2) syscall, abbr_to_signal, process_send_signal, and the
;;; stop/continue fd work.  Each moved elisp name is reinstalled with
;;; define-elisp-inline; the C reaches the mechanism through thin
;;; --signal-* DEFUNs.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - a runtime check: the module loads and installs every moved
;;;     signal name in the elisp function slot (define-elisp-inline);
;;;   - a static wiring check: the retired DEFUNs are gone from
;;;     src/process.c, the --signal-* bridge and the type slot row exist,
;;;     src/image.c no longer calls Fkill_process, the module is loaded
;;;     by the prelude, and run-tests.scm lists the imp-4 corpus.
;;;
;;; The live signal behaviour is exercised by test/m39/test-m39-imp4.el.
;;;
;;; The repo root is bound by the .el wrapper as %m39-root.

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
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (absent? text needle)
  (and (string? text) (not (contains? text needle))))

(define (repo path) (string-append %m39-root "/" path))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m39-root))
    (begin (report "m39-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m39-root "."))
    (report "m39-root-bound" 'PASS))

;;; --- 1. The module loads and installs every moved name -------------
(use-modules (emacs process-signal))
(use-modules (emacs-elisp runtime))

(define (installed name)
  (let ((f (symbol-function name)))
    (and f (procedure? f))))

(for-each
 (lambda (name)
   (check (string-append "m39/imp4/installed/" (symbol->string name)) #t
          (installed name)))
 '(internal-default-interrupt-process interrupt-process kill-process
   quit-process stop-process continue-process
   internal-default-signal-process signal-process))

;;; --- 2. Static: the module source defines the decisions ------------
(define ps (slurp (repo "mod/emacs/process-signal.scm")))
(if (not ps)
    (report "m39/imp4/scan/module"
            (cons 'FAIL "mod/emacs/process-signal.scm missing"))
    (begin
      (check "m39/imp4/module/defines-kill" #t
             (contains? ps "(define-elisp-inline (kill-process . args)"))
      (check "m39/imp4/module/defines-quit" #t
             (contains? ps "(define-elisp-inline (quit-process . args)"))
      (check "m39/imp4/module/defines-stop" #t
             (contains? ps "(define-elisp-inline (stop-process . args)"))
      (check "m39/imp4/module/defines-continue" #t
             (contains? ps "(define-elisp-inline (continue-process . args)"))
      (check "m39/imp4/module/defines-signal" #t
             (contains? ps "(define-elisp-inline (signal-process process sigcode . args)"))
      (check "m39/imp4/module/defines-default-signal" #t
             (contains? ps "(define-elisp-inline (internal-default-signal-process"))
      ;; The connection gate reads the type slot and names the three types.
      (check "m39/imp4/module/gate-type" #t
             (contains? ps "(symbol-function '--process-ref) process 'type)"))
      (check "m39/imp4/module/gate-network" #t (contains? ps "(eq? type 'network)"))
      (check "m39/imp4/module/gate-serial" #t (contains? ps "(eq? type 'serial)"))
      (check "m39/imp4/module/gate-pipe" #t (contains? ps "(eq? type 'pipe)"))
      ;; The signal choices go through the C mapping, not literals.
      (check "m39/imp4/module/sigint" #t (contains? ps "\"SIGINT\""))
      (check "m39/imp4/module/sigkill" #t (contains? ps "\"SIGKILL\""))
      (check "m39/imp4/module/sigquit" #t (contains? ps "\"SIGQUIT\""))
      (check "m39/imp4/module/sigtstp" #t (contains? ps "\"SIGTSTP\""))
      (check "m39/imp4/module/sigcont" #t (contains? ps "\"SIGCONT\""))
      ;; The hook runners run the hook list until success.
      (check "m39/imp4/module/hook-runner" #t
             (contains? ps "(symbol-function 'run-hook-with-args-until-success)"))
      ;; The C subrs are reached through the imported symbol-function.
      (check "m39/imp4/module/symbol-function-send" #t
             (contains? ps "(symbol-function '--signal-send)"))
      (check "m39/imp4/module/symbol-function-kill" #t
             (contains? ps "(symbol-function '--signal-kill)"))
      ;; The string branch uses the existing get-process DEFUN, and the
      ;; non-number branch uses the static get_process bridge (D8, D1).
      (check "m39/imp4/module/uses-get-process" #t
             (contains? ps "(symbol-function 'get-process)"))
      (check "m39/imp4/module/resolve-process" #t
             (contains? ps "(symbol-function '--signal-resolve-process)"))
      ;; The docstrings and interactive forms are reinstalled on the
      ;; symbol plist (D2, D4).
      (check "m39/imp4/module/installs-docstring" #t
             (contains? ps "'function-documentation"))
      (check "m39/imp4/module/installs-interactive" #t
             (contains? ps "'interactive-form"))))

;;; --- 3. Static: src/process.c bridge and retired DEFUNs -------------
(define proc-c (slurp (repo "src/process.c")))
(if (not proc-c)
    (report "m39/imp4/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      ;; The mechanism bridge exists.
      (for-each
       (lambda (name)
         (check (string-append "m39/imp4/process.c/defines/" name) #t
                (contains? proc-c (string-append "DEFUN (\"" name "\""))))
       '("--signal-send" "--signal-stop-connection" "--signal-continue-connection"
         "--signal-name-to-number" "--signal-kill" "--signal-resolve-process"
         "--signal-string-to-number" "--signal-process-pid"))
      ;; The redundant --signal-get-process bridge is gone; the string
      ;; branch uses the existing get-process DEFUN (review D8).
      (check "m39/imp4/process.c/no-signal-get-process" #t
             (absent? proc-c "--signal-get-process"))
      ;; The type slot read row exists in the imp-3 table.
      (check "m39/imp4/process.c/table-type-row" #t
             (contains? proc-c
                        "{ \"type\", offsetof (struct Lisp_Process, type), PROC_LISP_OBJECT }"))
      ;; The mechanism keeps abbr_to_signal, process_send_signal, kill(2).
      (check "m39/imp4/process.c/keeps-abbr-to-signal" #t
             (contains? proc-c "abbr_to_signal (char const *name)"))
      (check "m39/imp4/process.c/keeps-process-send-signal" #t
             (contains? proc-c "process_send_signal (Lisp_Object process, int signo"))
      (check "m39/imp4/process.c/keeps-kill-syscall" #t
             (contains? proc-c "kill (pid, XFIXNUM (signal))"))
      ;; Every retired DEFUN is gone.
      (for-each
       (lambda (name)
         (check (string-append "m39/imp4/process.c/retired/" name) #t
                (absent? proc-c (string-append "DEFUN (\"" name "\""))))
       '("internal-default-interrupt-process" "interrupt-process" "kill-process"
         "quit-process" "stop-process" "continue-process"
         "internal-default-signal-process" "signal-process"))))

;;; --- 4. Static: src/image.c rewired --------------------------------
(define image-c (slurp (repo "src/image.c")))
(if (not image-c)
    (report "m39/imp4/scan/image.c" (cons 'FAIL "src/image.c missing"))
    (begin
      (check "m39/imp4/image.c/no-Fkill_process" #t
             (absent? image-c "Fkill_process"))
      ;; x_kill_gs_process calls the C mechanism entry directly (review D5).
      (check "m39/imp4/image.c/calls-signal-send" #t
             (contains? image-c
                        "call3 (intern (\"--signal-send\"), img->lisp_data, make_fixnum (SIGKILL), Qnil)"))
      (check "m39/imp4/image.c/includes-signal-h" #t
             (contains? image-c "#include <signal.h>"))))

;;; --- 5. Static: the module is loaded by the prelude -----------------
(define prelude (slurp (repo "prelude/load.scm")))
(check "m39/imp4/prelude/loads-process-signal" #t
       (contains? prelude "(use-modules (emacs process-signal))"))

;;; --- 6. Static: run-tests.scm registers the imp-4 corpus ------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m39/imp4/run-tests.scm/registers-el" #t
       (contains? run-tests "test/m39/test-m39-imp4.el"))

;;; --- 7. Runtime: each name selects the right signal ----------------

(define (module-proc name)
  (module-ref (resolve-module '(emacs process-signal)) name))

(define (signal-number name)
  ((symbol-function '--signal-name-to-number) name))

;; Record the signal the module sends and the connection branch it
;; takes, by overriding the C mechanism subrs for the extent of a call.
;; The reinstalled elisp bodies resolve (symbol-function '--signal-*)
;; at call time, so the override is visible.  This records the *choice*,
;; not a text match (review D3).
(define sent '())
(define (record-push! v) (set! sent (cons v sent)))
(define (reset-sent!) (set! sent '()))
(define (last-sent) (if (null? sent) #f (car sent)))
(define (record-send proc signo cg) (record-push! signo) proc)
(define (record-stop proc) (record-push! 'stop-connection) proc)
(define (record-cont proc) (record-push! 'continue-connection) proc)

(define saved-send (symbol-function '--signal-send))
(define saved-stop (symbol-function '--signal-stop-connection))
(define saved-cont (symbol-function '--signal-continue-connection))
(define saved-processp (symbol-function 'processp))
(define saved-ref (symbol-function '--process-ref))

(set-symbol-function! '--signal-send record-send)
(set-symbol-function! '--signal-stop-connection record-stop)
(set-symbol-function! '--signal-continue-connection record-cont)

(define (signal-sent-by name . args)
  (reset-sent!)
  (apply (symbol-function name) args)
  (last-sent))

(check "m39/imp4/behavior/kill-process-sends-SIGKILL" (signal-number "SIGKILL")
       (signal-sent-by 'kill-process #nil #nil))
(check "m39/imp4/behavior/quit-process-sends-SIGQUIT" (signal-number "SIGQUIT")
       (signal-sent-by 'quit-process #nil #nil))
(check "m39/imp4/behavior/interrupt-default-sends-SIGINT" (signal-number "SIGINT")
       (signal-sent-by 'internal-default-interrupt-process #nil #nil))

;; The connection gate: a connection type takes the fd branch, anything
;; else takes the signal.  Stub processp and --process-ref so network,
;; serial, pipe, and a plain process are all covered without a live
;; object (review D3).
(define (stub-type! type)
  (set-symbol-function! 'processp (lambda (p) #t))
  (set-symbol-function! '--process-ref (lambda (p slot) type)))

(define (gate-result name type)
  (stub-type! type)
  (signal-sent-by name #nil #nil))

(check "m39/imp4/behavior/stop-network-connection" 'stop-connection
       (gate-result 'stop-process 'network))
(check "m39/imp4/behavior/stop-serial-connection" 'stop-connection
       (gate-result 'stop-process 'serial))
(check "m39/imp4/behavior/stop-pipe-connection" 'stop-connection
       (gate-result 'stop-process 'pipe))
(check "m39/imp4/behavior/stop-real-process-sends-SIGTSTP" (signal-number "SIGTSTP")
       (gate-result 'stop-process 'real))
(check "m39/imp4/behavior/continue-network-connection" 'continue-connection
       (gate-result 'continue-process 'network))
(check "m39/imp4/behavior/continue-serial-connection" 'continue-connection
       (gate-result 'continue-process 'serial))
(check "m39/imp4/behavior/continue-pipe-connection" 'continue-connection
       (gate-result 'continue-process 'pipe))
(check "m39/imp4/behavior/continue-real-process-sends-SIGCONT" (signal-number "SIGCONT")
       (gate-result 'continue-process 'real))

;; restore the C mechanism and the predicates.
(set-symbol-function! '--signal-send saved-send)
(set-symbol-function! '--signal-stop-connection saved-stop)
(set-symbol-function! '--signal-continue-connection saved-cont)
(set-symbol-function! 'processp saved-processp)
(set-symbol-function! '--process-ref saved-ref)

;;; --- 8. Runtime: the module owns each retired name; the docstring and
;;;         the interactive form are kept ---------------------------------

;; The retired C DEFUNs are gone; the module's define-elisp-inline
;; reinstall owns each function slot.  This proves at run time that no C
;; DEFUN registers the name (review D3).
(for-each
 (lambda (pair)
   (check (string-append "m39/imp4/behavior/reinstall-owns/"
                         (symbol->string (car pair)))
          #t
          (eq? (symbol-function (car pair)) (module-proc (cdr pair)))))
 '((internal-default-interrupt-process . elisp-internal-default-interrupt-process)
   (interrupt-process . elisp-interrupt-process)
   (kill-process . elisp-kill-process)
   (quit-process . elisp-quit-process)
   (stop-process . elisp-stop-process)
   (continue-process . elisp-continue-process)
   (internal-default-signal-process . elisp-internal-default-signal-process)
   (signal-process . elisp-signal-process)))

;; The docstring is on the symbol plist (review D2).
(check "m39/imp4/behavior/docstring-kill-process" #t
       (string? ((symbol-function 'get) 'kill-process 'function-documentation)))
(check "m39/imp4/behavior/docstring-signal-process" #t
       (string? ((symbol-function 'get) 'signal-process 'function-documentation)))
(check "m39/imp4/behavior/docstring-interrupt-process" #t
       (string? ((symbol-function 'get) 'interrupt-process 'function-documentation)))

;; The interactive form is kept for kill-process and signal-process, so
;; M-x still prompts (review D4).  commandp is the run-time proof.  The
;; form is single-wrapped: (interactive FORM), not (interactive
;; (interactive FORM)).
(define (interactive-form-of name)
  ((symbol-function 'interactive-form) name))
(check "m39/imp4/behavior/interactive-kill-process" #t
       (let ((f (interactive-form-of 'kill-process)))
         (and (pair? f) (eq? 'interactive (car f))
              (let ((form (cadr f)))
                (and (pair? form) (eq? 'list (car form)))))))
(check "m39/imp4/behavior/interactive-signal-process" #t
       (let ((f (interactive-form-of 'signal-process)))
         (and (pair? f) (eq? 'interactive (car f))
              (let ((form (cadr f)))
                (and (pair? form) (eq? 'list (car form)))))))
(check "m39/imp4/behavior/commandp-kill-process" #t
       (eq? #t ((symbol-function 'commandp) 'kill-process)))
(check "m39/imp4/behavior/commandp-signal-process" #t
       (eq? #t ((symbol-function 'commandp) 'signal-process)))
;; A name with no interactive spec stays a non-command.
(check "m39/imp4/behavior/not-commandp-quit-process" #t
       (eq? #nil ((symbol-function 'commandp) 'quit-process)))
