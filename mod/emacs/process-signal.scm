;;; process-signal.scm --- M39 imp-4: the process.c signal family
;;;                         ((emacs process-signal))
;;;
;;; Moves the *decision* of the src/process.c signal family out of C and
;;; into Scheme.  The *mechanism* stays C: the kill(2) syscall, the
;;; signal-number mapping (abbr_to_signal / str2sig), process_send_signal
;;; (the SIGNALS_VIA_CHARACTERS / TIOCGPGRP / TIOCSIGSEND work and the
;;; kill(2) call), and the stop/continue fd work (delete_read_fd,
;;; add_process_read_fd, tcflush, pset_command).
;;;
;;; Bridge shape (brief.org §5.2): Option A.  Thin mechanism DEFUNs live
;;; in src/process.c next to the imp-3 bridge.  The Scheme module owns the
;;; branch choice and calls them through the imported `symbol-function'.
;;; Option A was chosen because it gives src/image.c a C entry point that
;;; does not need the retired kill-process DEFUN (see src/image.c
;;; x_kill_gs_process, which now calls --signal-send), and because the
;;; mechanism names map one-to-one to the brief.org §3 mechanism list.
;;;
;;; Mechanism DEFUNs (all internal, `--' prefixed):
;;;
;;;   --signal-send                 process_send_signal wrapper
;;;   --signal-stop-connection      the stop-process fd / pset_command work
;;;   --signal-continue-connection  the continue-process fd / tcflush work
;;;   --signal-name-to-number       abbr_to_signal (signal-number mapping)
;;;   --signal-kill                 the kill(2) syscall
;;;   --signal-resolve-process      the static get_process (a process, a
;;;                                 buffer, a buffer name, or nil)
;;;   --signal-string-to-number     string_to_number + full-length test
;;;   --signal-process-pid          CHECK_PROCESS + pid + <= 0 error
;;;
;;; get-process is the existing C DEFUN; the string branch calls it
;;; through `symbol-function', so it needs no bridge (review D8).
;;;
;;; The connection gate of stop-process / continue-process reads the
;;; process `type' slot through the imp-3 --process-ref table.  A `type'
;;; read row was added to proc_slot_table for that (brief.org §14).
;;;
;;; Retired signal-family DEFUNs (imp-4):
;;;
;;;   internal-default-interrupt-process, interrupt-process,
;;;   kill-process, quit-process, stop-process, continue-process,
;;;   internal-default-signal-process, signal-process
;;;
;;; Each elisp name is reinstalled with define-elisp-inline, so the elisp
;;; function slot holds it and the elisp compiler may inline the body.
;;; The retired DEFUNs' docstrings and interactive specs are not lost:
;;; each docstring goes on the symbol plist as the `function-documentation'
;;; property (the property `documentation' reads), and each interactive
;;; spec goes on the procedure as the `interactive-form' procedure
;;; property (the property `commandp' and `interactive-form' test for a
;;; Scheme procedure).  See review D2 and D4.
;;;
;;; The inline body must reference only *imported* bindings and literals:
;;; define-elisp-inline absolutizes the body's free variables against the
;;; import chain, so a module-local helper would leave an unbound variable
;;; in the inlined elisp.  Every C subr is reached through the imported
;;; `symbol-function', and every elisp function by bare name only when it
;;; is a Guile-visible import (none here).
;;;
;;; Conventions (identical to M9-M39): #nil is elisp nil; no module-level
;;; mutable state.  Return an integer, not a Scheme #f, for any value C
;;; reads as a number: this Guile reads #f as elisp true.

(define-module (emacs process-signal)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (elisp-internal-default-interrupt-process
            elisp-interrupt-process
            elisp-kill-process
            elisp-quit-process
            elisp-stop-process
            elisp-continue-process
            elisp-internal-default-signal-process
            elisp-signal-process))

;; The connection gate is expressed inline in stop-process and
;; continue-process below: a process is a connection when its `type' slot
;; is network, serial, or pipe.  The gate reads the slot through the imp-3
;; C bridge --process-ref, so the decision stays in Scheme.

;; The DEFUNs took 0–2 or 2–3 arguments.  define-elisp-inline expands to a
;; plain `define', which cannot take #:optional (that is define* only), so
;; each name takes a rest list and reads its optional trailing arguments
;; from it.  elisp nil is #nil for a missing argument.

;;; --- the default actions -------------------------------------------

;; The signal number each default selects (SIGINT / SIGKILL / SIGQUIT /
;; SIGTSTP / SIGCONT) is looked up through the C mapping, so the
;; signal-number table stays C (brief.org §3).

(define-elisp-inline (internal-default-interrupt-process . args)
  (let ((process (if (null? args) #nil (car args)))
        (current-group (if (or (null? args) (null? (cdr args)))
                           #nil (cadr args))))
    ((symbol-function '--signal-send) process
     ((symbol-function '--signal-name-to-number) "SIGINT") current-group)))

(define-elisp-inline (kill-process . args)
  (let ((process (if (null? args) #nil (car args)))
        (current-group (if (or (null? args) (null? (cdr args)))
                           #nil (cadr args))))
    ((symbol-function '--signal-send) process
     ((symbol-function '--signal-name-to-number) "SIGKILL") current-group)
    process))

(define-elisp-inline (quit-process . args)
  (let ((process (if (null? args) #nil (car args)))
        (current-group (if (or (null? args) (null? (cdr args)))
                           #nil (cadr args))))
    ((symbol-function '--signal-send) process
     ((symbol-function '--signal-name-to-number) "SIGQUIT") current-group)
    process))

;; stop-process: the connection gate decides.  A connection gets the fd
;; work; any other process gets SIGTSTP.  The `No SIGTSTP support' error
;; fires when the C mapping has no SIGTSTP.

(define-elisp-inline (stop-process . args)
  (let ((process (if (null? args) #nil (car args)))
        (current-group (if (or (null? args) (null? (cdr args)))
                           #nil (cadr args))))
    (if (and ((symbol-function 'processp) process)
             (let ((type ((symbol-function '--process-ref) process 'type)))
               (or (eq? type 'network) (eq? type 'serial) (eq? type 'pipe))))
        ((symbol-function '--signal-stop-connection) process)
        (let ((signo ((symbol-function '--signal-name-to-number) "SIGTSTP")))
          (if (< signo 0)
              ((symbol-function 'error) "No SIGTSTP support")
              ((symbol-function '--signal-send) process signo current-group))))))

;; continue-process: same gate.  A connection gets the resume fd work;
;; any other process gets SIGCONT.

(define-elisp-inline (continue-process . args)
  (let ((process (if (null? args) #nil (car args)))
        (current-group (if (or (null? args) (null? (cdr args)))
                           #nil (cadr args))))
    (if (and ((symbol-function 'processp) process)
             (let ((type ((symbol-function '--process-ref) process 'type)))
               (or (eq? type 'network) (eq? type 'serial) (eq? type 'pipe))))
        ((symbol-function '--signal-continue-connection) process)
        (let ((signo ((symbol-function '--signal-name-to-number) "SIGCONT")))
          (if (< signo 0)
              ((symbol-function 'error) "No SIGCONT support")
              ((symbol-function '--signal-send) process signo current-group))))))

;; internal-default-signal-process: resolve the process, then the sigcode.
;; A string becomes a process (get-process) or a number; a non-number,
;; non-string becomes the static get_process (--signal-resolve-process,
;; which also accepts a buffer, a buffer name, or nil); a nil process
;; returns nil.  An integer sigcode is passed through; a symbol sigcode is
;; mapped by abbr_to_signal.
;;
;; The sigcode test is FIXNUMP, not `integer?`: the C body ran
;; check_integer_range on a fixnum only and sent a non-fixnum to
;; CHECK_SYMBOL.  A bignum must not reach --signal-kill, which runs
;; XFIXNUM on the signal, so the branch guards the fixnum range with
;; literals (review D6).

(define-elisp-inline (internal-default-signal-process process sigcode . rest)
  (let ((proc (if ((symbol-function 'stringp) process)
                  (let ((tem ((symbol-function 'get-process) process)))
                    (if ((symbol-function 'null) tem)
                        ((symbol-function '--signal-string-to-number) process)
                        tem))
                  (if ((symbol-function 'numberp) process)
                      process
                      ((symbol-function '--signal-resolve-process) process)))))
    (if ((symbol-function 'null) proc)
        #nil
        (let ((signo (if (and (integer? sigcode)
                              (<= -2305843009213693952 sigcode
                                  2305843009213693951))
                         sigcode
                         (let ((n ((symbol-function '--signal-name-to-number)
                                   ((symbol-function 'symbol-name) sigcode))))
                           (if (< n 0)
                               ((symbol-function 'error)
                                "Undefined signal name %s" sigcode)
                               n)))))
          ((symbol-function '--signal-kill)
           (if ((symbol-function 'numberp) proc)
               proc
               ((symbol-function '--signal-process-pid) proc))
           signo)))))

;;; --- the hook runners ---------------------------------------------

;; interrupt-process and signal-process are thin: each runs its hook list
;; until a function succeeds.  The hook runner
;; (run-hook-with-args-until-success) is still a C DEFUN, but the
;; *decision* moved to Scheme: which hook list to run, and with which
;; arguments.  A body with no separable decision would stay C.

(define-elisp-inline (interrupt-process . args)
  (let ((process (if (null? args) #nil (car args)))
        (current-group (if (or (null? args) (null? (cdr args)))
                           #nil (cadr args))))
    ((symbol-function 'run-hook-with-args-until-success)
     'interrupt-process-functions process current-group)))

(define-elisp-inline (signal-process process sigcode . args)
  (let ((remote (if (null? args) #nil (car args))))
    ((symbol-function 'run-hook-with-args-until-success)
     'signal-process-functions process sigcode remote)))

;;; --- the retired docstrings and interactive specs -----------------

;; The retired C DEFUNs carried a docstring and, for kill-process and
;; signal-process, an interactive spec.  Keep both (review D2, D4).
;;
;; The docstring goes on the symbol plist as `function-documentation';
;; that is the property `documentation' reads for a symbol (Fdocumentation,
;; src/doc.c).  set-symbol-plist! is the runtime procedure the C
;; symbol_plist bridges to; the elisp `put' subr's function slot is not
;; resolvable while the dump loads this module.
;;
;; The interactive form goes on the *procedure* as the `interactive-form'
;; procedure property: `commandp' and `interactive-form' test
;; scm_procedure_properties for a Scheme procedure (src/eval.c:1257,
;; src/data.c:873), not the symbol plist.

(define (install-doc-and-interactive! name doc . interactive)
  (set-symbol-plist! name (list 'function-documentation doc))
  (if (pair? interactive)
      (set-procedure-property! (symbol-function name)
                               'interactive-form (car interactive))))

(install-doc-and-interactive!
 'internal-default-interrupt-process
 "Default function to interrupt process PROCESS.
It shall be the last element in list `interrupt-process-functions'.
See function `interrupt-process' for more details on usage.")

(install-doc-and-interactive!
 'interrupt-process
 "Interrupt process PROCESS.
PROCESS may be a process, a buffer, or the name of a process or buffer.
No arg or nil means current buffer's process.
Second arg CURRENT-GROUP non-nil means send signal to
the current process-group of the process's controlling terminal
rather than to the process's own process group.
If the process is a shell, this means interrupt current subjob
rather than the shell.

If CURRENT-GROUP is `lambda', and if the shell owns the terminal,
don't send the signal.

This function calls the functions of `interrupt-process-functions' in
the order of the list, until one of them returns non-nil.")

(install-doc-and-interactive!
 'kill-process
 "Kill process PROCESS.  May be process or name of one.
See function `interrupt-process' for more details on usage."
 '(list (read-process-name "Kill process")))

(install-doc-and-interactive!
 'quit-process
 "Send QUIT signal to process PROCESS.  May be process or name of one.
See function `interrupt-process' for more details on usage.")

(install-doc-and-interactive!
 'stop-process
 "Stop process PROCESS.  May be process or name of one.
See function `interrupt-process' for more details on usage.
If PROCESS is a network or serial or pipe connection, inhibit handling
of incoming traffic.")

(install-doc-and-interactive!
 'continue-process
 "Continue process PROCESS.  May be process or name of one.
See function `interrupt-process' for more details on usage.
If PROCESS is a network or serial process, resume handling of incoming
traffic.")

(install-doc-and-interactive!
 'internal-default-signal-process
 "Default function to send PROCESS the signal with code SIGCODE.
It shall be the last element in list `signal-process-functions'.
See function `signal-process' for more details on usage.")

(install-doc-and-interactive!
 'signal-process
 "Send PROCESS the signal with code SIGCODE.
PROCESS may also be a number specifying the process id of the
process to signal; in this case, the process need not be a child of
this Emacs.
If PROCESS is a process object which contains the property
`remote-pid', or PROCESS is a number and REMOTE is a remote file name,
PROCESS is interpreted as process on the respective remote host, which
will be the process to signal.
If PROCESS is a string, it is interpreted as process object with the
respective process name, or as a number.
SIGCODE may be an integer, or a symbol whose name is a signal name."
 '(list (read-string "Process (name or number): ")
        (read-signal-name)))
