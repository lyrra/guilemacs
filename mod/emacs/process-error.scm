;;; process-error.scm --- M32 imp-2: the process.c error paths
;;;                       ((emacs process-error))
;;;
;;; Moves the *bodies* of the two process.c error handlers out of C and
;;; into Scheme:
;;;
;;;   process-filter-error-handler   -- read_process_output_error_handler
;;;                                     (src/process.c:6208-6217).
;;;   process-sentinel-error-handler -- exec_sentinel_error_handler
;;;                                     (src/process.c:7783-7795).
;;;
;;; It also owns the send_process EINTR-loop drain choice
;;; (src/process.c:6861-6862), exported as send-process-drain-signals!.
;;;
;;; The C entry points stay C.  Each handler keeps its C function
;;; pointer (internal_condition_case_1 takes a C pointer of type
;;; Lisp_Object (*)(Lisp_Object)); each is now a thin static dispatcher
;;; into this module, exactly as imp-1 did for the wait decision path.
;;; The sendto / write system calls and the EINTR loop control also
;;; stay C.
;;;
;;; The old C function cmd_error_internal retires here: process.c was
;;; its last caller.  This module calls its Scheme body directly, the
;;; (emacs command-loop) export cmd-error-internal!.
;;;
;;; The process_pending_signals stub *stays* C: xdisp.c still calls it.
;;; This module reads the pending-signals flag through the imp-1
;;; keyboard.c primitive and runs the Scheme drain in (emacs gobble).
;;;
;;; Conventions (identical to M9-M32): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); #nil is elisp nil; no module-level
;;; mutable state.

(define-module (emacs process-error)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (process-filter-error-handler
            process-sentinel-error-handler
            send-process-drain-signals!))

;; C shims.  --update-echo-area is a new M32 imp-2 keyboard.c primitive
;; (update_echo_area is not a DEFUN; no existing entry fits -- --echo-now
;; calls echo_now and --echo-update calls echo_update).  --pending-signals-p
;; is the imp-1 reader of the keyboard input-state flag.
(defelisp %--update-echo-area --update-echo-area)
(defelisp %--pending-signals-p  --pending-signals-p)

;; The error context target is the Scheme body of the retired C
;; cmd_error_internal: resolve it lazily, like the other cross-module
;; targets, so the module does not eagerly import (emacs command-loop).
(define %cmd-error-internal!
  (delay (module-ref (resolve-module '(emacs command-loop))
                     'cmd-error-internal!)))

;; The pending-signals drain is already a Scheme procedure in (emacs
;; gobble); resolve it lazily, like (emacs process-wait) does.
(define %process-pending-signals!
  (delay (module-ref (resolve-module '(emacs gobble))
                     'process-pending-signals!)))

;; The action sequence both C handlers share, in the original C order:
;; report DATA in CONTEXT, inhibit quit, refresh the echo area, then
;; pause when process-error-pause-time is positive.  Returns #t (Qt).
(define (%report-and-pause! data context)
  ((force %cmd-error-internal!) data context)
  (set-symbol-value! 'inhibit-quit #t)
  ((force %--update-echo-area))
  (let ((pause (symbol-value 'process-error-pause-time)))
    (when (> pause 0)
      ((%c 'sleep-for) pause #nil)))
  #t)

(define (process-filter-error-handler error-val)
  "Port of read_process_output_error_handler (src/process.c:6208-6217):
report the error in the process-filter context, inhibit quit, refresh
the echo area, and pause when process-error-pause-time is positive.
Returns #t (the C Qt), like the C handler."
  (%report-and-pause! error-val "error in process filter: "))

(define (process-sentinel-error-handler error-val)
  "Port of exec_sentinel_error_handler (src/process.c:7783-7795).  Makes
ERROR-VAL a cons cell first, as the rest of error handling expects, then
reports the error in the process-sentinel context.  Otherwise identical
to process-filter-error-handler.  Returns #t."
  (when (not (pair? error-val))
    (set! error-val (cons 'error error-val)))
  (%report-and-pause! error-val "error in process sentinel: "))

(define (send-process-drain-signals!)
  "When the pending-signals flag is set, run process-pending-signals!.
Port of the send_process EINTR-loop drain (src/process.c:6861-6862).
Returns nil."
  (when (not (eq? ((force %--pending-signals-p)) #nil))
    ((force %process-pending-signals!)))
  #nil)
