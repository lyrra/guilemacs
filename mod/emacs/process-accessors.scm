;;; process-accessors.scm --- M39 imp-3: the process.c Group A accessors
;;;                           ((emacs process-accessors))
;;;
;;; Moves the *decision* of the src/process.c Group A accessors out of C
;;; and into Scheme.  The slot stays C: each reader and writer reaches a
;;; slot of struct Lisp_Process through the table-driven C bridge
;;; --process-ref / --process-set! (see the proc_slot_table in
;;; src/process.c).  The elisp names are kept, so a caller that resolves
;;; the name in the elisp function slot does not change.
;;;
;;; Every accessor is defined with `define-elisp-inline', so the elisp
;;; function slot holds it and the elisp compiler may inline the body.
;;; The module needs no separate registration function.
;;;
;;; The inline body must reference only *imported* bindings and literals:
;;; define-elisp-inline compiles the body to tree-il and absolutizes its
;;; free variables against the import chain, so a module-local helper
;;; (for example `%ref') would leave an unbound variable in the inlined
;;; elisp.  Each body reaches the C subr directly through the imported
;;; `symbol-function'.
;;;
;;; Retired Group A DEFUNs (imp-3):
;;;
;;;   process-id, process-command, process-buffer, process-mark,
;;;   process-filter, process-sentinel, process-thread, process-plist,
;;;   process-coding-system, process-query-on-exit-flag,
;;;   set-process-query-on-exit-flag,
;;;   set-process-inherit-coding-system-flag, set-process-plist.
;;;
;;; And the disabled `process-connection' DEFUN (#if 0, never built).
;;;
;;; Names that stay C in this imp, with the reason (brief.org §6 rule 2
;;; allows a not-thin name to leave the batch):
;;;
;;;   get-process        -- reads Vprocess_alist; not a struct slot.
;;;   process-status     -- calls update_status and maps run/open/closed;
;;;                         it also has a live C caller (src/xdisp.c).
;;;   process-exit-status -- calls update_status, then reads the status
;;;                         list; not a plain slot.
;;;   process-name       -- a plain slot, but src/fns.c:2935 calls
;;;                         Fprocess_name, so the DEFUN cannot retire.
;;;   process-tty-name   -- reads four slots (tty_name, pty_in, pty_out,
;;;                         stderrproc) plus a stream argument.
;;;   process-type       -- calls the get_process mechanism.
;;;   waiting-for-user-input-p -- reads a C global flag, not a process
;;;                         slot.
;;;   process-inherit-coding-system-flag -- a plain read, but the DEFUN
;;;                         has an #ifdef subprocesses / #else dual path
;;;                         with a non-subprocesses global fallback.
;;;   set-process-buffer, set-process-filter, set-process-sentinel,
;;;   set-process-thread -- each has side work (fd mask, update_process_
;;;                         mark, childp plist_put, fd_callback_info,
;;;                         coding setup).
;;;
;;; Conventions (identical to M9-M39): #nil is elisp nil; no module-level
;;; mutable state.  Return an integer, not a Scheme #f, for any value C
;;; reads as a number: this Guile reads #f as elisp true.

(define-module (emacs process-accessors)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (elisp-process-id
            elisp-process-command
            elisp-process-buffer
            elisp-process-mark
            elisp-process-filter
            elisp-process-sentinel
            elisp-process-thread
            elisp-process-plist
            elisp-process-coding-system
            elisp-process-query-on-exit-flag
            elisp-set-process-query-on-exit-flag
            elisp-set-process-inherit-coding-system-flag
            elisp-set-process-plist))

;; The C bridge.  Each body calls the subr through `symbol-function' (an
;; imported binding) so the inlined elisp carries no module-local free
;; variable.  --process-ref reads one slot; --process-set! writes one.

(define-elisp-inline (process-id process)
  (let ((pid ((symbol-function '--process-ref) process 'pid)))
    (if (= pid 0) #nil pid)))

(define-elisp-inline (process-command process)
  ((symbol-function '--process-ref) process 'command))

(define-elisp-inline (process-buffer process)
  ((symbol-function '--process-ref) process 'buffer))

(define-elisp-inline (process-mark process)
  ((symbol-function '--process-ref) process 'mark))

(define-elisp-inline (process-filter process)
  ((symbol-function '--process-ref) process 'filter))

(define-elisp-inline (process-sentinel process)
  ((symbol-function '--process-ref) process 'sentinel))

(define-elisp-inline (process-thread process)
  ((symbol-function '--process-ref) process 'thread))

(define-elisp-inline (process-plist process)
  ((symbol-function '--process-ref) process 'plist))

(define-elisp-inline (process-coding-system process)
  (cons ((symbol-function '--process-ref) process 'decode_coding_system)
        ((symbol-function '--process-ref) process 'encode_coding_system)))

(define-elisp-inline (process-query-on-exit-flag process)
  (if (eq? ((symbol-function '--process-ref) process 'kill_without_query)
           #nil)
      #t #nil))

(define-elisp-inline (set-process-query-on-exit-flag process flag)
  ((symbol-function '--process-set!) process '--set-query-on-exit-flag
   (if (eq? flag #nil) #t #nil))
  flag)

(define-elisp-inline (set-process-inherit-coding-system-flag process flag)
  ((symbol-function '--process-set!) process
   '--set-inherit-coding-system-flag flag)
  flag)

(define-elisp-inline (set-process-plist process plist)
  ((symbol-function '--process-set!) process '--set-plist plist)
  plist)
