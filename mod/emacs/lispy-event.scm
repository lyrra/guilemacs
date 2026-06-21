(define-module (emacs lispy-event)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (make-lispy-event-dispatch
            make-lispy-event))

;;; M9 — make_lispy_event port to Scheme.
;;;
;;; make_lispy_event (src/keyboard.c:6450–7532) is a 1083-line
;;; switch(event->kind) that transforms a struct input_event into
;;; a Lisp event form.  It has no I/O, no syscalls, no signal
;;; handlers — pure transformation — making it the cleanest
;;; candidate for Scheme migration in keyboard.c.
;;;
;;; C-side infrastructure:
;;;   ie-smob   — foreign-pointer SMOB wrapping struct input_event *
;;;               (src/keyboard.c:874–943, tag in src/guile.c).
;;;   --ie-*    — field-accessor DEFUNs (imp-1.2).
;;;   --set-ie-* — field mutators (imp-1.3).
;;;
;;; The module's dispatch table is keyed by event_kind int; each
;;; entry is a Scheme procedure that takes an ie-smob and returns
;;; a Lisp event form.  The orchestrator looks up the kind and
;;; calls the registered procedure, falling through to C's
;;; --make-lispy-event-c for kinds not yet ported.
;;;
;;; See docs/m9-plan.org for the full implementation DAG.

(define make-lispy-event-dispatch
  ;; Hash table keyed by event_kind integers; populate with hashv-set!
  ;; and look up with hashv-ref.  Entries are added incrementally as
  ;; cases are ported (imp-3 → imp-7).
  (make-hash-table))

\f
;;; Lazy C-primitive references.  Resolved at first call so module
;;; load order is not sensitive to DEFUN registration order.

(define (%c name) (symbol-function name))

(define %--ie-kind              (delay (%c '--ie-kind)))
(define %--ie-arg               (delay (%c '--ie-arg)))
(define %--ie-frame-or-window   (delay (%c '--ie-frame-or-window)))
(define %--make-lispy-event-c   (delay (%c '--make-lispy-event-c)))
(define %--ie-kind-from-name    (delay (%c '--ie-kind-from-name)))

;;; Helper: register a per-kind handler in the dispatch table.
;;; Uses --ie-kind-from-name to convert a symbol (e.g. 'dbus-event)
;;; into its event_kind integer, then stores PROC under that key.

(define (register-kind! name-symbol proc)
  (let ((k ((force %--ie-kind-from-name) name-symbol)))
    (when (>= k 0)
      (hashv-set! make-lispy-event-dispatch k proc))))

;;; Orchestrator.

(define (make-lispy-event ie)
  "Transform an input-event SMOB into a Lisp event form.

Looks up (--ie-kind IE) in the dispatch table.  When a Scheme
procedure is registered for that kind, calls it with IE; otherwise
falls through to C's --make-lispy-event-c, which runs the original
make_lispy_event body."
  (let* ((kind ((force %--ie-kind) ie))
         (proc (hashv-ref make-lispy-event-dispatch kind)))
    (if proc
        (proc ie)
        ((force %--make-lispy-event-c) ie))))

;;; Per-kind handlers — imp-3 (trivial cases).

;;; Each handler: (cons <event-symbol> (--ie-arg ie))

(define (mle-dbus-event ie)
  (cons 'dbus-event ((force %--ie-arg) ie)))

(define (mle-thread-event ie)
  (cons 'thread-event ((force %--ie-arg) ie)))

(define (mle-xwidget-event ie)
  (cons 'xwidget-event ((force %--ie-arg) ie)))

(define (mle-xwidget-display-event ie)
  (cons 'xwidget-display-event ((force %--ie-arg) ie)))

(define (mle-file-notify-event ie)
  ;; FIX-WIN32: On W32 this would be
  ;; (file-notify DESCRIPTOR-ACTION-FILE CALLBACK)
  (cons 'file-notify ((force %--ie-arg) ie)))

;;; Dispatch table registration.
;;; Each register-kind! call maps a Lisp event symbol to its handler.
;;; When --ie-kind-from-name returns -1 the feature isn't compiled in
;;; and registration is silently skipped.

(register-kind! 'dbus-event mle-dbus-event)
(register-kind! 'thread-event mle-thread-event)
(register-kind! 'xwidget-event mle-xwidget-event)
(register-kind! 'xwidget-display-event mle-xwidget-display-event)
(register-kind! 'file-notify mle-file-notify-event)
