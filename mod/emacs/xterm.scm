;;; xterm.scm --- M33 imp-3: the xterm.c help-event decision
;;;                  ((emacs xterm))
;;;
;;; Moves the *decision* logic of the handle_one_xevent help path out
;;; of src/xterm.c and into Scheme.  The C *mechanism* stays C: the
;;; frame conversion (XSETFRAME), the input-pending flag
;;; (any_help_event_p), the XInput2 interaction call
;;; (xi_handle_interaction), the gen_help_event calls, and the event
;;; count.  See docs/m33-plan.org A2 ... A3 and brief.org 3.
;;;
;;; One exported procedure:
;;;
;;;   x-help-event-action -- src/xterm.c:25629-25657, the three-way
;;;                          choice of the help block in
;;;                          handle_one_xevent.
;;;
;;; Port principle (brief.org 3): the module decides the *outcome*.  The
;;; C forms the arguments of its own gen_help_event call, because
;;; help_echo_string, help_echo_window, help_echo_object, and
;;; help_echo_pos are C globals owned by src/xdisp.c.  The module must
;;; not read or write them.
;;;
;;; The result is a plain fixnum.  The C dispatcher in src/xterm.c
;;; switches on it, so the ABI types stay C.  This is the
;;; "argument-forming split" of M33 imp-2, applied to a 3-way choice.
;;;
;;;   0 -- no help event: skip the block.
;;;   1 -- show help echo: C sets any_help_event_p and calls
;;;        gen_help_event with the help values.
;;;   2 -- clear help echo: C clears help_echo_string and calls
;;;        gen_help_event with Qnil.
;;;
;;; Conventions (identical to M9-M33): a guilemacs Scheme integer is an
;;; elisp fixnum; #nil is elisp nil; no module-level mutable state.
;;; The module has no C primitive and no cross-module reference.

(define-module (emacs xterm)
  #:declarative? #t
  #:export (x-help-event-action))

;;; --- x-help-event-action -------------------------------------------
;;; Port of the help decision at src/xterm.c:25629-25630 and
;;; :25639-25655.  DO-HELP is a fixnum: 0 means "no help", a positive
;;; value means "show help", and a negative value means "clear help".
;;; HOLD-QUIT-P is a Scheme boolean: true when the caller holds a real
;;; quit event.  A held quit event overrides a positive DO-HELP, so the
;;; block is skipped.  Return 0, 1, or 2.
(define (x-help-event-action do-help hold-quit-p)
  ;; 0 = no help event, 1 = show, 2 = clear.  See brief.org 3.
  (cond
   ((= do-help 0) 0)
   (hold-quit-p 0)
   ((> do-help 0) 1)
   (else 2)))
