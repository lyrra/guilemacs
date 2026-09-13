;;; pgtk.scm --- M33 imp-5: the pgtkterm.c read path
;;;               ((emacs pgtk))
;;;
;;; Moves the *decision* logic of the src/pgtkterm.c read path out of C
;;; and into Scheme.  The C *mechanism* stays C: the frame conversion
;;; (XSETFRAME), the help_echo_string = Qnil assignment, the
;;; pgtk_emacs_to_gtk_modifiers conversion, the do_help computation,
;;; the any_help_event_p flag, the gen_help_event calls, the scroll
;;; accumulator, and the two fabs tests.  See docs/m33-plan.org A2 ...
;;; A5 and brief.org 4.
;;;
;;; Four exported procedures:
;;;
;;;   pgtk-clear-help-echo? -- src/pgtkterm.c:5483 and :5767, the help
;;;                            echo clear guards of configure_event and
;;;                            leave_notify_event.
;;;   pgtk-help-event-action -- src/pgtkterm.c:5986, the show-help
;;;                            decision of motion_notify_event.
;;;   pgtk-extra-keyboard-modifiers -- src/pgtkterm.c:5270, the fixnum
;;;                            mask read of key_press_event.
;;;   pgtk-mwheel-coalesce-scroll-events? -- src/pgtkterm.c:6229 and
;;;                            :6266, the boolean read of scroll_event.
;;;
;;; Port principle (brief.org 4): the module decides the *outcome*.  The
;;; C forms the arguments of its own gen_help_event call, because
;;; help_echo_string, help_echo_window, help_echo_object, and
;;; help_echo_pos are C globals owned by src/xdisp.c.  The module must
;;; not read or write them.
;;;
;;; pgtk-clear-help-echo? takes a C bool and returns a plain Scheme
;;; boolean.  The C keeps the mechanism: the XSETFRAME conversion, the
;;; assignment help_echo_string = Qnil, and the gen_help_event (Qnil,
;;; frame, Qnil, Qnil, 0) call.
;;;
;;; Conventions (identical to M9-M33): a guilemacs Scheme integer is an
;;; elisp fixnum; #nil is elisp nil; no module-level mutable state.  The
;;; module adds no C primitive.  It reads the two name cells with the
;;; delayed (emacs-elisp runtime) symbol-value.  It needs no
;;; --detect-input-pending: pgtkterm.c has no XTflash analogue.

(define-module (emacs pgtk)
  #:use-module (emacs elisp-ref)      ; defelisp
  #:use-module (emacs-elisp runtime)  ; symbol-value
  #:declarative? #t
  #:export (pgtk-clear-help-echo?
            pgtk-help-event-action
            pgtk-extra-keyboard-modifiers
            pgtk-mwheel-coalesce-scroll-events?))

;;; --- delayed C references ------------------------------------------
;;; The two names are cell readers.  The C keeps the mechanism.
(defelisp %symbol-value symbol-value)

;;; --- Helpers -------------------------------------------------------
;;; Each module carries its own copy.  See mod/emacs/recent-keys.scm:38.
(define (truthy? x)
  "Elisp truthiness: everything except #nil is true."
  (not (eq? x #nil)))

;;; --- pgtk-clear-help-echo? -----------------------------------------
;;; Port of the guards at src/pgtkterm.c:5483 and :5767.  Return true
;;; when the C must clear the help echo.  The C passes a C bool, so the
;;; argument arrives as a Scheme boolean.  Return it unchanged: do NOT
;;; use truthy? here, because a Scheme #f is not elisp #nil, so truthy?
;;; would return #t for a false argument.  brief.org 4.
(define (pgtk-clear-help-echo? any-help-p)
  any-help-p)

;;; --- pgtk-help-event-action ----------------------------------------
;;; Port of the guard at src/pgtkterm.c:5986.  Return 1 when do-help is
;;; positive, else 0.  The C passes a C int, so the argument is an
;;; elisp fixnum.  The C keeps the mechanism: it computes do-help from
;;; help_echo_string and previous_help_echo_string, because those
;;; globals belong to src/xdisp.c.  The module must not read them.  The
;;; C also keeps any_help_event_p = true and the gen_help_event call.
;;; brief.org 4.
(define (pgtk-help-event-action do-help)
  (if (> do-help 0) 1 0))

;;; --- pgtk-extra-keyboard-modifiers ---------------------------------
;;; Port of the read at src/pgtkterm.c:5270.  Return the fixnum mask.
;;; The C keeps pgtk_emacs_to_gtk_modifiers and converts with
;;; scm_to_intmax, as src/xterm.c does.  brief.org 4.
(define (pgtk-extra-keyboard-modifiers)
  ((force %symbol-value) 'extra-keyboard-modifiers))

;;; --- pgtk-mwheel-coalesce-scroll-events? ---------------------------
;;; Port of the reads at src/pgtkterm.c:6229 and :6266.  Return a plain
;;; Scheme boolean.  The C keeps the accumulator, the two fabs tests,
;;; and the branch bodies.  brief.org 4.
(define (pgtk-mwheel-coalesce-scroll-events?)
  (truthy? ((force %symbol-value) 'mwheel-coalesce-scroll-events)))
