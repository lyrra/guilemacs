;;; xterm.scm --- M33 imp-3/imp-4: the xterm.c help decision, the
;;;                  input test, and 2 name readers
;;;                  ((emacs xterm))
;;;
;;; Moves the *decision* logic of the handle_one_xevent help path out
;;; of src/xterm.c and into Scheme.  The C *mechanism* stays C: the
;;; frame conversion (XSETFRAME), the input-pending flag
;;; (any_help_event_p), the XInput2 interaction call
;;; (xi_handle_interaction), the gen_help_event calls, and the event
;;; count.  See docs/m33-plan.org A2 ... A3 and brief.org 3.
;;;
;;; Four exported procedures:
;;;
;;;   x-help-event-action -- src/xterm.c:25629-25657, the three-way
;;;                          choice of the help block in
;;;                          handle_one_xevent.
;;;   x-input-pending?     -- src/xterm.c:11603, the input test of
;;;                          XTflash.  brief.org 3.
;;;   x-extra-keyboard-modifiers -- src/xterm.c:20363 and :24261, the
;;;                          fixnum mask read.  brief.org 4.1.
;;;   x-mwheel-coalesce-scroll-events? -- src/xterm.c:22829, the
;;;                          boolean read.  brief.org 4.2.
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
;;; The module adds no C primitive.  It reads the 2 name cells with the
;;; delayed (emacs-elisp runtime) symbol-value and the input state with
;;; (emacs kbd-buffer) detect-input-pending?, resolved lazily.

(define-module (emacs xterm)
  #:use-module (emacs elisp-ref)      ; defelisp
  #:use-module (emacs-elisp runtime)  ; symbol-value
  #:declarative? #t
  #:export (x-help-event-action
            x-input-pending?
            x-extra-keyboard-modifiers
            x-mwheel-coalesce-scroll-events?))

;;; --- delayed C references ------------------------------------------
;;; The 2 names are cell readers.  The C keeps the mechanism.
(defelisp %symbol-value           symbol-value)

;; M36 imp-2: the input test moved to (emacs kbd-buffer).  Resolve it
;; lazily, like the other cross-module targets.
(define %detect-input-pending?
  (delay (module-ref (resolve-module '(emacs kbd-buffer))
                     'detect-input-pending?)))

;;; --- Helpers -------------------------------------------------------
;;; Each module carries its own copy.  See mod/emacs/recent-keys.scm:38.
(define (truthy? x)
  "Elisp truthiness: everything except #nil is true."
  (not (eq? x #nil)))

;;; --- x-input-pending? ----------------------------------------------
;;; Port of the input test at src/xterm.c:11603 in XTflash.  Return #t
;;; when input events are pending.  The primitive returns elisp t or
;;; elisp nil, so normalize with truthy?.  The C keeps the loop: the
;;; current_timespec read, the timespec_cmp test, the FD_ZERO / FD_SET
;;; build, the timeout, and the pselect call.  brief.org 3.
(define (x-input-pending?)
  (truthy? ((force %detect-input-pending?))))

;;; --- x-extra-keyboard-modifiers ------------------------------------
;;; Port of the reads at src/xterm.c:20363 and :24261.  Return the
;;; fixnum mask.  The C keeps x_emacs_to_x_modifiers.  brief.org 4.1.
(define (x-extra-keyboard-modifiers)
  ((force %symbol-value) 'extra-keyboard-modifiers))

;;; --- x-mwheel-coalesce-scroll-events? ------------------------------
;;; Port of the read at src/xterm.c:22829.  Return a plain Scheme
;;; boolean.  The C keeps the 2 fabs tests.  brief.org 4.2.
(define (x-mwheel-coalesce-scroll-events?)
  (truthy? ((force %symbol-value) 'mwheel-coalesce-scroll-events)))

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
