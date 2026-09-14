;;; minibuf.scm --- M34 imp-4: the minibuf.c input-state callers
;;;                 ((emacs minibuf))
;;;
;;; Moves the *decision* logic of the live src/minibuf.c call sites of
;;; keyboard extern stubs and of four stay-C names into Scheme.  The
;;; *mechanism* stays C: the run_exit_minibuf_hook dynwind block and the
;;; Fset_buffer, the temporarily_switch_to_single_kboard call, the
;;; minibuf_save_list conspairing, the stdin read and the expflag parse,
;;; the Ferase_buffer call, and the specbind_guile / dynwind blocks.  See
;;; brief.org 3, 4, 5.
;;;
;;; Nine exported procedures:
;;;
;;;   minibuf-run-exit-minibuffer-hook!  -- site 1 (src/minibuf.c:1129):
;;;                                         the minibuffer-exit-hook run.
;;;   minibuf-single-kboard-target       -- site 2 (:759): the frame value
;;;                                         handed to temporarily_switch_...
;;;   minibuf-unread-command-string      -- site 5.1a (:320): the drain.
;;;   minibuf-batch-unread-drain-p       -- site 5.1b (:696): the test.
;;;   minibuf-capture-help-state         -- site 5.2 (:768, :776).
;;;   minibuf-set-help-form!             -- site 5.2 (:798).
;;;   minibuf-restore-help-state!        -- site 5.2 (:1197, :1205).
;;;   minibuf-capture-deactivate-mark    -- site 5.3 (:1225).
;;;   minibuf-restore-deactivate-mark!   -- site 5.3 (:1227).
;;;
;;; The four names (unread-command-events, help-form, overriding-local-map,
;;; deactivate-mark) keep their C storage: other C files still read them.
;;; This module only reads and writes the same cells with symbol-value and
;;; set-symbol-value!.  The DEFVAR_* cell and the symbol value are the same
;;; object.  No DEFVAR_* site leaves C.  See brief.org 5.
;;;
;;; Conventions (identical to M9-M34, cf. mod/emacs/window.scm):
;;; cross-module targets are resolved lazily with delay + module-ref; #nil
;;; is elisp nil; no defelisp (the cross-module target is a Scheme
;;; procedure); no module-level mutable state.

(define-module (emacs minibuf)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (minibuf-run-exit-minibuffer-hook!
            minibuf-single-kboard-target
            minibuf-unread-command-string
            minibuf-batch-unread-drain-p
            minibuf-capture-help-state
            minibuf-set-help-form!
            minibuf-restore-help-state!
            minibuf-capture-deactivate-mark
            minibuf-restore-deactivate-mark!))

;; (emacs command-loop) holds the safe_run_hooks port.  Resolve it lazily,
;; so the module does not eagerly import (emacs command-loop).  See
;; brief.org 3.
(define %safe-run-hooks!
  (delay (module-ref (resolve-module '(emacs command-loop))
                     'safe-run-hooks!)))

;;; --- Helpers -------------------------------------------------------
;;; Each module carries its own copy.  See mod/emacs/frame.scm:48.
;;; Only truthy? is kept: every #nil case below is a symbol-value or a C
;;; value that tests truthiness, so an (eq? x #nil) helper has no caller
;;; (cr.org F8; cf. the (emacs frame) helper note).
;; Elisp truthiness: everything except #nil is true.
(define (truthy? x) (not (eq? x #nil)))

;;; --- minibuf-run-exit-minibuffer-hook! -----------------------------
;;; Port of the site-1 call in run_exit_minibuf_hook (src/minibuf.c:1129):
;;;   safe_run_hooks (Qminibuffer_exit_hook);
;;; Call (emacs command-loop) safe-run-hooks! on the minibuffer-exit-hook
;;; symbol.  Return nothing.  See brief.org 3.
(define (minibuf-run-exit-minibuffer-hook!)
  ((force %safe-run-hooks!) 'minibuffer-exit-hook))

;;; --- minibuf-single-kboard-target ----------------------------------
;;; Port of the site-2 argument in read_minibuf (src/minibuf.c:759):
;;;   temporarily_switch_to_single_kboard (XFRAME (mini_frame));
;;; The call is unconditional, so the movable decision is *which frame*.
;;; MINI-FRAME is the C mini_frame Lisp_Object passed in (Option A
;;; frame-value form, brief.org 4).  Return it so the C keeps its own
;;; temporarily_switch_to_single_kboard (XFRAME (target)) call.  The
;;; original C has no guard, so none is added.  mini_frame is always
;;; live: read_minibuf sets it to WINDOW_FRAME (XWINDOW (minibuf_window))
;;; (:800), and minibuf_window is only ever assigned a live frame's
;;; minibuffer window (choose_minibuf_frame :222; the frame helpers
;;; :303, :309, :337, :355).  (cr.org F3; the former frame-live-p guard
;;; was a behaviour deviation for a dead-but-valid frame.)
(define (minibuf-single-kboard-target mini-frame)
  mini-frame)

;;; --- minibuf-unread-command-string ---------------------------------
;;; Port of the site-5.1a drain in read_minibuf_noninteractive
;;; (src/minibuf.c:320): when executing-kbd-macro is non-nil and
;;; unread-command-events is a cons, pop fixnum events into a string and
;;; stop on newline (#\newline / 10) or carriage return (#\return / 13).
;;; Return the string, or #nil when the guard does not hold.  The C keeps
;;; the stdin read and the expflag parse.  See brief.org 5.1a.
;;; Two C-faithful details (cr.org F4): the event test is FIXNUMP, so a
;;; bignum event is skipped (the fixnum range test, not exact-integer?);
;;; and line[len++] = c truncates the int to 8 bits, so the char is
;;; (logand event #xFF).
(define (minibuf-unread-command-string)
  (if (and (truthy? (symbol-value 'executing-kbd-macro))
           (pair? (symbol-value 'unread-command-events)))
      (let loop ((evs (symbol-value 'unread-command-events))
                 (chars '()))
        (if (pair? evs)
            (let ((event (car evs)))
              ;; Consume the event first, exactly as the C does.
              (set-symbol-value! 'unread-command-events (cdr evs))
              (if (and (integer? event)
                       (<= most-negative-fixnum event most-positive-fixnum))
                  (if (or (= event 10) (= event 13))
                      (list->string (reverse chars))
                      (loop (cdr evs)
                            (cons (integer->char (logand event #xFF)) chars)))
                  (loop (cdr evs) chars)))
            (list->string (reverse chars))))
      #nil))

;;; --- minibuf-batch-unread-drain-p ----------------------------------
;;; Port of the site-5.1b clause in read_minibuf (src/minibuf.c:696):
;;;   (NILP (Vexecuting_kbd_macro)
;;;    || (!NILP (Vexecuting_kbd_macro) && CONSP (Vunread_command_events)))
;;; Return #t when executing-kbd-macro is nil, else #t only when
;;; unread-command-events is a cons; else #nil.  The C keeps the
;;; noninteractive / IS_DAEMON test.  See brief.org 5.1b.
(define (minibuf-batch-unread-drain-p)
  (if (truthy? (symbol-value 'executing-kbd-macro))
      (if (pair? (symbol-value 'unread-command-events)) #t #nil)
      #t))

;;; --- minibuf-capture-help-state ------------------------------------
;;; Port of the site-5.2 reads in read_minibuf (src/minibuf.c:768, :776):
;;;   Voverriding_local_map ... Vhelp_form ...
;;; Return the pair (help-form . overriding-local-map).  The C keeps the
;;; minibuf_save_list mechanism: it conses XCDR at the
;;; Voverriding_local_map position and XCAR at the Vhelp_form position, so
;;; the list order and the number of conses are unchanged
;;; (read_minibuf_unwind walks the list by position).  See brief.org 5.2.
(define (minibuf-capture-help-state)
  (cons (symbol-value 'help-form)
        (symbol-value 'overriding-local-map)))

;;; --- minibuf-set-help-form! ----------------------------------------
;;; Port of the site-5.2 set in read_minibuf (src/minibuf.c:798):
;;;   Vhelp_form = Vminibuffer_help_form;
;;; Read minibuffer-help-form and set help-form.  See brief.org 5.2.
(define (minibuf-set-help-form!)
  (set-symbol-value! 'help-form (symbol-value 'minibuffer-help-form)))

;;; --- minibuf-restore-help-state! -----------------------------------
;;; Port of the site-5.2 restores in read_minibuf_unwind
;;; (src/minibuf.c:1197, :1205): Vhelp_form = ... ; Voverriding_local_map
;;; = ... .  SAVED is the pair (help-form . overriding-local-map) that the
;;; C built from the two minibuf_save_list positions.  Set both cells.  See
;;; brief.org 5.2.
(define (minibuf-restore-help-state! saved)
  (set-symbol-value! 'help-form (car saved))
  (set-symbol-value! 'overriding-local-map (cdr saved)))

;;; --- minibuf-capture-deactivate-mark -------------------------------
;;; Port of the site-5.3 read in read_minibuf_unwind (src/minibuf.c:1225):
;;;   old_deactivate_mark = Vdeactivate_mark;
;;; Return the deactivate-mark value.  See brief.org 5.3.
(define (minibuf-capture-deactivate-mark)
  (symbol-value 'deactivate-mark))

;;; --- minibuf-restore-deactivate-mark! ------------------------------
;;; Port of the site-5.3 write in read_minibuf_unwind (src/minibuf.c:1227):
;;;   Vdeactivate_mark = old_deactivate_mark;
;;; Set deactivate-mark to MARK.  The C keeps Ferase_buffer, dynwind_begin,
;;; specbind_guile, and dynwind_end.  See brief.org 5.3.
(define (minibuf-restore-deactivate-mark! mark)
  (set-symbol-value! 'deactivate-mark mark))
