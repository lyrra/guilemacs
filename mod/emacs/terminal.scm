;;; terminal.scm --- M33 imp-1: the term.c TTY help/mouse consumers
;;;                     ((emacs terminal))
;;;
;;; Moves the *decision* logic of the TTY menu help/mouse paths out of
;;; src/term.c and into Scheme.  The C *mechanism* stays in term.c: the
;;; menu select loop, the terminal struct walk, and the raw
;;; read_socket_hook pointer.  See docs/m33-plan.org A4.
;;;
;;; Three exported procedures:
;;;
;;;   tty-menu-clear-help!           -- src/term.c:3432-3434, the
;;;                                     MI_QUIT_MENU arm.
;;;   tty-menu-help-callback         -- src/term.c:3600-3620, the
;;;                                     tty_menu_help_callback body.
;;;   tty-menu-discard-mouse-events! -- src/term.c:3566-3568.
;;;
;;; The frame help path (src/term.c:3536-3546) is the fn-pointer wiring
;;; at src/term.c:3920; the tty_menu_help_callback port below covers it.
;;; Its condition reads only term.c-local statics (menu_help_message,
;;; prev_menu_help_message), so no fourth dispatcher is added.  See
;;; brief.org 5.4.  Confirmed reading: see cr.org F1.
;;;
;;; Two known, harmless divergences from the C body are recorded here
;;; for a future reader (cr.org F2, F3).  Both keep today's behavior.
;;;
;;;   F2.  The C body used CHECK_TYPE (PLAIN_VECTORP (menu_vec), ...).
;;;        PLAIN_VECTORP rejects pseudovectors (src/lisp.h).  The
;;;        %vectorp subr below uses VECTOR_OR_PSEUDOVECTORP (src/data.c),
;;;        so it also accepts a pseudovector.  menu_items is always a
;;;        plain vector, so the result is the same today.  No fix: the
;;;        module has no plain-vector predicate, and a new one would
;;;        grow the C surface.
;;;   F3.  The C body used empty_unibyte_string for the Qquote arm.  The
;;;        "" literal below can cross as a multibyte string.  The value
;;;        is empty, so the help-echo path does not change.
;;;
;;; Conventions (identical to M9-M32): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp list/vector values built with
;;; the plain Scheme cons and integers (a guilemacs Scheme integer is an
;;; elisp fixnum); #nil is elisp nil; no module-level mutable state.

(define-module (emacs terminal)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (tty-menu-clear-help!
            tty-menu-help-callback
            tty-menu-discard-mouse-events!))

;;; --- C shim references ---------------------------------------------
;; --menu-items and --clear-input-pending! are the two new M33 imp-1
;; keyboard.c primitives: the module must read the menu_items vector and
;; clear the input-pending flag (src/keyboard.c:9390).
(defelisp %--menu-items           --menu-items)
(defelisp %--clear-input-pending! --clear-input-pending!)
(defelisp %aref                   aref)
(defelisp %vectorp                vectorp)
(defelisp %signal                 signal)

;;; --- lazy cross-module targets -------------------------------------
;; Resolve the two cross-module procedures lazily, like gobble.scm does
;; for (emacs kbd-buffer): an eager import of (emacs help-echo) pulls in
;; (emacs kbd-buffer) -> (emacs lispy-event), which is not loadable at
;; this boot point.  (emacs terminal) is boot-loaded, so both stay lazy.
(define %show-help-echo
  (delay (module-ref (resolve-module '(emacs help-echo)) 'show-help-echo)))
(define %kbd-buffer-discard-mouse-events!
  (delay (module-ref (resolve-module '(emacs kbd-buffer))
                     'kbd-buffer-discard-mouse-events!)))
(define %kbd-buffer-events-waiting
  (delay (module-ref (resolve-module '(emacs kbd-buffer))
                     'kbd-buffer-events-waiting)))


;;; --- C enum constants (src/keyboard.h:359-366) ---------------------
;; MENU_ITEMS_PANE_NAME and MENU_ITEMS_ITEM_NAME are integer enum
;; constants in src/keyboard.h, which src/term.c includes.
(define %menu-items-pane-name 1)   ; MENU_ITEMS_PANE_NAME
(define %menu-items-item-name 0)   ; MENU_ITEMS_ITEM_NAME

;;; --- helpers -------------------------------------------------------
(define (truthy? x)
  "Elisp truthiness: everything except #nil is true."
  (not (eq? x #nil)))

(define (Qt? x)
  "True when X is the elisp symbol t.  Some paths pass the Guile
boolean #t for the same value; see (emacs command-loop)."
  (or (eq? x #t) (eq? x 't)))

;;; --- tty-menu-clear-help! ------------------------------------------
;;; Port of the MI_QUIT_MENU arm (src/term.c:3432-3434): remove the last
;;; help-echo, so that it does not re-appear after "Quit".
(define (tty-menu-clear-help!)
  ((force %show-help-echo) #nil #nil #nil #nil)
  #nil)

;;; --- tty-menu-discard-mouse-events! --------------------------------
;;; Port of src/term.c:3566-3568: discard any mouse events waiting in the
;;; Emacs event queue, then clear the input-pending flag when no real
;;; event waits.  clear_input_pending stays C; the module reads it
;;; through the new --clear-input-pending! primitive.
(define (tty-menu-discard-mouse-events!)
  ((force %kbd-buffer-discard-mouse-events!))
  (unless (truthy? ((force %kbd-buffer-events-waiting)))
    ((force %--clear-input-pending!)))
  #nil)

;;; --- tty-menu-help-callback ----------------------------------------
;;; Port of the tty_menu_help_callback body (src/term.c:3600-3620).
;;; HELP-STRING is a Scheme string or #nil; PANE and ITEM are fixnums.
;;; The list3 and make_fixnum calls in the C body build the
;;; (menu-item MENU-NAME PANE-NUMBER) form and the fixnum slots; the
;;; plain Scheme list and integers below are the same elisp values.
(define (tty-menu-help-callback help-string pane item)
  (let ((menu-vec ((force %--menu-items))))
    ;; CHECK_TYPE (PLAIN_VECTORP (menu_vec), Qvectorp, menu_vec).  Note
    ;; F2 in the header: %vectorp is a little looser than PLAIN_VECTORP.
    (unless (truthy? ((force %vectorp) menu-vec))
      ((force %signal) 'wrong-type-argument (list 'vectorp menu-vec)))
    (let* ((slot0 ((force %aref) menu-vec 0))
           (pane-name
            (cond
             ((Qt? slot0)
              ((force %aref) menu-vec %menu-items-pane-name))
             ((eq? slot0 'quote)
              ;; This should not happen; see xmenu_show.  Note F3 in the
              ;; header: the C used empty_unibyte_string here.
              "")
             (else
              ((force %aref) menu-vec %menu-items-item-name))))
           ;; (menu-item MENU-NAME PANE-NUMBER)
           (menu-object (list 'menu-item pane-name pane)))
      ((force %show-help-echo) help-string #nil menu-object item))))
