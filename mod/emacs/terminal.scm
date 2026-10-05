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
            tty-menu-discard-mouse-events!
            ;; M48 imp-2 -- G1, the terminal-capability policy
            term-display-color-p
            term-display-color-cells
            term-type
            term-controlling-tty-p
            ;; M48 imp-2 -- G3, the query / geometry policy
            term-frame-geometry
            term-frame-edges
            term-display-pixel-width
            term-display-pixel-height))

;;; --- C shim references ---------------------------------------------
;; --menu-items and --clear-input-pending! are the two new M33 imp-1
;; keyboard.c primitives: the module must read the menu_items vector and
;; clear the input-pending flag (src/keyboard.c:9390).
(defelisp %--menu-items           --menu-items)
(defelisp %--clear-input-pending! --clear-input-pending!)
(defelisp %aref                   aref)
(defelisp %vectorp                vectorp)
(defelisp %signal                 signal)

;;; --- M48 imp-2: the typed C --term-* leaves ------------------------
;; One delayed reference per leaf of src/term.c (brief.org section 5).
;; The leaf name is the contract: imp-3 / imp-4 look the *wrapper* up
;; with (scm_c_public_ref "emacs terminal" "term-<block>").
(defelisp %--term-display-color-p       --term-display-color-p)
(defelisp %--term-display-color-cells   --term-display-color-cells)
(defelisp %--term-type                  --term-type)
(defelisp %--term-controlling-tty-p     --term-controlling-tty-p)
;; imp-6 deleted --term-frame-geometry and --term-frame-edges: the
;; geometry arithmetic is Scheme now, so no leaf reference remains.
(defelisp %--term-display-pixel-width   --term-display-pixel-width)
(defelisp %--term-display-pixel-height  --term-display-pixel-height)

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

;;; --- M48 imp-2: the thin wrappers over the typed C --term-* leaves -
;;; One wrapper per leaf of src/term.c (brief.org section 5).  A wrapper
;;; is a one-line call to its leaf; the module holds no policy, no FFI
;;; call, and no raw syscall.  imp-2 adds wrappers only; imp-3 (G1) and
;;; imp-4 (G3) look these up with
;;; (scm_c_public_ref "emacs terminal" "term-<block>").

(define (term-display-color-p colors)
  ((force %--term-display-color-p) colors))

(define (term-display-color-cells colors)
  ((force %--term-display-color-cells) colors))

(define (term-type type)
  ((force %--term-type) type))

(define (term-controlling-tty-p name dev-tty)
  ((force %--term-controlling-tty-p) name dev-tty))

;;; --- M48 imp-6: the G3 geometry arithmetic, in Scheme --------------
;;; Port of the static C helper term_frame_geometry_1 of src/term.c.
;;; Until imp-6 the two wrappers below called the typed C leaves
;;; --term-frame-geometry and --term-frame-edges, which called that C
;;; helper: the decision never left C (docs/m48-port-review.org).  The
;;; arithmetic is HERE now, and the C helper and both leaves are gone.
;;;
;;; The C hub keeps the mechanism: decode_live_frame, the
;;; FRAME_INITIAL_P / FRAME_TTY guard, every C-owned frame field read,
;;; the alist build, and the FRAME_TOOL_BAR_POSITION read (the symbol
;;; rule).  Only plain integers, a plain boolean, and a plain string
;;; cross the layer.
;;;
;;; The native edges equal the outer edges on a tty, so they are not
;;; separate values: EDGE-TYPE "inner" selects the inner 4-tuple, and
;;; every other value (including "outer" and nil) selects the outer one.

(define (term--integer x)
  "Fold a non-integer argument to 0.  The deleted C leaf did this with
FIXNUMP, and the C hub passes fixnums only, so this keeps a direct
Scheme caller from turning a bad argument into an error."
  (if (integer? x) x 0))

(define (term--true? x)
  "Elisp truthiness for a flag that crosses the layer.  This differs
from `truthy?' on one value: the Guile #f.  The C hub passes Qt or
Qnil, but a Scheme caller may pass #f, and #f must read as false."
  (not (or (eq? x #nil) (eq? x #f))))

(define (term--frame-geometry-values left top width height ibw
                                     menu-bar-height tab-bar-height
                                     tool-bar-height tool-bar-on-top)
  "The 11 derived geometry integers of a tty frame, as a plain list:
 (OUTER-LEFT OUTER-TOP OUTER-RIGHT OUTER-BOTTOM
  INNER-LEFT INNER-TOP INNER-RIGHT INNER-BOTTOM
  MENU-BAR-WIDTH TAB-BAR-WIDTH TOOL-BAR-WIDTH).
A bar contributes its width only when its height is not 0, and the
tool bar moves the inner top or the inner bottom by its position."
  (let* ((left   (term--integer left))
         (top    (term--integer top))
         (width  (term--integer width))
         (height (term--integer height))
         (ibw    (term--integer ibw))
         (menu-bar-height (term--integer menu-bar-height))
         (tab-bar-height  (term--integer tab-bar-height))
         (tool-bar-height (term--integer tool-bar-height))
         (on-top?         (term--true? tool-bar-on-top))
         (outer-left   left)
         (outer-top    top)
         (outer-right  (+ left width))
         (outer-bottom (+ top height))
         (inner-left   (+ outer-left ibw))
         (inner-right  (- outer-right ibw))
         (inner-top    (+ outer-top ibw menu-bar-height tab-bar-height
                          (if on-top? tool-bar-height 0)))
         (inner-bottom (- outer-bottom ibw
                          (if on-top? 0 tool-bar-height)))
         ;; a tab bar and a tool bar span the native width inside the
         ;; border; a menu bar spans the whole native width.
         (bar-width    (- width (* 2 ibw))))
    (list outer-left outer-top outer-right outer-bottom
          inner-left inner-top inner-right inner-bottom
          (if (zero? menu-bar-height) 0 width)
          (if (zero? tab-bar-height)  0 bar-width)
          (if (zero? tool-bar-height) 0 bar-width))))

(define (term-frame-geometry left top width height ibw
                             menu-bar-height tab-bar-height
                             tool-bar-height tool-bar-on-top)
  (term--frame-geometry-values left top width height ibw
                               menu-bar-height tab-bar-height
                               tool-bar-height tool-bar-on-top))

(define (term-frame-edges left top width height ibw
                          menu-bar-height tab-bar-height
                          tool-bar-height tool-bar-on-top edge-type)
  (let* ((vals (term--frame-geometry-values left top width height ibw
                                            menu-bar-height tab-bar-height
                                            tool-bar-height tool-bar-on-top))
         (inner? (and (string? edge-type) (string=? edge-type "inner")))
         (edges  (if inner? (list-tail vals 4) vals)))
    (list (list-ref edges 0) (list-ref edges 1)
          (list-ref edges 2) (list-ref edges 3))))

(define (term-display-pixel-width initial width)
  ((force %--term-display-pixel-width) initial width))

(define (term-display-pixel-height initial height)
  ((force %--term-display-pixel-height) initial height))
