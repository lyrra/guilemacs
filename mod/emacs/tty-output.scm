;;; tty-output.scm --- M52 imp-3: the src/term.c TTY output boundary
;;;                     ((emacs tty-output))
;;;
;;; M52 imp-3 defines the boundary of the src/term.c TTY output path.
;;; It moves NO policy: the selection of the capability string and the
;;; cursor / scroll / clear arithmetic stay in C until imp-4.  This
;;; module holds the 4 thin wrappers over the 4 typed C leaves only.
;;;
;;; The C leaves (src/term.c):
;;;
;;;   (%--tty-emit-cap   device cap args) -> a fixnum byte count, or a
;;;        negative fixnum holding the negated errno
;;;   (%--tty-write-bytes device bytevector) -> the same shape
;;;   (%--tty-flush       device)          -> 0, or a negated errno
;;;   (%--tty-emit-seq    device seq)      -> the total byte count
;;;
;;; Every value that crosses the layer is plain: the DEVICE is an opaque
;;; handle (a terminal object, a frame, or nil), the CAP key is a plain
;;; string, the ARGS is a plain fixnum list, and the SEQ is a plain list
;;; of (cap . args) items.  No Lisp_Object, char *, FILE *, or struct
;;; crosses the layer (the M42 rule).  The C-owned FILE *output and
;;; FILE *termscript streams stay in C; C stays the single writer.  A
;;; Guile port must NOT own a C-owned FILE * stream (docs/kb.org
;;; =passthrough-leaf-is-not-a-port=).
;;;
;;; The module is a NEW module.  The sibling (emacs terminal) owns the
;;; M48 display queries and the M33 menu consumers, and (emacs tty-modes)
;;; owns the termios mode policy in src/sysdep.c.  A new module does not
;;; extend a sibling.  It holds no policy, no FFI call, and no public
;;; ref site yet (the FFI bridge comes at imp-4).
;;;
;;; The cleanup contract (brief.org section 6, the leaf rules) is a leaf
;;; property:
;;;   - A SHORT WRITE: the C leaf reports the fwrite count to Scheme, so
;;;     Scheme decides retry / give-up.  C keeps the =clearerr=.
;;;   - EINTR / EAGAIN: the fwrite path does not handle them today; the
;;;     tcdrain drain retries EINTR (src/sysdep.c).  A leaf returns the
;;;     negated errno on a hard failure.
;;;   - EOF: not applicable to output.
;;;   - CLOSE: C closes the streams.  Scheme never closes them.
;;;
;;; The padding note (cr1.org F3, for imp-4): the real termcap output
;;; path is the C OUTPUT macro, which calls emacs_tputs and applies
;;; padding.  The leaf m52_tty_emit_cap_1 calls tparam and a raw
;;; fwrite, so it does NOT apply padding.  imp-3 rewires nothing, so
;;; there is no regression today.  When imp-4 moves the output policy,
;;; it MUST NOT lose the padding behaviour: either call emacs_tputs, or
;;; record the padding decision in docs/m52-plan.org.
;;;
;;; Conventions (identical to M9-M51): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp nil is #nil; no module-level
;;; mutable state.

(define-module (emacs tty-output)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (tty-emit-cap tty-write-bytes tty-flush tty-emit-seq
            tty-turn-on-insert-cap tty-turn-off-insert-cap
            tty-turn-off-highlight-cap tty-turn-on-highlight-cap
            tty-toggle-highlight-cap
            tty-ring-bell-cap tty-hide-cursor-cap tty-show-cursor-cap
            tty-background-highlight-cap tty-highlight-if-desired-cap
            tty-update-end-steps
            tty-set-terminal-modes-steps tty-reset-terminal-modes-steps
            tty-cursor-to-steps tty-raw-cursor-to-steps
            tty-clear-to-end-steps tty-clear-frame-steps
            tty-clear-end-of-line-steps
            tty-set-terminal-window-steps tty-set-scroll-region-steps
            tty-delete-glyphs-steps tty-ins-del-lines-steps))

;; The typed C leaves of src/term.c.
(defelisp %--tty-emit-cap   --tty-emit-cap)
(defelisp %--tty-write-bytes --tty-write-bytes)
(defelisp %--tty-flush      --tty-flush)
(defelisp %--tty-emit-seq   --tty-emit-seq)

;; Emit one termcap capability of DEVICE.  DEVICE is an opaque handle;
;; CAP is a plain string naming one TS_* capability; ARGS is a plain
;; fixnum list applied through tparam.  Return the leaf's plain fixnum:
;; the byte count, or a negative fixnum holding the negated errno.
(define (tty-emit-cap device cap args)
  ((force %--tty-emit-cap) device cap args))

;; Write the plain bytevector BYTES to DEVICE's output and termscript
;; streams (the bell / newline path).  Return the leaf's plain fixnum:
;; the byte count, or a negated errno.
(define (tty-write-bytes device bytes)
  ((force %--tty-write-bytes) device bytes))

;; Flush the C-owned output stream of DEVICE.  Return the leaf's plain
;; fixnum: 0 on success, or a negated errno.
(define (tty-flush device)
  ((force %--tty-flush) device))

;; Apply one ordered sequence SEQ of (CAP . ARGS) items to DEVICE.  This
;; is the thin entry point; it adds no policy.  Return the leaf's plain
;; fixnum: the total byte count, or a negated errno.
(define (tty-emit-seq device seq)
  ((force %--tty-emit-seq) device seq))

;; --- M52 imp-4: the insert / highlight state-flip policy --------------
;;
;; Each procedure holds the DECISION of one src/term.c hub: given the
;; plain C state flag (a fixnum, 0 or 1) it returns the plain capability
;; KEY string to emit, or #nil when the hub must emit nothing.  The
;; selection is pure: a procedure calls no leaf and emits nothing
;; (docs/kb.org =leaf-must-call-the-mechanism=).  Each returned key MUST
;; match a m52_caps key byte for byte; a key that does not match makes
;; m52_cap_string_1 return NULL, so the hub emits nothing (a silent byte
;; change).  C owns the state write and the OUTPUT / OUTPUT_IF call.

;; tty_turn_on_insert: emit only when insert-mode is off.
(define (tty-turn-on-insert-cap insert-mode)
  (if (zero? insert-mode) "insert-mode" #nil))

;; tty_turn_off_insert: emit only when insert-mode is on.
(define (tty-turn-off-insert-cap insert-mode)
  (if (zero? insert-mode) #nil "end-insert-mode"))

;; tty_turn_off_highlight: emit only when standout-mode is on.
(define (tty-turn-off-highlight-cap standout-mode)
  (if (zero? standout-mode) #nil "end-standout-mode"))

;; tty_turn_on_highlight: emit only when standout-mode is off.
(define (tty-turn-on-highlight-cap standout-mode)
  (if (zero? standout-mode) "standout-mode" #nil))

;; tty_toggle_highlight: the two-way flip.  Choose the direction from the
;; plain flag and return that direction's key (never #nil).
(define (tty-toggle-highlight-cap standout-mode)
  (if (zero? standout-mode) "standout-mode" "end-standout-mode"))

;; --- M52 imp-5: the bell / cursor / update-end policy -----------------
;;
;; Each procedure holds the DECISION of one src/term.c hub.  The shape is
;; the imp-4 shape: a pure procedure over plain fixnum flags returns a
;; plain capability KEY (or an ordered KEY list, or #nil).  A procedure
;; calls no leaf and emits nothing (docs/kb.org
;; =leaf-must-call-the-mechanism=).  Every returned KEY MUST match a
;; m52_caps key byte for byte; a key that does not match makes
;; m52_cap_string_1 return NULL, so the hub emits nothing (a silent byte
;; change).  C owns the state write and the OUTPUT / OUTPUT_IF call.

;; tty_ring_bell: pick "visible-bell" when the user option visible_bell
;; is on AND the terminal holds a visible-bell capability; else "bell".
;; It never returns #nil.
(define (tty-ring-bell-cap visible-bell has-visible-bell)
  (if (and (not (zero? visible-bell)) (not (zero? has-visible-bell)))
      "visible-bell" "bell"))

;; tty_hide_cursor: hide only when the cursor is not already hidden.  The
;; #nil case means "emit nothing" (the C hub tests the whole list).
(define (tty-hide-cursor-cap cursor-hidden)
  (if (zero? cursor-hidden) (list "cursor-invisible") #nil))

;; tty_show_cursor: show only when the cursor is hidden.  "cursor-normal"
;; always; add "cursor-visible" when the user option visible_cursor is on.
;; The #nil case means "emit nothing".
(define (tty-show-cursor-cap cursor-hidden visible-cursor)
  (if (zero? cursor-hidden)
      #nil
      (if (zero? visible-cursor)
          (list "cursor-normal")
          (list "cursor-normal" "cursor-visible"))))

;; tty_background_highlight: the standout direction for empty space.
;; Never #nil.
(define (tty-background-highlight-cap inverse-video)
  (if (zero? inverse-video) "end-standout-mode" "standout-mode"))

;; tty_highlight_if_desired: the standout direction for the text.  Never
;; #nil.
(define (tty-highlight-if-desired-cap inverse-video)
  (if (zero? inverse-video) "end-standout-mode" "standout-mode"))

;; tty_update_end: the ordered step list.  The "show-cursor" step is
;; present only when the selected window's cursor_off_p is 0; the two
;; other steps are always present.
(define (tty-update-end-steps cursor-off-p)
  (if (zero? cursor-off-p)
      (list "show-cursor" "off-insert" "background")
      (list "off-insert" "background")))

;; --- M52 imp-6: the terminal-mode / cursor-motion policy -------------
;;
;; Each procedure holds the DECISION of one src/term.c hub.  A procedure
;; returns an ordered step list, or #nil.  Two step kinds exist; C tells
;; them apart with STRINGP:
;;
;;   - KEY step: a plain string.  It names one m52_caps key.  C resolves
;;     it with m52_cap_string_1 and emits it through OUTPUT_IF.
;;   - MARKER step: a plain list (TAG ARG...).  TAG is a plain string;
;;     C runs the matching mechanism.  A marker carries plain fixnum data
;;     only, so the newline count and the cmgoto target cross the layer.
;;
;; A procedure calls no leaf and emits nothing (docs/kb.org
;; =leaf-must-call-the-mechanism=).  Every KEY string MUST match a
;; m52_caps key byte for byte; a key that does not match makes
;; m52_cap_string_1 return NULL, so the hub emits nothing (a silent byte
;; change).  C owns the state write, the FILE * streams, and the
;; OUTPUT / OUTPUT_IF padding.

;; tty_set_terminal_modes: the setup order.  termcap-modes OR newlines,
;; then the cursor key, then the keypad key.
(define (tty-set-terminal-modes-steps has-termcap-modes total-lines visible-cursor)
  (list (if (zero? has-termcap-modes)
            (list "newlines" total-lines)   ; MARKER
            "termcap-modes")                ; KEY
        (if (zero? visible-cursor) "cursor-normal" "cursor-visible")
        "keypad-mode"))

;; tty_reset_terminal_modes: the fixed reset order.  No flag.
(define (tty-reset-terminal-modes-steps)
  (list "end-keypad-mode" "cursor-normal" "end-termcap-modes" "orig-pair"
        (list "raw-cr")))

;; tty_cursor_to: #nil on no move, else the conditional resets plus the
;; move marker.
(define (tty-cursor-to-steps cur-y cur-x vpos hpos standout-motion insmode-motion)
  (if (and (= cur-y vpos) (= cur-x hpos))
      #nil
      (append (if (zero? standout-motion) (list (list "background")) '())
              (if (zero? insmode-motion) (list (list "off-insert")) '())
              (list (list "move" vpos hpos)))))

;; tty_raw_cursor_to: the same shape, with the target ROW / COL.
(define (tty-raw-cursor-to-steps cur-y cur-x row col standout-motion insmode-motion)
  (if (and (= cur-y row) (= cur-x col))
      #nil
      (append (if (zero? standout-motion) (list (list "background")) '())
              (if (zero? insmode-motion) (list (list "off-insert")) '())
              (list (list "move" row col)))))

;; --- M52 imp-7: the clear policy -------------------------------------
;;
;; Each procedure holds the DECISION of one src/term.c clear hub.  A
;; procedure returns ONE step, or #nil for "do nothing".  The two step
;; kinds match imp-6:
;;
;;   - KEY step: a plain string that names one m52_caps key.  C resolves
;;     it with m52_cap_string_1 and emits it through OUTPUT / OUTPUT1.
;;   - MARKER step: a plain list (TAG ARG...).  TAG is a plain string; C
;;     runs the matching mechanism.
;;
;; A procedure calls no leaf and emits nothing (docs/kb.org
;; =leaf-must-call-the-mechanism=).  Every KEY string MUST match a
;; m52_caps key byte for byte; a key that does not match makes
;; m52_cap_string_1 return NULL, so the hub emits nothing (a silent byte
;; change).  The 3 keys below are already in the table.  C keeps the
;; C-owned state, the FILE * streams, and the OUTPUT / OUTPUT1 padding.

;; tty_clear_to_end: prefer the whole-screen-bottom capability; else the
;; per-row loop.
(define (tty-clear-to-end-steps has-clr-to-bottom)
  (if (zero? has-clr-to-bottom)
      (list "clear-loop")               ; MARKER
      "clear-to-bottom"))               ; KEY

;; tty_clear_frame: prefer the whole-frame capability; else the fallback.
(define (tty-clear-frame-steps has-clr-frame)
  (if (zero? has-clr-frame)
      (list "clear-frame-fallback")     ; MARKER
      "clear-frame"))                   ; KEY

;; tty_clear_end_of_line: #nil when a guard holds; else the capability or
;; the hard way.  The guard stops the erase of a 0-width region.
(define (tty-clear-end-of-line-steps costs-set cur-x first-unused-hpos has-clr-line)
  (if (or (zero? costs-set) (>= cur-x first-unused-hpos))
      #nil
      (if (zero? has-clr-line)
          (list "clear-line-hard")      ; MARKER
          "clear-line")))               ; KEY

;; --- M52 imp-8: the scroll / window / glyph arithmetic ----------------
;;
;; Each procedure holds the DECISION of one src/term.c arithmetic hub.  A
;; procedure takes plain fixnums and returns a plain ordered step list, a
;; single plain step, or #nil.  The two step kinds match imp-6 / imp-7:
;;
;;   - KEY step: a plain string that names one m52_caps key.  C resolves
;;     it with m52_cap_string_1 and emits it through the original macro.
;;   - MARKER step: a plain list (TAG ARG...).  TAG is a plain string;
;;     C matches it with m52_tty_step_tag_p and runs its own mechanism.
;;
;; A procedure calls no leaf and emits nothing (docs/kb.org
;; =leaf-must-call-the-mechanism=).  Every KEY string MUST match a
;; m52_caps key byte for byte; a key that does not match makes
;; m52_cap_string_1 return NULL, so the hub emits nothing (a silent byte
;; change).  C keeps the C-owned state, the FILE * streams, tparam, and
;; the OUTPUT / OUTPUT1 / OUTPUTL / OUTPUT_IF padding.

;; tty_set_terminal_window: the window height, and the scroll-region call.
;; The MARKER ("set-window" w) HERE means "write tty->specified_window =
;; w".  It is NOT the "set-window" capability KEY that
;; tty-set-scroll-region-steps uses; C tells the two apart with STRINGP
;; against m52_tty_step_tag_p.
(define (tty-set-terminal-window-steps size total-lines scroll-ok)
  (let ((w (if (zero? size) total-lines size)))
    (if (zero? scroll-ok)
        (list (list "set-window" w))
        (list (list "set-window" w) (list "scroll-region" 0 w)))))

;; tty_set_scroll_region: the form choice and the tparam args.  The
;; returned list is ONE MARKER.  A trailing arg that the form does not
;; use stays 0 in C, because the router zeroes the arg array first.
(define (tty-set-scroll-region-steps start stop total-lines cols
                                     has-sr has-sr1 has-window)
  (cond ((not (zero? has-sr))
         (list "scroll-region" start (- stop 1)))
        ((not (zero? has-sr1))
         (list "scroll-region-1" total-lines start
               (- total-lines stop) total-lines))
        (else
         (list "set-window" start 0 stop cols))))

;; tty_delete_glyphs: the insert-mode branch, the delete form, and the
;; end-delete-mode step.  Returns the ordered step list.  The list is
;; FLAT: each mechanism step is a MARKER (a nested list); each capability
;; step is a KEY (a bare string).
(define (tty-delete-glyphs-steps n delete-in-insert-mode has-del-multi-chars)
  (append (if (zero? delete-in-insert-mode)
              (list (list "off-insert") "delete-mode")
              (list (list "on-insert")))
          (if (zero? has-del-multi-chars)
              (list (list "del-char" n))
              (list (list "del-multi" n)))
          (if (zero? delete-in-insert-mode)
              (list "end-delete-mode")
              '())))

;; tty_ins_del_lines: #nil when a guard holds, else the form and the args.
;; i = eabs (n); (- specified-window vpos) is the OUTPUTL line count.
(define (tty-ins-del-lines-steps vpos n specified-window total-lines
                                 scroll-ok memory-below
                                 has-multi has-single has-scroll)
  (let ((i (abs n)))
    (if (or (and (not (zero? scroll-ok)) (>= (+ vpos i) specified-window))
            (and (zero? memory-below) (>= (+ vpos i) total-lines)))
        #nil
        (cond ((not (zero? has-multi))  (list "multi" i))
              ((not (zero? has-single)) (list "single" i))
              (else (list "scroll" i (- specified-window vpos)))))))
