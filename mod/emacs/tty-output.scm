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
;;; M54 imp-2 (the output stream, one operation, one owner).  This
;;; module holds the after-write DECISION of one output write:
;;; tty-write-verdict decides done / retry / give-up from the plain
;;; counts (written len err).  It is pure and emits nothing.  C keeps
;;; the FILE *output, the fwrite, the clearerr, and the return shape; C
;;; stays the single writer.  Scheme borrows the DECISION only.  The
;;; plain record tty-out-handle is the safe handle of milestone.org
;;; section 5: a plain value box, not a FILE * and not a port over one.
;;; The state is *C owned, Scheme borrowed* (docs/m54-plan.org sect. 6).
;;;
;;; M58 imp-4 (the Group B color-mode DECISION).  The mode
;;; canonicalization and the -1 / 0 / 8 scheme choice of
;;; tty_setup_colors, and the change gate of set_tty_color_mode, are
;;; pure procedures of this module: tty-color-mode-tag and
;;; tty-color-mode-changed-p.  The DECISION moved; the cap strings,
;;; the TN_* / TS_* writes, the static default slots, the param_alist
;;; and tty-color-mode-alist resolve, the raw previous_color_mode
;;; store, and the FILE * streams stay C.
;;;
;;; Conventions (identical to M9-M51): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp nil is #nil; no module-level
;;; mutable state.

(define-module (emacs tty-output)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (tty-emit-cap tty-write-bytes tty-flush tty-emit-seq
            tty-write-verdict tty-termscript-copy-handle
            tty-tab-verdict
            make-tty-out-handle tty-out-handle? tty-out-handle-bytes
            tty-out-handle-short-writes tty-out-handle-hard-errors
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
            tty-delete-glyphs-steps tty-ins-del-lines-steps
            tty-face-on-steps tty-face-off-steps tty-capable-p
            tty-color-mode-tag tty-color-mode-changed-p))

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

;; --- M54 imp-2: the output after-write verdict ------------------------
;;
;; M54 moves the ownership of the 3 src/termchar.h FILE * streams behind
;; explicit Guile interfaces, one path at a time.  imp-2 moves ONE
;; operation of the OUTPUT stream: the after-write DECISION of one output
;; write.  C keeps the FILE *, the =fwrite=, the =clearerr=, and the
;; return shape; C stays the single writer.  Scheme borrows the DECISION
;; only, so no FILE * crosses the seam (docs/kb.org
;; =passthrough-leaf-is-not-a-port=).  The state is *C owned, Scheme
;; borrowed* (docs/m54-plan.org section 6).

;; The safe handle of milestone.org section 5: a plain value box, NOT a
;; FILE * and NOT a Guile port over a C stream.  It holds 3 plain
;; counters only: the total byte count, the short-write count, and the
;; hard-error count.  Scheme owns this record; C does not read it.
;;
;; FIX-20261012-guilemacs: implement the record as a plain TAGGED VECTOR,
;; not with (srfi srfi-9) define-record-type.  In the guilemacs module
;; load path a srfi-9 record exposed its constructor as a syntax object
;; through module-ref (a wrong-type-arg on call), so the record shape
;; would not cross the module interface.  A tagged vector is a plain
;; value box: no C struct, no FILE *, and no port can hide in it.
(define tty-out-handle-tag 'tty-out-handle)

(define (make-tty-out-handle bytes short-writes hard-errors)
  (vector tty-out-handle-tag bytes short-writes hard-errors))

(define (tty-out-handle? x)
  (and (vector? x)
       (= 4 (vector-length x))
       (eq? tty-out-handle-tag (vector-ref x 0))))

(define (tty-out-handle-bytes h) (vector-ref h 1))
(define (tty-out-handle-short-writes h) (vector-ref h 2))
(define (tty-out-handle-hard-errors h) (vector-ref h 3))

;; The after-write DECISION of ONE output write.  WRITTEN is the plain
;; count that =fwrite= returned; LEN is the plain requested count; ERR is
;; the plain errno of the write (0 when there is no error).  Return a
;; plain string: "done" when every byte went out, "retry" on =EINTR= /
;; =EAGAIN=, else "give-up".  The procedure is pure: it calls no leaf and
;; emits nothing (docs/kb.org =leaf-must-call-the-mechanism=).  C runs one
;; write and one decision.
(define (tty-write-verdict written len err)
  (cond ((>= written len)                                  "done")
        ((or (zero? err) (= err EINTR) (= err EAGAIN))     "retry")
        (else                                              "give-up")))

;; --- M54 imp-3: the termscript copy DECISION --------------------------
;;
;; A termscript is a COPY of the terminal output (src/termchar.h :61:
;; "send all terminal output characters to this stream also").  imp-3
;; moves ONE operation of that copy stream: the after-write DECISION of
;; ONE termscript copy write.  C keeps the FILE *termscript, the
;; =fwrite=, and the =clearerr=; C stays the single writer, so Scheme
;; still never sees the FILE *.  Scheme borrows the DECISION only.
;;
;; The copy REUSES tty-write-verdict (M54 imp-2).  There is ONE verdict
;; procedure and ONE dispatcher; the copy votes through the same plain
;; values (copied len err) and the same policy: copied >= len -> done;
;; EINTR / EAGAIN (or err = 0) -> retry; a hard errno -> give-up.
;;
;; The record below carries the plain copy counts in the imp-2 handle
;; tty-out-handle (brief.org section 9, Option A).  C still does not
;; read the handle: the handle is BORROWED, not transferred, and C holds
;; no Scheme-side store for it.  The procedure is pure -- it calls no
;; leaf and emits nothing (docs/kb.org =leaf-must-call-the-mechanism=) --
;; and it holds no module state.
(define (tty-termscript-copy-handle copied len err)
  (make-tty-out-handle
   copied
   (if (< copied len) 1 0)
   (if (and (< copied len) (not (zero? err))
            (not (= err EINTR)) (not (= err EAGAIN)))
       1 0)))

;; --- M54 imp-4: the input stream TAB policy ---------------------------
;;
;; imp-4 moves ONE decision of the src/termchar.h INPUT stream
;; (src/termchar.h :51): the terminal TAB policy UseTabs of ONE tty init
;; (src/term.c :5030).  C keeps the mechanism: it calls
;; tabs_safe_p (fileno (tty->input)) (the termios read on the C
;; descriptor) and it reads TabWidth (tty) (a plain fixnum).  It passes
;; the two PLAIN values to Scheme; Scheme owns the pure DECISION.  C
;; stores the result in UseTabs (tty).  No FILE * and no port crosses the
;; seam (docs/kb.org =passthrough-leaf-is-not-a-port=).

;; The terminal TAB policy DECISION of ONE tty init.  TABS-SAFE? is the
;; plain C tabs_safe_p result; TAB-WIDTH is the plain C TabWidth.  Return
;; the plain string "tabs" when the tty may use hard tabs, else "spaces".
;; The procedure is pure: it calls no leaf and emits nothing
;; (docs/kb.org =leaf-must-call-the-mechanism=).  The plain string, not a
;; Scheme boolean, removes the #f / elisp nil ambiguity of a nil verdict
;; (the C seam uses nil for "no Scheme runtime").
(define (tty-tab-verdict tabs-safe? tab-width)
  (if (and tabs-safe? (= tab-width 8)) "tabs" "spaces"))

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

;; --- M58 imp-3: the Group A face-appearance DECISION -----------------
;;
;; FIX-20261018-guilemacs: M58 imp-3 -- the face-appearance DECISION of
;; src/term.c moves to this module.  Three C hubs hold the decision
;; today: turn_on_face, turn_off_face, and tty_capable_p.  C keeps every
;; MECHANISM and passes PLAIN values only:
;;
;;   stays C (mechanism)          | C passes
;;   -----------------------------+-----------------------------------
;;   the struct face field reads  | the plain attrs mask
;;   MAY_USE_WITH_COLORS_P        | the plain `may' mask
;;   the TS_* / TF_* / TN_* reads | the plain `cap' presence mask
;;   strcmp (me, se)              | the plain me-is-end-standout flag
;;   face_tty_specified_color     | folded into the `cap' mask
;;   tparam                       | the plain color number
;;   OUTPUT / OUTPUT1 / OUTPUT_IF | the step list below
;;   tty_toggle_highlight         | the ("toggle-highlight") step
;;   the standout_mode clear      | the ("clear-standout") step
;;   the FILE * streams, fwrite   | nothing crosses the seam
;;
;; The step protocol extends the M52 vocabulary.  Every step is a plain
;; list (TAG ARG...); C tells the tags apart with m52_tty_step_tag_p:
;;
;;   ("cap1" KEY)      OUTPUT1_IF (tty, m52_cap_string_1 (tty, KEY))
;;   ("cap" KEY)       OUTPUT_IF  (tty, m52_cap_string_1 (tty, KEY))
;;   ("tparam" SLOT V) tparam, OUTPUT, xfree
;;   ("toggle-highlight")  tty_toggle_highlight (tty)
;;   ("clear-standout")    tty->standout_mode = 0
;;
;; SLOT: 0 = TS_set_foreground, 1 = TS_set_background,
;;       2 = TF_set_underline_color, 3 = TF_set_underline_style.
;;
;; OUTPUT and OUTPUT1 are NOT interchangeable: OUTPUT pads with
;; FRAME_TOTAL_LINES - curY, OUTPUT1 uses 1 line (brief.org section
;; 5.1 rule 1).  The KEY therefore carries its macro: ("cap" KEY) is the
;; frame-padded route, ("cap1" KEY) is the 1-line route.  Every KEY
;; MUST match a m52_caps key byte for byte; a mismatch makes
;; m52_cap_string_1 return NULL and the hub emits nothing (a silent byte
;; change).
;;
;; The masks are plain fixnums.  NEVER duplicate a C enum or a sentinel
;; value here: C makes every compare and passes plain results.
;;
;;   attrs:  1 bold, 2 italic, 4 underline, 8 strike-through, 16 reverse
;;   may:    1 reverse, 2 bold, 4 italic, 8 underline, 16 strike-through
;;           (the MAY_USE_WITH_COLORS_P results, evaluated in C)
;;   cap:    1 TS_enter_italic_mode, 2 TF_set_underline_style,
;;           16 foreground specified AND its slot string present,
;;           32 background specified AND its slot string present,
;;           64 TF_set_underline_color AND a face underline color,
;;           128 the plain underline route (the underline style is
;;           FACE_UNDERLINE_SINGLE, or the terminal holds no style
;;           capability)
;;
;; face->foreground / face->background / face->underline_color hold the
;; 3 sentinels FACE_TTY_DEFAULT_* (src/dispextern.h) as (unsigned long)
;; -1 ... -3, i.e. 0xFFFFFFFFFFFFFFFF on a 64-bit host.  A sentinel does
;; NOT fit in a fixnum, so it NEVER crosses this seam: C tests it
;; (face_tty_specified_color), folds the answer into the cap mask, and
;; passes 0 in place of the sentinel.  A number below is always a real
;; color.  Scheme copies no sentinel and no C enum.

;; The step list of turn_on_face.  ARGS is ONE plain list:
;;   (reverse attrs underline may cap colors standout fg bg underline-color)
;; Ten fixnums exceed the 9-argument SCM_CALL_N form, so C passes one
;; list.  The ORDER is the original C order: reverse FIRST, because
;; TS_end_standout_mode may equal TS_exit_attribute_mode.  UNDERLINE is
;; the plain face->underline value, used as the tparam argument only.
(define (tty-face-on-steps args)
  (define (bit? mask n) (not (zero? (logand mask n))))
  (let ((reverse   (list-ref args 0))
        (attrs     (list-ref args 1))
        (underline (list-ref args 2))
        (may       (list-ref args 3))
        (cap       (list-ref args 4))
        (colors    (list-ref args 5))
        (standout  (list-ref args 6))
        (fg        (list-ref args 7))
        (bg        (list-ref args 8))
        (underline-color (list-ref args 9)))
    (append
     ;; Reverse video FIRST.
     (if (and (bit? may 1) (not (zero? reverse)))
         (list (list "toggle-highlight"))
         '())
     (if (and (bit? attrs 1) (bit? may 2))
         (list (list "cap1" "bold"))
         '())
     ;; Italics are unavailable on many terminals: map the slant to dim.
     (if (and (bit? attrs 2) (bit? may 4))
         (list (list "cap1" (if (bit? cap 1) "italic" "dim")))
         '())
     ;; A single underline uses the plain capability; any other style
     ;; needs the parameterized string.
     (if (and (bit? attrs 4) (bit? may 8))
         (list (if (bit? cap 128)
                   (list "cap1" "underline")
                   (list "tparam" 3 underline)))
         '())
     (if (and (bit? attrs 8) (bit? may 16))
         (list (list "cap1" "strike-through"))
         '())
     ;; The color steps run only when the terminal has colors.  The
     ;; foreground and background slots SWAP while standout is on.
     (if (zero? colors)
         '()
         (append
          (if (bit? cap 16)
              (list (list "tparam" (if (zero? standout) 0 1) fg))
              '())
          (if (bit? cap 32)
              (list (list "tparam" (if (zero? standout) 1 0) bg))
              '())
          (if (bit? cap 64)
              (list (list "tparam" 2 underline-color))
              '()))))))

;; The step list of turn_off_face.  Seven plain fixnums:
;;   has-me attrs has-exit-underline me-is-end-standout colors
;;   fg-not-default bg-not-default
;; The exit sequence comes BEFORE the color reset.  C keeps the
;; standout_mode clear; Scheme decides when the ("clear-standout") step
;; is present.
(define (tty-face-off-steps has-me attrs has-exit-underline
                            me-is-end-standout colors
                            fg-not-default bg-not-default)
  (append
   (if (not (zero? has-me))
       ;; "me" turns off double-bright, half-bright, reverse, standout,
       ;; and underline.  Emit it only when a face attribute is on.
       (if (zero? attrs)
           '()
           (append (list (list "cap1" "exit-attribute"))
                   (if (zero? me-is-end-standout)
                       '()
                       (list (list "clear-standout")))))
       ;; Without "me" only the appearances that have an exit sequence
       ;; work.  The C source tests face->underline (src/term.c
       ;; :2352 ... :2358) and OUTPUT_IF tests the string, so BOTH the
       ;; underline bit of attrs and the plain presence flag must hold.
       ;; Testing has-exit-underline alone emits the underline exit
       ;; string for a face that holds no underline -- a silent byte
       ;; change on a terminal without "me" (brief.org S2 point 4).
       (if (or (zero? (logand attrs 4)) (zero? has-exit-underline))
           '()
           (list (list "cap" "exit-underline"))))
   ;; Switch back to the default colors.
   (if (and (not (zero? colors))
            (or (not (zero? fg-not-default))
                (not (zero? bg-not-default))))
       (list (list "cap1" "orig-pair"))
       '())))

;; The verdict of tty_capable_p.  Four plain fixnums:
;;   caps presence no-color-video max-colors
;; CAPS holds the requested TTY_CAP_* bits, PRESENCE the matching "the
;; TS_* / TF_* string is present" bits, NO-COLOR-VIDEO the TN_no_color_video
;; bits, and MAX-COLORS the TN_max_colors count (0 = no color support).
;; Return the plain fixnum 0 (not capable) or 1 (capable).
;;
;; The table below is the C TTY_CAPABLE_P_TRY chain of src/term.c, one
;; row per check: the requested bit, the presence bit, and the
;; enum no_color_bit value.  C keeps the field reads and passes the
;; masks.
(define (tty-capable-p caps presence no-color-video max-colors)
  (define (may-use? nc-bit)
    ;; MAY_USE_WITH_COLORS_P: colors > 0 means the NC bit decides.
    (or (<= max-colors 0) (zero? (logand no-color-video nc-bit))))
  (define (blocked? cap-bit presence-bit nc-bit)
    (and (not (zero? (logand caps cap-bit)))
         (or (zero? (logand presence presence-bit))
             (not (may-use? nc-bit)))))
  (if (or (blocked? #x01 #x01 #x04)   ; TTY_CAP_INVERSE          NC_REVERSE
          (blocked? #x02 #x02 #x02)   ; TTY_CAP_UNDERLINE        NC_UNDERLINE
          (blocked? #x02 #x04 #x02)   ; TTY_CAP_UNDERLINE_STYLED NC_UNDERLINE
          (blocked? #x04 #x08 #x20)   ; TTY_CAP_BOLD             NC_BOLD
          (blocked? #x08 #x10 #x10)   ; TTY_CAP_DIM              NC_DIM
          (blocked? #x10 #x20 #x08)   ; TTY_CAP_ITALIC           NC_ITALIC
          (blocked? #x20 #x40 #x40))  ; TTY_CAP_STRIKE_THROUGH   NC_STRIKE_THROUGH
      0
      1))

;; M58 imp-4: the Group B color-mode DECISION of src/term.c.  The
;; canonicalization and the -1 / 0 / 8 scheme choice of
;; tty_setup_colors move HERE.  C keeps every mechanism: the 3 cap
;; strings (including the TERMINFO variants of the 8-color scheme),
;; every TN_* and TS_* write, the static default slots,
;; tty_default_color_capabilities save / restore, the
;; f->param_alist and tty-color-mode-alist resolve, the
;; TYPE_RANGED_FIXNUMP narrowing, the raw previous_color_mode store,
;; safe_calln, and the FILE * streams.  C resolves the Lisp value to a
;; plain int first, so no Lisp_Object, struct frame *, or
;; struct tty_display_info * crosses the seam.

;; The scheme tag of one color MODE.  MODE is a plain fixnum.  Return
;; one plain tag list:
;;
;;   ("none")    no colors at all (TN_max_colors 0, the 3 TS_* NULL)
;;   ("ansi-8")  the 8 standard ANSI colors
;;   ("default") the default capabilities, if any
;;
;; The canonicalization belongs HERE: every mode below -1 (-5, -1)
;; gives ("none"), so C canonicalizes no second time.
(define (tty-color-mode-tag mode)
  (cond
   ((< mode -1) (list "none"))
   ((= mode -1) (list "none"))
   ((= mode 8) (list "ansi-8"))
   (else (list "default"))))

;; The change gate of set_tty_color_mode.  MODE and PREVIOUS are the
;; RAW color modes (plain fixnums).  Return the plain fixnum 1 when the
;; mode changed, else 0.  The compare is on the RAW modes: -5 and -1
;; are a change, even though both give the same ("none") scheme.
(define (tty-color-mode-changed-p mode previous)
  (if (= mode previous) 0 1))
