(define-module (emacs command-loop)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:use-module (srfi srfi-11)          ; let*-values (adjust-point-for-property)
  ;; M28 imp-5 family 6 — --record-recent-keys-cmd-pseudo-event reclaimed;
  ;; call the (emacs recent-keys) port directly.  (emacs recent-keys)
  ;; imports only elisp-ref + runtime, so this eager import is cycle-free.
  #:use-module ((emacs recent-keys) #:select (record-cmd-pseudo-event!))
  #:declarative? #t
  #:export (command-loop-1-prologue
            command-loop-1-iter-pre-read
            command-loop-1-iter-dispatch
            command-loop-1-iter-post-dispatch
            command-loop-1-iter-mark-region
            command-loop-1-finalize
            adjust-point-for-property
            command-loop-1
            command-loop-2
            top-level-1
            command-loop-main
            cmd-error
            cmd-error-internal!
            command-error-default-function
            safe-run-hooks!
            safe-run-hooks-2!
            safe-run-hooks-maybe-narrowed!
            init-command-loop-registrations
            init-m23-imp4-registrations
            init-m23-imp5-registrations))

;;; M7a — Prologue of command_loop_1, ported from C to Scheme.
;;;
;;; This is the first slice of the larger M7 effort (porting the
;;; ~370-line command_loop_1 body to Scheme).  The prologue is the
;;; one-time state initialization plus the trailing post-command-hook
;;; and delayed-warnings-hook that the previous command (which may
;;; have thrown to top-level) didn't get to run.
;;;
;;; The C body of command_loop_1_prologue (still callable from the
;;; surrounding command_loop_1 body) is now a one-liner cached-SCM
;;; dispatch to this procedure.  Net C deletion: ~30 lines.
;;;
;;; Subsequent slices (M7b main-loop iteration, M7c finalize) will
;;; replace the rest of command_loop_1 in further commits.
;;;
;;; See docs/keyboard.org §"M7a — command_loop_1 prologue".


;; Cache lookups for the C-side primitives used per command-loop entry.
(define %cancel-echoing                       (delay (%c '--cancel-echoing)))
(define %clear-waiting-for-input              (delay (%c '--clear-waiting-for-input)))
(define %set-this-command-key-count           (delay (%c '--set-this-command-key-count)))
(define %set-this-single-command-key-start    (delay (%c '--set-this-single-command-key-start)))
(define %echo-area-buffer-0-non-empty-p       (delay (%c '--echo-area-buffer-0-non-empty-p)))
(define %resize-echo-area-exactly             (delay (%c '--resize-echo-area-exactly)))
(define %current-kboard                       (delay (%c 'current-kboard)))
(define %set-kboard-prefix-arg                (delay (%c 'set-kboard-prefix-arg)))
(define %set-kboard-last-prefix-arg           (delay (%c 'set-kboard-last-prefix-arg)))
(define %set-kboard-last-command              (delay (%c 'set-kboard-last-command)))
(define %set-kboard-real-last-command         (delay (%c 'set-kboard-real-last-command)))
(define %set-kboard-last-repeatable-command   (delay (%c 'set-kboard-last-repeatable-command)))

(define (%nilp x)
  ;; Recognize all three nil-equivalents that show up in Guile-elisp:
  ;; the elisp `nil' symbol (#nil), the Scheme empty list ('()), and
  ;; Scheme #f.  `null?' in Guile catches both #nil and '() in this
  ;; build; `not' catches #f.
  (or (null? x) (not x)))

;;; ---------------------------------------------------------------------
;;; M22 imp-2 — cmd_error_internal ported to Scheme.  The C function is
;;; now a thin dispatcher to this procedure; the two process.c call sites
;;; are unchanged.  DATA is (error-symbol . error-data); CONTEXT is a
;;; (possibly empty) ASCII string.

(define (cmd-error-internal! data context)
  "Take actions on handling an error.  DATA is the error data; CONTEXT
is an ASCII string describing the context.  Clears signaling-function
and quit-flag, binds inhibit-quit, and calls command-error-function
with (DATA CONTEXT SIGNALING-FUNCTION) if it is set.  Mirrors the old
C cmd_error_internal."
  ;; The immediate context is not interesting for Quits, since they are
  ;; asynchronous.
  (when (not (%nilp ((force %signal-quit-p) data)))
    ((force %signaling-function-set!) #nil))
  (set-symbol-value! 'quit-flag    #nil)
  (set-symbol-value! 'inhibit-quit #t)
  ;; Use the user's specified output function if any.
  (when (not (%nilp (symbol-value 'command-error-function)))
    ((%c 'funcall) (symbol-value 'command-error-function)
     data context ((force %signaling-function))))
  ((force %signaling-function-set!) #nil))

(define (command-loop-1-prologue)
  "Per-entry initialization for command_loop_1.  Mirrors the C
prologue (keyboard.c command_loop_1_prologue) verbatim:

  - Reset prefix-arg, last-prefix-arg on current-kboard.
  - Clear deactivate-mark, waiting-for-input.
  - Cancel echoing on current-kboard.
  - Zero this-command-key-count and this-single-command-key-start.
  - If not in memory-full state: run post-command-hook (if any),
    resize echo area if displaying, run delayed-warnings-hook.
  - Save this-command / real-this-command into the kboard's
    last-command slots so that this command's `last-command' query
    sees the previous command.
  - If last-command-event is not a cons, also save into
    last-repeatable-command (so `repeat' picks it up)."
  (let ((kboard ((force %current-kboard))))
    ((force %set-kboard-prefix-arg)      kboard #nil)
    ((force %set-kboard-last-prefix-arg) kboard #nil)
    (set-symbol-value! 'deactivate-mark #nil)
    ((force %clear-waiting-for-input))
    ((force %cancel-echoing))

    ((force %set-this-command-key-count)        0)
    ((force %set-this-single-command-key-start) 0)

    (when (%nilp (symbol-value 'memory-full))
      ;; The C check `!NILP(Vrun_hooks)' guards against the very early
      ;; startup window before eval.c registers the run-hooks symbol.
      ;; In Scheme we check `fboundp' instead — by the time this prologue
      ;; runs the function is set, but keeping the guard preserves the
      ;; original safety.  Use elisp symbol-function lookup (bare
      ;; `fboundp' is not a Scheme binding).
      (when (and (not (%nilp (symbol-value 'post-command-hook)))
                 ((%c 'fboundp) 'run-hooks))
        (safe-run-hooks-maybe-narrowed! 'post-command-hook))

      (when (not (%nilp ((force %echo-area-buffer-0-non-empty-p))))
        ((force %resize-echo-area-exactly)))

      (when (not (%nilp (symbol-value 'delayed-warnings-list)))
        (safe-run-hooks! 'delayed-warnings-hook)))

    ;; Save this-command / real-this-command into last-command slots.
    ((force %set-kboard-last-command)      kboard (symbol-value 'this-command))
    ((force %set-kboard-real-last-command) kboard (symbol-value 'real-this-command))
    (let ((lce (symbol-value 'last-command-event)))
      (unless (pair? lce)
        ((force %set-kboard-last-repeatable-command)
         kboard (symbol-value 'real-this-command))))))

;;;;
;;;; M7b1 — pre-read portion of command_loop_1's main loop body.
;;;;

;; Cache the M7b1 helper subrs.
(define %selected-frame-live-p                  (delay (%c '--selected-frame-live-p)))
(define %set-buffer-from-selected-window        (delay (%c '--set-buffer-from-selected-window)))
(define %display-pending-malloc-warnings-loop   (delay (%c '--display-pending-malloc-warnings-loop)))
(define %clear-ignore-mouse-drag                (delay (%c '--clear-ignore-mouse-drag)))
(define %minibuf-and-echo-area-aligned-p        (delay (%c '--minibuf-and-echo-area-aligned-p)))
(define %resize-mini-window-minibuf-non-shrink  (delay (%c '--resize-mini-window-minibuf-non-shrink)))
(define %quit-char                              (delay (%c '--quit-char)))
(define %set-raw-keybuf-count                   (delay (%c '--set-raw-keybuf-count)))
(define %read-key-sequence                      (delay (%c '--read-key-sequence)))
(define %inc-num-input-keys                     (delay (%c '--inc-num-input-keys)))
(define %message1-clear
  ;; The wrapped thunk does `(message nil)` via elisp symbol-function
  ;; lookup; bare `message' is not a Scheme binding.
  (delay (lambda () ((%c 'message) #nil))))

(define (command-loop-1-iter-pre-read)
  "Pre-read portion of one iteration of command_loop_1's while-loop.
Returns:
  0 — OK, continue iteration (last-command-event has been updated).
  1 — EOF; caller should return Qnil from command_loop_1.
  2 — Menu rejected; caller should goto finalize (skip rest of iter).

Mirrors lines 1520-1649 of the original C command_loop_1 body.  See
docs/keyboard.org §M7b1."
  ;; Frame check.
  (when (%nilp ((force %selected-frame-live-p)))
    ((%c 'kill-emacs) #nil #nil))

  ;; Buffer current update.
  ((force %set-buffer-from-selected-window))

  ;; Drain pending malloc warnings (rare).
  ((force %display-pending-malloc-warnings-loop))

  (set-symbol-value! 'deactivate-mark #nil)
  ((force %clear-ignore-mouse-drag))

  ;; Minibuffer/echo-area timing dance.
  (when (not (%nilp ((force %minibuf-and-echo-area-aligned-p))))
    ;; The C body uses dynwind + specbind(Qinhibit_quit, Qt); we use
    ;; an elisp `let' (which specbinds inhibit-quit on the elisp side)
    ;; via the runtime helpers.  Scheme dynamic-wind isn't quite the
    ;; right tool here — specbind has to bind on the elisp specpdl
    ;; stack so signal-handlers see inhibit-quit=t.
    (let ((saved (symbol-value 'inhibit-quit)))
      (dynamic-wind
        (lambda () (set-symbol-value! 'inhibit-quit #t))
        (lambda ()
          ((%c 'sit-for) (symbol-value 'minibuffer-message-timeout) 0 2)
          ((force %message1-clear))
          (safe-run-hooks! 'echo-area-clear-hook)
          ((force %resize-mini-window-minibuf-non-shrink)))
        (lambda () (set-symbol-value! 'inhibit-quit saved))))

    ;; If a C-g came in while we were displaying, treat it as input.
    (when (not (%nilp (symbol-value 'quit-flag)))
      (set-symbol-value! 'quit-flag #nil)
      (set-symbol-value! 'unread-command-events
                         (list ((force %quit-char))))))

  ;; Reset this-command-related vars.
  (set-symbol-value! 'this-command                       #nil)
  (set-symbol-value! 'real-this-command                  #nil)
  (set-symbol-value! 'this-original-command              #nil)
  (set-symbol-value! 'this-command-keys-shift-translated #nil)

  ;; Read the next key sequence.  --read-key-sequence sets
  ;; last-command-event internally when length > 0.
  ((force %set-raw-keybuf-count) 0)
  (let ((i ((force %read-key-sequence))))
    ;; Post-read frame check + buffer update.
    (when (%nilp ((force %selected-frame-live-p)))
      ((%c 'kill-emacs) #nil #nil))
    ((force %set-buffer-from-selected-window))

    ((force %inc-num-input-keys))

    (cond
     ((= i 0)
      ;; EOF — only happens at end of a kbd macro.
      1)
     ((= i -1)
      ;; Menu rejected — reset the per-key counters and signal finalize.
      ((%c '--cancel-echoing))
      ((%c '--set-this-command-key-count) 0)
      ((%c '--set-this-single-command-key-start) 0)
      2)
     (else
      ;; Normal — last-command-event already set by --read-key-sequence.
      0))))

;;;;
;;;; M7b2 — dispatch portion (force-start, cmd lookup, pre-command-hook, execute)
;;;;

(define %clear-force-start                              (delay (%c '--clear-force-start-and-flush-buffer-unchanged)))
(define %read-key-sequence-cmd                          (delay (%c '--read-key-sequence-cmd)))
(define %read-key-sequence-remapped                     (delay (%c '--read-key-sequence-remapped)))
(define %maybe-quit                                     (delay (%c '--maybe-quit)))
(define %save-state-for-redisplay-get-pt                (delay (%c '--save-state-for-redisplay-get-pt)))
(define %restore-last-point-position                    (delay (%c '--restore-last-point-position)))
(define %with-hourglass-protection                      (delay (%c '--with-hourglass-protection)))
(define %save-point-before-last-command-or-undo         (delay (%c '--save-point-before-last-command-or-undo)))
(define %reset-redisplay-tick-state                     (delay (%c '--reset-redisplay-tick-state)))
(define %clear-display-working-on-window-p              (delay (%c '--clear-display-working-on-window-p)))

(define (command-loop-1-iter-dispatch)
  "Dispatch portion of one iteration of command_loop_1's while-loop.
Runs after pre-read has populated last-command-event.  Performs the
command lookup, the executing-kbd-macro/quit-flag dance, state save
for redisplay, command-remap, recent-keys pseudo-event push,
this-command/real-this-command set, pre-command-hook run, and the
command-execute call (wrapped with hourglass protection on a window
system, plus undo-boundary + redisplay-tick reset).

Mirrors lines 1696-1804 of the original C command_loop_1 body.  See
docs/keyboard.org §M7b2."

  ;; force-start handling — clear the flag and flush BEG/END unchanged.
  ((force %clear-force-start))

  (let ((cmd ((force %read-key-sequence-cmd))))
    ;; Executing-kbd-macro + quit-flag interaction.
    (when (not (%nilp (symbol-value 'executing-kbd-macro)))
      (when (not (%nilp (symbol-value 'quit-flag)))
        (set-symbol-value! 'executing-kbd-macro #t)
        ((force %maybe-quit))))   ;; will return since macro now empty

    ;; State save for redisplay.  --save-state-for-redisplay-get-pt sets
    ;; cl1_prev_buffer / cl1_prev_modiff / last_point_position to current
    ;; state and returns PT, which we capture for the post-dispatch
    ;; restore.
    (let ((last-pt ((force %save-state-for-redisplay-get-pt))))

      ;; Reset disable-point-adjustment and deactivate-mark.
      (set-symbol-value! 'disable-point-adjustment #nil)
      (set-symbol-value! 'deactivate-mark          #nil)

      ;; Remap command through active keymaps.
      (set-symbol-value! 'this-original-command cmd)
      (let* ((remapped ((force %read-key-sequence-remapped)))
             (cmd (if (%nilp remapped) cmd remapped)))

        ;; Push (nil . cmd) pseudo-event into recent-keys ring.
        (record-cmd-pseudo-event! cmd)

        (set-symbol-value! 'this-command      cmd)
        (set-symbol-value! 'real-this-command cmd)

        ;; pre-command-hook.
        (safe-run-hooks-maybe-narrowed! 'pre-command-hook)

        ;; Execute the command.
        (if (%nilp (symbol-value 'this-command))
            ;; nil means key is undefined.
            ((%c 'undefined))
          ;; Wrap the dispatch in hourglass protection (no-op in batch).
          ((force %with-hourglass-protection)
           (lambda ()
             ;; Undo-boundary so changes from this command are properly
             ;; partitioned in the undo history.
             ((%c 'undo-auto--add-boundary))
             ;; Snapshot point/buffer for potential undo-with-point.
             ((force %save-point-before-last-command-or-undo))
             ;; Reset redisplay tick accounting.
             ((force %reset-redisplay-tick-state))
             ;; The actual command dispatch.
             ((%c 'command-execute) (symbol-value 'this-command))
             ;; And again — could be flipped by the command-execute body.
             ((force %clear-display-working-on-window-p))))))

      ;; Restore last_point_position to its pre-command value, in case
      ;; a recursive-edit invoked from the command clobbered it.
      ((force %restore-last-point-position) last-pt))))

;;;;
;;;; M7b3 — post-dispatch portion (post-command-hook, last-command save, echo refresh)
;;;;

(define %echo-area-window-eq-selected-frame-minibuf-p (delay (%c '--echo-area-window-eq-selected-frame-minibuf-p)))
(define %current-kboard-immediate-echo-p              (delay (%c '--current-kboard-immediate-echo-p)))
(define %clear-current-kboard-immediate-echo          (delay (%c '--clear-current-kboard-immediate-echo)))
(define %echo-now                                     (delay (%c '--echo-now)))

(define (command-loop-1-iter-post-dispatch)
  "Post-dispatch portion of one iteration of command_loop_1's while-loop.
Saves Vcurrent_prefix_arg into the kboard's last-prefix-arg slot,
runs the trailing post-command-hook + delayed-warnings-hook for the
command we just dispatched, refreshes/resizes the echo area, saves
this-command / real-this-command / last-repeatable-command into the
kboard, zeroes the per-command key counters, and refreshes or cancels
the echo display depending on the kboard's immediate-echo bit-field.

Mirrors lines 1805-1858 of the original C command_loop_1 body.  See
docs/keyboard.org §M7b3."
  (let ((kboard ((force %current-kboard))))
    ((force %set-kboard-last-prefix-arg) kboard (symbol-value 'current-prefix-arg))

    (safe-run-hooks-maybe-narrowed! 'post-command-hook)

    ;; Resize echo area if the displayed message is on the selected
    ;; frame's minibuffer (Bug#34317 guard).
    (when (and (not (%nilp ((force %echo-area-buffer-0-non-empty-p))))
               (not (%nilp ((force %echo-area-window-eq-selected-frame-minibuf-p)))))
      ((force %resize-echo-area-exactly)))

    (when (not (%nilp (symbol-value 'delayed-warnings-list)))
      (safe-run-hooks! 'delayed-warnings-hook))

    ;; Save final this-command / real-this-command / last-repeatable.
    ((force %set-kboard-last-command)      kboard (symbol-value 'this-command))
    ((force %set-kboard-real-last-command) kboard (symbol-value 'real-this-command))
    (let ((lce (symbol-value 'last-command-event)))
      (unless (pair? lce)
        ((force %set-kboard-last-repeatable-command)
         kboard (symbol-value 'real-this-command))))

    ;; Zero per-command key counters.
    ((force %set-this-command-key-count)        0)
    ((force %set-this-single-command-key-start) 0)

    ;; Immediate-echo refresh path.  If echoes are still in flight and
    ;; internal-echo-keystrokes-prefix returns non-nil, redraw; else
    ;; cancel.
    (if (and (not (%nilp ((force %current-kboard-immediate-echo-p))))
             (not (%nilp ((%c 'internal-echo-keystrokes-prefix)))))
        (begin
          ((force %clear-current-kboard-immediate-echo))
          ((force %echo-now)))
        ((force %cancel-echoing)))))

;;;;
;;;; M7b4 — mark/region block
;;;;

(define %current-buffer-mark-active-p       (delay (%c '--current-buffer-mark-active-p)))
(define %current-buffer-mark-has-buffer-p   (delay (%c '--current-buffer-mark-has-buffer-p)))
(define %cl1-prev-buffer-current-p          (delay (%c '--cl1-prev-buffer-current-p)))
(define %cl1-prev-modiff-current-p          (delay (%c '--cl1-prev-modiff-current-p)))

(define (command-loop-1-iter-mark-region)
  "Mark/region block of one iteration of command_loop_1's while-loop.
Runs only when current-buffer's mark-active is non-nil and run-hooks
is fboundp (startup guard).  Adjusts transient-mark-mode (the obsolete
`only' / `identity' rotation), either dispatches deactivate-mark or
synchronizes the PRIMARY selection + runs post-select-region-hook
based on select-active-regions, and conditionally runs
activate-mark-hook when the command changed the buffer or modified
its contents.

Mirrors lines 1916-1967 of the original C command_loop_1 body.  See
docs/keyboard.org §M7b4."
  (when (and (not (%nilp ((force %current-buffer-mark-active-p))))
             ((%c 'fboundp) 'run-hooks))
    ;; Emacs 22 compatibility: rotate transient-mark-mode's `only' /
    ;; `identity' values.
    (let ((tmm (symbol-value 'transient-mark-mode)))
      (cond
       ((eq? tmm 'identity) (set-symbol-value! 'transient-mark-mode #nil))
       ((eq? tmm 'only)     (set-symbol-value! 'transient-mark-mode 'identity))))

    (if (not (%nilp (symbol-value 'deactivate-mark)))
        ;; If `select-active-regions' is non-nil this also sets PRIMARY.
        ((%c 'deactivate-mark))
        ;; Otherwise, optionally sync PRIMARY + run activate-mark-hook.
        (let* ((window-system-p
                (not (%nilp ((%c 'window-system) #nil))))
               (tty-active-regions
                (and (symbol-bound? 'tty-select-active-regions)
                     (not (%nilp (symbol-value 'tty-select-active-regions)))))
               (xterm-set-selection-p
                (and tty-active-regions
                     (not (%nilp ((%c 'terminal-parameter)
                                  #nil 'xterm--set-selection)))))
               (sar-trigger?
                (let ((sar (symbol-value 'select-active-regions))
                      (tmm (symbol-value 'transient-mark-mode)))
                  ;; `eq?' here (Scheme), not elisp `eq' — the latter is
                  ;; not a Scheme binding inside this module.
                  (if (eq? sar 'only)
                      (eq? (if (pair? tmm) (car tmm) #nil) 'only)
                      (and (not (%nilp sar)) (not (%nilp tmm))))))
               (inhibit-update?
                (not (%nilp ((%c 'memq) (symbol-value 'this-command)
                             (symbol-value 'selection-inhibit-update-commands))))))
          (when (and (or window-system-p xterm-set-selection-p)
                     ;; Even if mark-active is non-nil, the underlying
                     ;; marker may not yet have a buffer (Bug#7044).
                     (not (%nilp ((force %current-buffer-mark-has-buffer-p))))
                     sar-trigger?
                     (not inhibit-update?))
            (let ((txt ((symbol-value 'region-extract-function) #nil)))
              (when (> ((%c 'length) txt) 0)
                ;; Don't set empty selections.
                ((%c 'gui-set-selection) 'PRIMARY txt))
              ((%c 'run-hook-with-args) 'post-select-region-hook txt)))
          ;; activate-mark-hook fires only when the command changed
          ;; buffer-state visible to the redisplay logic.
          (when (or (%nilp ((force %cl1-prev-buffer-current-p)))
                    (%nilp ((force %cl1-prev-modiff-current-p))))
            ((%c 'run-hooks) 'activate-mark-hook))))

    (set-symbol-value! 'saved-region-selection #nil)))

;;;;
;;;; M7c — finalize block (point adjustment + kbd-macro chars install)
;;;;

(define %selected-window-buffer-current-p
  (delay (%c '--selected-window-buffer-current-p)))
(define %last-point-position-ne-pt-p
  (delay (%c '--last-point-position-ne-pt-p)))
(define %composition-break-at-point-p
  (delay (%c '--composition-break-at-point-p)))
(define %last-point-position-in-accessible-p
  (delay (%c '--last-point-position-in-accessible-p)))
(define %pt-in-accessible-p
  (delay (%c '--pt-in-accessible-p)))
(define %composition-adjust-point-lpp-changes-p
  (delay (%c '--composition-adjust-point-lpp-changes-p)))
(define %composition-adjust-point-pt-changes-p
  (delay (%c '--composition-adjust-point-pt-changes-p)))
(define %adjust-point-for-property-cl1
  (delay (%c '--adjust-point-for-property-cl1)))
(define %set-windows-or-buffers-changed
  (delay (%c '--set-windows-or-buffers-changed)))
(define %finalize-kbd-macro-chars
  (delay (%c '--finalize-kbd-macro-chars)))
(define %kboard-defining-kbd-macro (delay (%c 'kboard-defining-kbd-macro)))
(define %kboard-prefix-arg         (delay (%c 'kboard-prefix-arg)))

(define (command-loop-1-finalize)
  "Finalize block of one iteration of command_loop_1's while-loop.
Two responsibilities:

  1. Adjust point for grapheme-cluster boundaries when the buffer
     and selected-window buffer are unchanged but PT moved.  If
     point-adjustment is enabled and composition-break-at-point is
     off, possibly invalidate the display (windows_or_buffers_changed
     = 21) and call adjust_point_for_property.  Otherwise — if
     point-adjustment is disabled but PT is now inside a grapheme
     cluster — set windows_or_buffers_changed = 39.

  2. Install chars successfully executed in the current kbd-macro
     recording (when defining-kbd-macro is set and no prefix-arg is
     pending).

Mirrors lines 1976-2010 of the original C command_loop_1 body.  See
docs/keyboard.org §M7c."
  (when (and (not (%nilp ((force %cl1-prev-buffer-current-p))))
             (not (%nilp ((force %selected-window-buffer-current-p))))
             (not (%nilp ((force %last-point-position-ne-pt-p)))))
    (cond
     ((and (%nilp (symbol-value 'disable-point-adjustment))
           (%nilp (symbol-value 'global-disable-point-adjustment))
           (%nilp ((force %composition-break-at-point-p))))
      (when (and (not (%nilp ((force %last-point-position-in-accessible-p))))
                 (not (%nilp ((force %composition-adjust-point-lpp-changes-p)))))
        ;; The last point was temporarily set within a grapheme
        ;; cluster to prevent automatic composition.  Invalidate
        ;; the display to recover the automatic composition.
        ((force %set-windows-or-buffers-changed) 21))
      ((force %adjust-point-for-property-cl1)))
     ((and (not (%nilp ((force %pt-in-accessible-p))))
           (not (%nilp ((force %composition-adjust-point-pt-changes-p)))))
      ;; Now point is within a grapheme cluster.  Invalidate the
      ;; display so the cluster is de-composed and the cursor is
      ;; correctly placed at point.
      ((force %set-windows-or-buffers-changed) 39))))

  ;; Install chars successfully executed in kbd macro.
  (let ((kb ((force %current-kboard))))
    (when (and (not (%nilp ((force %kboard-defining-kbd-macro) kb)))
               (%nilp ((force %kboard-prefix-arg) kb)))
      ((force %finalize-kbd-macro-chars)))))

;;;;
;;;; M7c-adj — adjust-point-for-property (ported from static C
;;;; adjust_point_for_property, src/keyboard.c).  Called from the C
;;;; --adjust-point-for-property-cl1 dispatcher.  See
;;;; docs/m22-plan.org §imp-3 (Finding E).
;;;;

(define %composition-adjust-point   (delay (%c '--composition-adjust-point)))
(define %display-prop-intangible-p  (delay (%c '--display-prop-intangible-p)))

;; FIX-20260901-guilemacs: the C TEXT_PROP_MEANS_INVISIBLE macro always
;; examines its argument as a raw property VALUE (via invisible_prop,
;; src/xdisp.c:29616).  The Lisp-visible `invisible-p' DEFUN instead
;; dispatches FIXNATP/MARKER arguments as buffer POSITIONS
;; (src/xdisp.c:29666-29670) before falling through to the same value check.
;; Every call site here passes a raw property value, never a position, so the
;; substitution matches C for all normal values (symbols, t, lists).  It
;; diverges only for a plain non-negative-integer property VALUE, which
;; invisible_prop treats as not-invisible while `invisible-p' would re-read
;; the property at that position.  No real invisible-property user sets plain
;; integers, so this is left as a documented gap rather than a full Scheme
;; reimplementation of invisible_prop.
(define (invisible-level val)
  "TEXT_PROP_MEANS_INVISIBLE, expressed on a raw property VALUE:
0 = not invisible, 1 = t, else the fixnum ellipsis level.  invisible-p
accepts a raw property value directly."
  (let ((inv ((%c 'invisible-p) val)))
    (cond ((%nilp inv) 0)
          ((eq? inv #t) 1)
          (else inv))))

(define (adjust-point-for-property last-pt modified)
  "Adjust point to a boundary of a region that has a `composition',
`display' or `invisible' property that should be treated intangible.
LAST-PT is the last position of point; MODIFIED is whether the buffer
was just modified (which suppresses composition adjustment).  Mirrors
src/keyboard.c adjust_point_for_property; eassert dropped (no behavior)."
  (define (pt) ((%c 'point)))
  ;; cr.org Finding 1: point-byte was a new primitive with no precedent;
  ;; the existing position-bytes (position arg) already does this.
  (define (pt-byte) ((%c 'position-bytes) (pt)))
  (define (begv) ((%c 'point-min)))
  (define (zv) ((%c 'point-max)))
  (define (set-pt! p) ((%c 'goto-char) p))

  ;; get_char_property_and_overlay + display_prop_intangible_p + range.
  ;; Returns (values found? val beg end) for the display property at POS.
  (define (display-range-at pos)
    (let* ((po ((%c 'get-char-property-and-overlay) pos 'display
                ((%c 'selected-window))))
           (val ((%c 'car) po))
           (ov ((%c 'cdr) po)))
      (if (or (%nilp val)
              (%nilp ((force %display-prop-intangible-p) val ov pos (pt-byte))))
          (values #f #nil 0 0)
          (if (not (%nilp ((%c 'overlayp) ov)))
              (values #t val ((%c 'overlay-start) ov) ((%c 'overlay-end) ov))
              ;; get_property_and_range (POS, display, ..., Qnil) — the C
              ;; body tries the Scheme text-property path first.
              (let ((v ((%c 'get-text-property) pos 'display
                        ((%c 'current-buffer)))))
                (if (%nilp v)
                    (values #f #nil 0 0)
                    (let* ((prev ((%c 'previous-single-property-change)
                                  pos 'display ((%c 'current-buffer)) (begv)))
                           (next ((%c 'next-single-property-change)
                                  pos 'display ((%c 'current-buffer)) (zv)))
                           (b (if (%nilp prev) (begv) prev))
                           (e (if (%nilp next) (zv) next)))
                      (values #t v b e))))))))

  ;; The forward C while loop finding the invisible area's end.
  (define (scan-invisible-forward pos ellipsis)
    (let ((e pos)
          (el ellipsis))
      (let loop ()
        (let* ((po ((%c 'get-char-property-and-overlay) e 'invisible #nil))
               (val ((%c 'car) po))
               (ov ((%c 'cdr) po))
               (inv (invisible-level val)))
          (if (and (< e (zv)) (> inv 0))
              (begin
                (set! el (or el (> inv 1)
                             (and (not (%nilp ((%c 'overlayp) ov)))
                                  (or (not (%nilp ((%c 'overlay-get) ov 'after-string)))
                                      (not (%nilp ((%c 'overlay-get) ov 'before-string)))))))
                (let ((tmp ((%c 'next-single-char-property-change)
                            e 'invisible #nil #nil)))
                  (set! e (if (and (not (%nilp tmp)) (integer? tmp)) tmp (zv)))
                  (loop)))
              (values e el))))))

  ;; The backward C while loop finding the invisible area's start.
  ;; FIX-20260901-guilemacs: the C body checks (beg > BEGV) BEFORE reading
  ;; the property at (beg - 1); BEGV - 1 is an invalid buffer position and
  ;; get-char-property-and-overlay signals args-out-of-range there.  Keep the
  ;; same short-circuit order so the scan never reads past the accessible
  ;; region's start.
  (define (scan-invisible-backward pos ellipsis)
    (let ((b pos)
          (el ellipsis))
      (let loop ()
        (if (not (> b (begv)))
            (values b el)
            (let* ((po ((%c 'get-char-property-and-overlay) (- b 1) 'invisible #nil))
                   (val ((%c 'car) po))
                   (ov ((%c 'cdr) po))
                   (inv (invisible-level val)))
              (if (not (> inv 0))
                  (values b el)
                  (begin
                    (set! el (or el (> inv 1)
                                 (and (not (%nilp ((%c 'overlayp) ov)))
                                      (or (not (%nilp ((%c 'overlay-get) ov 'after-string)))
                                          (not (%nilp ((%c 'overlay-get) ov 'before-string)))))))
                    (let ((tmp ((%c 'previous-single-char-property-change)
                                b 'invisible #nil #nil)))
                      (set! b (if (and (not (%nilp tmp)) (integer? tmp)) tmp (begv)))
                      (loop)))))))))

  (let ((check-composition (not modified))
        (check-display #t)
        (check-invisible #t)
        (orig-pt (pt)))
    (let comp-loop ()
      (when (or check-composition check-display check-invisible)
        ;; --- composition branch ---
        (when (and check-composition
                   (> (pt) (begv)) (< (pt) (zv))
                   (let ((b ((force %composition-adjust-point) last-pt (pt))))
                     (if (not (= b (pt)))
                         (begin (set-pt! b) #t)
                         #f)))
          (set! check-display #t)
          (set! check-invisible #t))
        (set! check-composition #f)
        ;; --- display branch ---
        (when (and check-display
                   (> (pt) (begv)) (< (pt) (zv)))
          (let*-values (((found val beg end) (display-range-at (pt))))
            (when (and found
                       (or (< beg (pt))
                           (and (<= beg (pt))
                                (string? val)
                                (= 0 (string-length val)))))
              (set-pt! (if (< (pt) last-pt)
                           (if (and (string? val) (= 0 (string-length val)))
                               (max (- beg 1) (begv))
                               beg)
                           end))
              (set! check-composition #t)
              (set! check-invisible #t))))
        (set! check-display #f)
        ;; --- invisible branch ---
        (when (and check-invisible (> (pt) (begv)) (< (pt) (zv)))
          (let*-values (((e el) (scan-invisible-forward (pt) #f)))
            (let*-values (((beg end ellipsis)
                           (let*-values (((b el2) (scan-invisible-backward (pt) el)))
                             (values b e el2))))
              (when (and (< beg (pt)) (> end (pt)))
                (set-pt! (if (and (= orig-pt (pt))
                                  (or (< last-pt beg) (> last-pt end)))
                             (begin (set! orig-pt -1)
                                    (if (< (pt) last-pt) end beg))
                             (if (< (pt) last-pt) beg end)))
                (set! check-composition #t)
                (set! check-display #t))
              ;; Pretend the area doesn't exist if the buffer is not modified.
              (when (and (not modified) (not ellipsis) (< beg end))
                (cond
                 ((and (= last-pt beg) (= (pt) end) (< end (zv)))
                  (set! check-composition #t)
                  (set! check-display #t)
                  (set-pt! (+ end 1)))
                 ((and (= last-pt end) (= (pt) beg) (> beg (begv)))
                  (set! check-composition #t)
                  (set! check-display #t)
                  (set-pt! (- beg 1)))
                 ((= (pt) (if (< (pt) last-pt) beg end))
                  ;; We've already moved as far as we can; trying to go
                  ;; to the other end would mean moving backwards.
                  #f)
                 (else
                  (let ((val ((%c 'get-pos-property) (pt) 'invisible #nil)))
                    (if (and (> (invisible-level val) 0)
                             (let ((val2 ((%c 'get-pos-property)
                                          (if (= (pt) beg) end beg)
                                          'invisible #nil)))
                               (= (invisible-level val2) 0)))
                        (begin
                          (set! check-composition #t)
                          (set! check-display #t)
                          (set-pt! (if (= (pt) beg) end beg))))))))))
        (set! check-invisible #f)
        (comp-loop))))))
;;;;
;;;; M7d — command_loop_1 entry point
;;;;

(define (command-loop-1)
  "Top-level command-loop body, called by C `command_loop_1' via
`internal_condition_case'.  Runs the prologue once, then iterates:

  pre-read → dispatch → post-dispatch → mark-region → finalize

with two early-exit paths from pre-read:
  outcome 1 (EOF, end of kbd-macro replay) — return nil to C.
  outcome 2 (menu rejected) — skip dispatch, jump straight to finalize.

The Scheme tail-call loop replaces the C while/goto control flow of
the original command_loop_1 body verbatim.  See docs/keyboard.org §M7d."
  (command-loop-1-prologue)
  (let loop ()
    (let ((outcome (command-loop-1-iter-pre-read)))
      (cond
       ((= outcome 1) #nil)                ; EOF
       ((= outcome 2)                      ; goto finalize
        (command-loop-1-finalize)
        (loop))
       (else
        (command-loop-1-iter-dispatch)
        (command-loop-1-iter-post-dispatch)
        (command-loop-1-iter-mark-region)
        (command-loop-1-finalize)
        (loop))))))

;;;;
;;;; M7f — cmd-error (ported from static C cmd_error)
;;;;

(define %executing-kbd-macro-c-p
  (delay (%c '--executing-kbd-macro-c-p)))
(define %clear-executing-kbd-macro
  (delay (%c '--clear-executing-kbd-macro)))
(define %executing-kbd-macro-iterations
  (delay (%c '--executing-kbd-macro-iterations)))
(define %display-hourglass-p (delay (%c '--display-hourglass-p)))
(define %cancel-hourglass    (delay (%c '--cancel-hourglass)))
(define %signal-quit-p       (delay (%c '--signal-quit-p)))
(define %signaling-function  (delay (%c '--signaling-function)))
(define %signaling-function-set! (delay (%c '--signaling-function-set!)))

(define (cmd-error data)
  "Top-of-command-loop error handler.  DATA is (error-symbol .
error-data).  Cancels hourglass and kbd-macro replay (or finalizes
chars if the macro is being recorded and got a minibuffer-quit),
binds standard-output / standard-input / print-level / print-length
for safe error display, calls cmd-error-internal, then clears
quit-flag and inhibit-quit.  Returns 0 (fixnum) so the loop in
command-loop-2 / top-level-1 treats it as non-nil and continues
iterating.

Mirrors the static C cmd_error in src/keyboard.c."
  ;; Hourglass — no-op in batch / TTY.
  (when (not (%nilp ((force %display-hourglass-p))))
    ((force %cancel-hourglass)))

  ;; Build kbd-macro iteration prefix.
  (let* ((kbd-macro-active? (not (%nilp ((force %executing-kbd-macro-c-p)))))
         (macroerror
          (cond
           ((not kbd-macro-active?) "")
           ((= ((force %executing-kbd-macro-iterations)) 1)
            "After 1 kbd macro iteration: ")
           (else
            (format #f "After ~a kbd macro iterations: "
                    ((force %executing-kbd-macro-iterations))))))
         (conditions
          ((%c 'get) ((%c 'car) data) 'error-conditions)))

    (if (%nilp ((%c 'memq) 'minibuffer-quit conditions))
        ;; Not a minibuffer-quit: abort any macro replay.
        ((force %clear-executing-kbd-macro))
        ;; Else, if M-x command signaled minibuffer-quit while a kbd
        ;; macro is being defined, finalize the chars buffered so far.
        (let ((kb ((force %current-kboard))))
          (when (not (%nilp ((force %kboard-defining-kbd-macro) kb)))
            ((force %finalize-kbd-macro-chars)))))

    ;; specbind on the elisp side (these vars used to be C specpdl).
    (let ((saved-output (symbol-value 'standard-output))
          (saved-input  (symbol-value 'standard-input))
          (saved-level  (symbol-value 'print-level))
          (saved-length (symbol-value 'print-length))
          (kb           ((force %current-kboard))))
      (dynamic-wind
        (lambda ()
          (set-symbol-value! 'standard-output #t)
          (set-symbol-value! 'standard-input  #t)
          (set-symbol-value! 'print-level     10)
          (set-symbol-value! 'print-length    10))
        (lambda ()
          ((force %set-kboard-prefix-arg)      kb #nil)
          ((force %set-kboard-last-prefix-arg) kb #nil)
          ((force %cancel-echoing))
          (cmd-error-internal! data macroerror))
        (lambda ()
          (set-symbol-value! 'standard-output saved-output)
          (set-symbol-value! 'standard-input  saved-input)
          (set-symbol-value! 'print-level     saved-level)
          (set-symbol-value! 'print-length    saved-length)))))

  (set-symbol-value! 'quit-flag    #nil)
  (set-symbol-value! 'inhibit-quit #nil)
  0)

;;;;
;;;; M7g — command-error-default-function (default value of
;;;; `command-error-function').  See docs/keyboard.org §M7g.
;;;;

(define %selected-frame-glyphs-initialized-p
  (delay (%c '--selected-frame-glyphs-initialized-p)))
(define %selected-frame-initial-p
  (delay (%c '--selected-frame-initial-p)))
(define %daemon-not-yet-running-p
  (delay (%c '--daemon-not-yet-running-p)))
(define %print-error-message    (delay (%c '--print-error-message)))
(define %clear-message-1-0      (delay (%c '--clear-message-1-0)))
(define %message-log-maybe-newline
  (delay (%c '--message-log-maybe-newline)))
(define %bitch-at-user          (delay (%c '--bitch-at-user)))

(define (command-error-default-function data context signal)
  "Default value of `command-error-function'.  DATA is (error-symbol .
error-data); CONTEXT is a string (typically the macroerror prefix);
SIGNAL is the signaling function name (or nil).

Either prints to stderr and exits -1 (when the frame can't yet
display, or in batch / daemon-init), or clears the echo area, dings
or bitches at the user, and prints to both stderr and the message
log.  Mirrors src/keyboard.c Fcommand_error_default_function."
  ;; CHECK_STRING on context — let elisp signal wrong-type-argument
  ;; if a non-string slipped through.
  (let* ((conditions ((%c 'get) ((%c 'car) data) 'error-conditions))
         (is-minibuffer-quit?
          (not (%nilp ((%c 'memq) 'minibuffer-quit conditions))))
         (write-to-stderr?
          (and (not is-minibuffer-quit?)
               (or (%nilp ((force %selected-frame-glyphs-initialized-p)))
                   (and (%nilp ((force %daemon-not-yet-running-p)))
                        (not (%nilp ((force %selected-frame-initial-p)))))
                   (not (%nilp (symbol-value 'noninteractive)))))))
    (cond
     (write-to-stderr?
      ((force %print-error-message) data 'external-debugging-output
       context signal)
      ((%c 'terpri) 'external-debugging-output #nil)
      ((%c 'kill-emacs) -1 #nil))
     (else
      ((force %clear-message-1-0))
      ((force %message-log-maybe-newline))
      (cond
       (is-minibuffer-quit?
        ((%c 'ding) #t))
       (else
        ((%c 'discard-input))
        ((force %bitch-at-user))))
      ;; DEBUG: also print errors to stderr for debugging
      ((force %print-error-message) data 'external-debugging-output
       context signal)
      ((%c 'terpri) 'external-debugging-output #nil)
      ((force %print-error-message) data #t context signal))))
  #nil)

;;;;
;;;; M7e — command_loop_2 / top_level_1 outer drivers
;;;;

(define %eval-top-level  (delay (%c '--eval-top-level)))

(define (%catch-cmd-error thunk)
  "Run THUNK; if it throws an elisp-condition, route the (error-sym .
error-data) cons to cmd-error and return its result (a fixnum 0).
Mirrors internal_condition_case (..., Qt, cmd_error)."
  (catch 'elisp-condition
    thunk
    (lambda (key err-sym err-data)
      (cmd-error (cons err-sym err-data)))))

(define (command-loop-2)
  "C command_loop_2's body in Scheme.  Loops command-loop-1 inside a
catch on 'elisp-condition (handler = cmd-error).  Exits when
command-loop-1 returns nil — end of file in -batch, or end of
kbd-macro replay.  Mirrors src/keyboard.c command_loop_2 (lines
1278-1288)."
  (let loop ()
    (let ((val (%catch-cmd-error (lambda () (command-loop-1)))))
      (when (not (%nilp val)) (loop))))
  #nil)

(define %command-loop-level (delay (%c '--command-loop-level)))
(define %minibuffer-depth   (delay (%c 'minibuffer-depth)))
(define %call-with-catch    (delay (%c 'call-with-catch)))
(define %clear-executing-kbd-macro-c-only
  (delay (%c '--clear-executing-kbd-macro-c-only)))

(define (command-loop-main)
  "Body of `command_loop' after the C-side sigsetjmp / stack-overflow
recovery setup.  Two cases:

  (recursive)  command-loop-level > 0 OR minibuffer-depth > 0
               Run command-loop-2 once under a `catch on `exit',
               clear the C-only executing-kbd-macro shadow, return
               whatever command-loop-2 yielded.  This is the
               recursive-edit path.

  (top-level)  Otherwise run forever, alternating top-level-1 and
               command-loop-2 under separate `catch'es on `top-level'.
               In -batch mode the inner kill-emacs exits the loop.

Mirrors src/keyboard.c command_loop (lines 1302-1319).  See
docs/keyboard.org §M7h."
  (if (or (> ((force %command-loop-level)) 0)
          (> ((force %minibuffer-depth)) 0))
      (let ((val ((force %call-with-catch) 'exit
                  (lambda () (command-loop-2)))))
        ((force %clear-executing-kbd-macro-c-only))
        val)
      (let loop ()
        ((force %call-with-catch) 'top-level
         (lambda () (top-level-1)))
        ((force %call-with-catch) 'top-level
         (lambda () (command-loop-2)))
        ((force %clear-executing-kbd-macro-c-only))
        ;; End of file in -batch run causes exit here.
        (when (not (%nilp (symbol-value 'noninteractive)))
          ((%c 'kill-emacs) #t #nil))
        (loop))))

(define (top-level-1)
  "C top_level_1's body in Scheme.  Runs the startup expression
installed in `top-level' under cmd-error handling; if no startup
expression is set, displays one of the two `Bare Emacs' messages.
Mirrors src/keyboard.c top_level_1 (lines 1306-1317)."
  (cond
   ((not (%nilp (symbol-value 'top-level)))
    (%catch-cmd-error (force %eval-top-level)))
   ((not (%nilp (symbol-value 'purify-flag)))
    ((%c 'message) "Bare impure Emacs (standard Lisp code not loaded)"))
   (else
    ((%c 'message) "Bare Emacs (standard Lisp code not loaded)")))
  #nil)

;;;;
;;;; M22 imp-4 — safe_run_hooks family
;;;;
;;; Ported from src/keyboard.c (safe_run_hooks_1, safe_run_hooks_error,
;;; safe_run_hook_funcall, safe_run_hooks, safe_run_hooks_2,
;;; safe_run_hooks_maybe_narrowed).  run-hook-with-args-1 reimplements
;;; the walk done by the src/eval.c run_hook_with_args helper (which
;;; stays in C — it is not static, and six other call sites still use
;;; it).  The three public entries are the thin-dispatcher
;;; targets for the retained C safe_run_hooks / safe_run_hooks_2 and the
;;; C callers of the narrowed variant; the two helpers stay private.

;; Cache for the narrowing shims added with this port.  The C guard
;; compares the computed region against the buffer's *absolute* bounds
;; (BEG/Z), not the current narrowed bounds (BEGV/ZV), so mirror that
;; with --buffer-beg/--buffer-end.
(define %get-large-narrowing-begv (delay (%c '--get-large-narrowing-begv)))
(define %get-large-narrowing-zv   (delay (%c '--get-large-narrowing-zv)))
(define %buffer-beg               (delay (%c '--buffer-beg)))
(define %buffer-end               (delay (%c '--buffer-end)))

;; Specbind inhibit-quit = t for the duration of THUNK, restoring the
;; saved value on the way out.  Mirrors the C dynwind_begin + specbind
;; (Qinhibit_quit, Qt) + dynwind_end bracket.
(define (specbind-inhibit-quit! thunk)
  (let ((saved (symbol-value 'inhibit-quit)))
    (dynamic-wind
      (lambda () (set-symbol-value! 'inhibit-quit #t))
      thunk
      (lambda () (set-symbol-value! 'inhibit-quit saved)))))

;; True when X is elisp t (C EQ (x, Qt)).  The runtime bridges Qt to
;; Scheme #t; the defensive 't check mirrors buffer-locals.scm:358.
(define (elisp-t? x)
  (or (eq? x #t) (eq? x 't)))

;; Copy of VAL with every element eq? to FUN removed.  Returns two
;; values: (found? forward-order-new-list), mirroring the local- and
;; default-part scans in safe_run_hooks_error (all occurrences are
;; removed; the accumulator is reversed to restore forward order).
(define (strip-hook-fun val fun)
  (let loop ((tail val) (found #f) (acc '()))
    (if (pair? tail)
        (if (eq? fun (car tail))
            (loop (cdr tail) #t acc)
            (loop (cdr tail) found (cons (car tail) acc)))
        (values found (reverse acc)))))

;; safe-run-hook-funcall: run FUN with ARGS under an error trampoline
;; (catch 'elisp-condition).  On error, report with `message' and remove
;; FUN from the hook: from the local value first (set), else from the
;; default value (set-default).  Replaces safe_run_hooks_1 +
;; safe_run_hook_funcall + safe_run_hooks_error.
(define (safe-run-hook-funcall hook fun . args)
  (catch 'elisp-condition
    (lambda () (apply (%c 'funcall) (cons fun args)))
    (lambda (key err-sym err-data)
      ((%c 'message) "Error in %s (%S): %S"
       hook fun (cons err-sym err-data))
      (call-with-values
          (lambda ()
            (strip-hook-fun (if ((%c 'boundp) hook)
                                (symbol-value hook)
                                #nil)
                            fun))
        (lambda (found newval)
          (if found
              (set-symbol-value! hook newval)
              (call-with-values
                  (lambda ()
                    (strip-hook-fun (if (not (%nilp ((%c 'default-boundp) hook)))
                                        ((%c 'default-value) hook)
                                        #nil)
                                    fun))
                (lambda (found2 newval2)
                  (when found2
                    ((%c 'set-default) hook newval2))))))))))

;; run-hook-with-args-1: call each function in HOOK's value with
;; EXTRA-ARGS.  Reimplements the walk done by the src/eval.c
;; run_hook_with_args helper (which stays in C — it is not static, and
;; six other call sites still use it).  The Lisp run-hook-with-args
;; primitive is a different, error-free shape and is not used here.
(define (run-hook-with-args-1 hook . extra-args)
  (if (not ((%c 'fboundp) 'run-hooks))
      #nil
      (let ((val (if ((%c 'boundp) hook) (symbol-value hook) #nil)))
        (cond
         ((%nilp val) #nil)
         ((or (not (pair? val))
              (not (%nilp ((%c 'functionp) val))))
          (apply safe-run-hook-funcall hook val extra-args))
         (else
          (let ((global (if (not (%nilp ((%c 'default-boundp) hook)))
                            ((%c 'default-value) hook)
                            #nil)))
            (let loop ((tail val))
              (when (pair? tail)
                (let ((elt (car tail)))
                  (if (elisp-t? elt)
                      ;; t means run the global (default) binding too.
                      (unless (%nilp global)
                        (if (or (not (pair? global))
                                (not (%nilp ((%c 'functionp) global))))
                            (apply safe-run-hook-funcall hook global extra-args)
                            (let loop2 ((g global))
                              (when (pair? g)
                                ;; A nested t should not occur; ignore it
                                ;; to avoid an endless loop (C comment).
                                (unless (elisp-t? (car g))
                                  (apply safe-run-hook-funcall hook (car g)
                                         extra-args))
                                (loop2 (cdr g))))))
                      (apply safe-run-hook-funcall hook elt extra-args)))
                (loop (cdr tail)))))
          #nil)))))

;; Replaces C safe_run_hooks.  Also used directly for the narrowed
;; variant's own calls via safe-run-hooks-maybe-narrowed!.
(define (safe-run-hooks! hook)
  (specbind-inhibit-quit! (lambda () (run-hook-with-args-1 hook))))

;; Replaces C safe_run_hooks_2.
(define (safe-run-hooks-2! hook arg1 arg2)
  (specbind-inhibit-quit!
   (lambda () (run-hook-with-args-1 hook arg1 arg2))))

;; Replaces C safe_run_hooks_maybe_narrowed.  When long-line
;; optimizations are active and the computed region differs from the
;; full accessible region, narrow before running and widen (plus restore
;; point) afterward — mirroring the C labeled_narrow_to_region
;; unwind-protect that dynwind_end triggers.
(define (safe-run-hooks-maybe-narrowed! hook)
  (specbind-inhibit-quit!
   (lambda ()
     (let ((did-narrow #f)
           (ptm #nil))
       (when (and (not (%nilp ((%c 'long-line-optimizations-p))))
                  (> (symbol-value 'long-line-optimizations-region-size) 0))
         (let ((begv ((force %get-large-narrowing-begv) ((%c 'point))))
               (zv ((force %get-large-narrowing-zv) ((%c 'point)))))
           ;; Compare against BEG/Z (absolute), not point-min/point-max
           ;; (BEGV/ZV): when the buffer is already narrowed, begv/zv
           ;; equal the current bounds exactly, yet C still narrows so
           ;; point gets restored.  (command-loop.scm Finding 2, cr.org)
           (unless (and (= begv ((force %buffer-beg)))
                        (= zv ((force %buffer-end))))
             (set! ptm ((%c 'point-marker)))
             ((%c 'internal--labeled-narrow-to-region)
              begv zv 'long-line-optimizations-in-command-hooks)
             (set! did-narrow #t))))
       (dynamic-wind
         (lambda () #t)
         (lambda () (run-hook-with-args-1 hook))
         (lambda ()
           (when did-narrow
             ((%c 'internal--labeled-widen)
              'long-line-optimizations-in-command-hooks)
             ((%c 'goto-char) ptm))))))))

;;;;
;;;; Registration
;;;;

(define (init-command-loop-registrations)
  "Expose --command-loop-1-prologue and --command-loop-1-iter-pre-read
as elisp functions so tests can exercise them directly.  Production
code reaches them through the C dispatch in command_loop_1_prologue /
command_loop_1_iter_pre_read."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((--command-loop-1-prologue           ,command-loop-1-prologue)
              (--command-loop-1-iter-pre-read      ,command-loop-1-iter-pre-read)
              (--command-loop-1-iter-dispatch      ,command-loop-1-iter-dispatch)
              (--command-loop-1-iter-post-dispatch ,command-loop-1-iter-post-dispatch)
              (--command-loop-1-iter-mark-region   ,command-loop-1-iter-mark-region)
              (--command-loop-1-finalize           ,command-loop-1-finalize)
              (--command-loop-1                    ,command-loop-1)
              (--command-loop-2                    ,command-loop-2)
              (--top-level-1                       ,top-level-1)
              (--command-loop-main                 ,command-loop-main)
              (--cmd-error                         ,cmd-error)
              ;; Hoisted from C (was Fcommand_error_default_function).
              (command-error-default-function      ,command-error-default-function)))
  ;; M23 imp-1 — local-only DEFVAR_* moved here from syms_of_keyboard.
  ;; Declare special so elisp let/setq compiles as dynamic, and set the
  ;; C default value (globals storage removed with the DEFVAR).
  (for-each
   (lambda (spec)
     (proclaim-special! (car spec))
     (unless (symbol-default-bound? (car spec))
       (set-symbol-default-value! (car spec) (cadr spec))))
   `((pre-command-hook              ,#nil)
     (post-command-hook             ,#nil)
     (disable-point-adjustment      ,#nil)
     (global-disable-point-adjustment ,#nil)
     (current-minibuffer-command    ,#nil)
     (this-command-keys-shift-translated ,#nil)
     (command-error-function        ,'command-error-default-function)
     (selection-inhibit-update-commands
      ,(list 'handle-switch-frame 'handle-select-window))
     (post-select-region-hook       ,#nil)
     ;; The four DEFVAR_* below live in modules that are lazily loaded
     ;; only (lispy-event / kbd-buffer / help-echo) — their load-time
     ;; top-level forms need C DEFUNs registered after prelude, so they
     ;; cannot be use-modules'd at boot.  Declare them here (an
     ;; eagerly-loaded module) so they are special + bound from the
     ;; start.  FIX-20260902-guilemacs: rehome when those modules become
     ;; boot-loadable.
     (double-click-fuzz             3)
     (input-pending-p-filter-events ,#t)
     (display-monitors-changed-functions ,#nil)
     (show-help-function            ,#nil))))

;;; M23 imp-4 — local-only DEFSYM symbols re-interned from Scheme.
;;; These 39 symbol names had a DEFSYM call site in syms_of_keyboard
;;; (src/keyboard.c) with no other C reader anywhere, so the call site
;;; was deleted (see brief.org Group 2).  Deleting it removes the name
;;; from make-docfile's defsym_name[]/lispsym[] bootstrap interning, so
;;; the symbol now exists only if Scheme interns it here.
;;;
;;; Interning via `intern' (rebound to the pure-Scheme elisp-intern at
;;; boot, utils.scm:566) returns the canonical Guile symbol for the
;;; name.  A Guile symbol always exists once string->symbol runs, so
;;; this re-interns the canonical object rather than creating a new
;;; identity.  For the 11 keyword names (leading ":") we additionally
;;; set the symbol's value to itself, the same self-evaluating-keyword
;;; idiom the reader uses (reader.scm elisp-intern-and-make-keyword).
;;; Keywords interned by `intern' alone would not self-evaluate.

(define (init-m23-imp4-registrations)
  "Intern the 39 local-only symbols deleted from syms_of_keyboard in
M23 imp-4 (brief.org Group 2).  Makes the 11 keyword names among them
self-evaluating, matching the elisp reader idiom."
  (define (intern-one! name)
    (let ((sym ((symbol-function 'intern) name #nil)))
      (when (and (> (string-length name) 0)
                 (char=? (string-ref name 0) #\:))
        (set-symbol-value! sym sym))
      sym))
  (for-each intern-one!
            '(":image" ":rtl" ":wrap" ":enable" ":visible" ":help"
              ":button" ":keys" ":key-sequence" ":label" ":vert-only"
              "activate-mark-hook" "command-error-default-function"
              "command-execute" "current-key-remap-sequence"
              "delayed-warnings-hook" "display-monitors-changed-functions"
              "echo-keystrokes" "encoded" "gui-set-selection"
              "handle-select-window" "handle-switch-frame"
              "help--append-keystrokes-help" "help-echo-inhibit-substitution"
              "internal-echo-keystrokes-prefix"
              "long-line-optimizations-in-command-hooks" "menu-enable"
              "mouse-fixup-help-message" "no-record" "post-command-hook"
              "post-select-region-hook" "pre-command-hook"
              "selection-request" "tty-select-active-regions" "undefined"
              "undo-auto--add-boundary" "undo-auto--undoably-changed-buffers"
              "window-edges" "xterm--set-selection")))

;;; M23 imp-5 — special-event-map registration.
;;;
;;; Ports keys_of_keyboard's special-event-map table (previously a
;;; ~76-line C table of initial_define_lispy_key calls in
;;; src/keyboard.c) out of C into Scheme.  keys_of_keyboard now holds a
;;; one-call dispatch to this function; it runs from src/emacs.c after
;;; syms_of_keyboard_globals has created Vspecial_event_map, so the map
;;; exists at this call site — unlike the prelude-boot call sites of
;;; init-command-loop-registrations / init-m23-imp4-registrations, which
;;; is why this registration must not be moved to prelude/load.scm.
;;;
;;; Each entry reproduces initial_define_lispy_key exactly: that C
;;; helper is store_in_keymap (map, intern KEY, intern DEF, false), and
;;; (define-key map (vector KEY) DEF) reduces to the same store_in_keymap
;;; call for a one-element, non-character vector key.
;;;
;;; Dropped-platform entries (Windows-only, out of scope per docs/
;;; milestone-overview.org "Platform scope") are deliberately not ported:
;;;   end-session → kill-emacs   (#ifdef HAVE_NTGUI)
;;;   language-change → ignore   (#if defined (WINDOWSNT))
;;; thread-event → thread-handle-event (#ifdef THREADS_ENABLED) is also
;;; not ported: this build has THREADS_ENABLED undefined and exposes no
;;; Scheme featurep predicate for threads, so the binding is dead here.

(define (init-m23-imp5-registrations)
  "Install the special-event-map entries keys_of_keyboard used to
register from C (initial_define_lispy_key).  Runs from keys_of_keyboard
at C boot, after Vspecial_event_map exists."
  (let ((sem (symbol-value 'special-event-map)))
    (define (bind! key def)
      ((%c 'define-key) sem (vector key) def))
    (bind! 'delete-frame        'handle-delete-frame)
    (bind! 'ns-put-working-text 'ns-put-working-text)
    (bind! 'ns-unput-working-text 'ns-unput-working-text)
    ;; Here we used to use `ignore-event' which would simple set prefix-arg
    ;; to current-prefix-arg, as is done in `handle-switch-frame'.  But
    ;; `handle-switch-frame is not run from the special-map.  Commands from
    ;; that map are run in a special way that automatically preserves the
    ;; prefix-arg.  Restoring the prefix arg here is not just redundant but
    ;; harmful: see the historical C comment in keys_of_keyboard
    ;; (iconify-frame entry) for the C-u C-x v = walk-through.
    (bind! 'iconify-frame       'ignore)
    (bind! 'make-frame-visible  'ignore)
    (bind! 'save-session        'handle-save-session)
    ;; select-window is intentionally NOT bound here.  Handling it at such
    ;; a low level caused read_key_sequence to get confused because it does
    ;; not realize that the current_buffer was changed by read_char (see
    ;; the commented-out initial_define_lispy_key in the historical C).
    (when (not (%nilp ((%c 'featurep) 'dbusbind)))
      ;; Define a special event raised for dbus callback functions.
      (bind! 'dbus-event 'dbus-handle-event))
    (when (not (%nilp (or ((%c 'featurep) 'inotify)
                          ((%c 'featurep) 'gfilenotify)
                          ((%c 'featurep) 'kqueue))))
      ;; Define a special event raised for notification callback functions.
      (bind! 'file-notify 'file-notify-handle-event))
    (bind! 'config-changed-event 'ignore)
    (bind! 'focus-in            'handle-focus-in)
    (bind! 'focus-out           'handle-focus-out)
    (bind! 'move-frame          'handle-move-frame)))
