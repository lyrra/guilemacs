(define-module (emacs command-loop)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (command-loop-1-prologue
            command-loop-1-iter-pre-read
            command-loop-1-iter-dispatch
            command-loop-1-iter-post-dispatch
            command-loop-1-iter-mark-region
            command-loop-1-finalize
            command-loop-1
            command-loop-2
            top-level-1
            command-loop-main
            cmd-error
            command-error-default-function
            init-command-loop-registrations))

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

(define (%c name) (symbol-function name))

;; Cache lookups for the C-side primitives used per command-loop entry.
(define %cancel-echoing                       (delay (%c '--cancel-echoing)))
(define %clear-waiting-for-input              (delay (%c '--clear-waiting-for-input)))
(define %set-this-command-key-count           (delay (%c '--set-this-command-key-count)))
(define %set-this-single-command-key-start    (delay (%c '--set-this-single-command-key-start)))
(define %safe-run-hooks-maybe-narrowed        (delay (%c '--safe-run-hooks-maybe-narrowed-selected)))
(define %safe-run-hooks                       (delay (%c '--safe-run-hooks)))
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
      ;; original safety.
      (when (and (not (%nilp (symbol-value 'post-command-hook)))
                 (fboundp 'run-hooks))
        ((force %safe-run-hooks-maybe-narrowed) 'post-command-hook))

      (when (not (%nilp ((force %echo-area-buffer-0-non-empty-p))))
        ((force %resize-echo-area-exactly)))

      (when (not (%nilp (symbol-value 'delayed-warnings-list)))
        ((force %safe-run-hooks) 'delayed-warnings-hook)))

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
(define %message1-clear                         (delay (lambda () (message #nil))))

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
          ((%c '--safe-run-hooks) 'echo-area-clear-hook)
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
(define %record-recent-keys-cmd-pseudo-event            (delay (%c '--record-recent-keys-cmd-pseudo-event)))
(define %with-hourglass-protection                      (delay (%c '--with-hourglass-protection)))
(define %save-point-before-last-command-or-undo         (delay (%c '--save-point-before-last-command-or-undo)))
(define %reset-redisplay-tick-state                     (delay (%c '--reset-redisplay-tick-state)))
(define %clear-display-working-on-window-p              (delay (%c '--clear-display-working-on-window-p)))
(define %safe-run-hooks-maybe-narrowed-selected         (delay (%c '--safe-run-hooks-maybe-narrowed-selected)))

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
        ((force %record-recent-keys-cmd-pseudo-event) cmd)

        (set-symbol-value! 'this-command      cmd)
        (set-symbol-value! 'real-this-command cmd)

        ;; pre-command-hook.
        ((force %safe-run-hooks-maybe-narrowed-selected) 'pre-command-hook)

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

    ((force %safe-run-hooks-maybe-narrowed) 'post-command-hook)

    ;; Resize echo area if the displayed message is on the selected
    ;; frame's minibuffer (Bug#34317 guard).
    (when (and (not (%nilp ((force %echo-area-buffer-0-non-empty-p))))
               (not (%nilp ((force %echo-area-window-eq-selected-frame-minibuf-p)))))
      ((force %resize-echo-area-exactly)))

    (when (not (%nilp (symbol-value 'delayed-warnings-list)))
      ((force %safe-run-hooks) 'delayed-warnings-hook))

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
                  (if (eq sar 'only)
                      (eq (if (pair? tmm) (car tmm) #nil) 'only)
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
(define %cmd-error-internal  (delay (%c '--cmd-error-internal)))

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
          ((force %cmd-error-internal) data macroerror))
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
              (--cmd-error                         ,cmd-error))))
