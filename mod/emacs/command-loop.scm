(define-module (emacs command-loop)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (command-loop-1-prologue
            command-loop-1-iter-pre-read
            command-loop-1-iter-dispatch
            command-loop-1-iter-post-dispatch
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
              (--command-loop-1-iter-post-dispatch ,command-loop-1-iter-post-dispatch))))
