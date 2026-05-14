(define-module (emacs command-loop)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (command-loop-1-prologue
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

(define (init-command-loop-registrations)
  "Expose --command-loop-1-prologue as an elisp function so tests can
exercise the prologue directly.  Production code reaches the same
procedure through the C command_loop_1 → command_loop_1_prologue dispatch."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((--command-loop-1-prologue ,command-loop-1-prologue))))
