(define-module (emacs recursive-edit)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (exit-recursive-edit
            abort-recursive-edit
            recursion-depth
            top-level
            init-recursive-edit-registrations))

;;; M4 — Three user-facing recursive-edit DEFUNs ported from
;;; keyboard.c.  See docs/keyboard.org §M4.
;;;
;;; The full recursive-edit machinery (Frecursive_edit,
;;; recursive_edit_unwind, restore_kboard_configuration, the
;;; command_loop_level mutations) stays C-owned.  Moving it would
;;; force a major cut through M7 (command_loop_1) territory — defer
;;; until that milestone.  These three functions are independent:
;;; they read C state (command_loop_level, minibuf_level) via
;;; `--' accessor subrs, signal user-error when called outside a
;;; recursive edit, and throw to the elisp `exit' tag (caught by
;;; the C-side internal_catch in command_loop).

(define (%c name) (symbol-function name))

(define (%user-error msg)
  ;; Elisp `signal' isn't bound in Scheme top-level — resolve via the
  ;; elisp symbol table.  Same pattern as (emacs recent-keys).
  ((%c 'signal) 'user-error (list msg)))

(define (%nesting>0?)
  (or (> ((%c '--command-loop-level)) 0)
      (> ((%c '--minibuf-level))      0)))

(define (exit-recursive-edit)
  "Exit the innermost recursive edit or minibuffer.  Throws to `exit'
with value nil so that the C-side command_loop's internal_catch
returns normally."
  (if (%nesting>0?)
      ((%c 'throw) 'exit #nil)
      (%user-error "No recursive edit is in progress")))

(define (abort-recursive-edit)
  "Abort the command that requested this recursive edit.  Throws to
`exit' with value t so that command_loop's internal_catch knows to
signal abort rather than return normally."
  (if (%nesting>0?)
      ((%c 'throw) 'exit #t)
      (%user-error "No recursive edit is in progress")))

(define (recursion-depth)
  "Return current command-loop-level + minibuffer-recursion-depth.
Mirrors the C body of Frecursion_depth."
  (+ ((%c '--command-loop-level))
     ((%c '--minibuf-level))))

(define (top-level)
  "Exit all recursive editing levels and active minibuffers by
throwing to the `top-level' tag.  Mirrors C Ftop_level.

Drops any held interrupt-input nesting first (a no-op in batch but
important when redisplay traps with input blocked during a tool-bar
update on a window system).  The HAVE_WINDOW_SYSTEM hourglass-cancel
that the C version did is deferred until M7 (it lives in xdisp.c
and is irrelevant in batch and TTY)."
  ((%c '--totally-unblock-input))
  ((%c 'throw) 'top-level #nil))

(define (init-recursive-edit-registrations)
  "Register the user-facing DEFUNs against their elisp symbols."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((exit-recursive-edit  ,exit-recursive-edit)
              (abort-recursive-edit ,abort-recursive-edit)
              (recursion-depth      ,recursion-depth)
              (top-level            ,top-level))))
