(define-module (emacs recursive-edit)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:use-module (emacs command-loop)
  #:declarative? #t
  #:export (exit-recursive-edit
            abort-recursive-edit
            recursion-depth
            top-level
            recursive-edit
            recursive-edit-1
            init-recursive-edit-registrations))

;;; M4 + M22 imp-2 — recursive-edit machinery ported from keyboard.c.
;;; See docs/keyboard.org §M4 and docs/m22-plan.org §imp-2.
;;;
;;; M4: the three user-facing DEFUNs (exit/abort/recursion-depth) and
;;; top-level were ported first.  M22 imp-2 moves the core body too:
;;; Frecursive_edit is now a thin C dispatcher whose whole body is the
;;; Scheme `recursive-edit' below, and recursive_edit_1 is a thin C
;;; dispatcher to `recursive-edit-1'.  cmd_error_internal's logic moved
;;; to (emacs command-loop) cmd-error-internal!.
;;;
;;; Specpdl-order note (see docs/m22-plan.org §imp-2 Risk 2): the C
;;; dispatcher keeps a dynwind bracket so temporarily_switch_to_single_
;;; kboard's kboard-restore still fires at dynwind_end — i.e. on throw as
;;; well as normal return.  The buffer/level restore is this module's
;;; dynamic-wind after-thunk, which runs before that C dynwind_end, so
;;; restore order on exit is: buffer/level first, then kboard.  This is
;;; the reverse of the old C LIFO order (kboard then buffer/level); it
;;; only matters in a multi-tty session and is the order the dynamic-wind
;;; structure in brief.org prescribes.


;;; --- C-only recursive-edit state accessors (M22 imp-2 shims) ---
(define %input-blocked-p                  (delay (%c '--input-blocked-p)))
;; --command-loop-level is read fresh each call (see %nesting>0? below for
;; why), not via a cached delay.
(define %command-loop-level-increment!    (delay (%c '--command-loop-level-increment!)))
(define %command-loop-level-decrement!    (delay (%c '--command-loop-level-decrement!)))
(define %update-mode-lines-set!           (delay (%c '--update-mode-lines-set!)))
(define %redisplaying-p-clear!            (delay (%c '--redisplaying-p-clear!)))
(define %temporarily-switch-to-single-kboard!
  (delay (%c '--temporarily-switch-to-single-kboard!)))
(define %recursive-edit-quit!             (delay (%c '--recursive-edit-quit!)))
(define %cancel-hourglass                 (delay (%c '--cancel-hourglass)))

;;; --- plain elisp helpers (resolved via %c, codebase convention) ---
(define %current-buffer   (delay (%c 'current-buffer)))
(define %selected-window  (delay (%c 'selected-window)))
(define %window-buffer    (delay (%c 'window-buffer)))
(define %set-buffer       (delay (%c 'set-buffer)))
(define %buffer-p         (delay (%c 'bufferp)))
(define %funcall          (delay (%c 'funcall)))
(define %functionp        (delay (%c 'functionp)))
(define %signal           (delay (%c 'signal)))
(define %list             (delay (%c 'list)))
(define %makunbound       (delay (%c 'makunbound)))

(define (%nilp x)
  ;; Recognize all three nil-equivalents: elisp nil symbol (#nil), the
  ;; empty list, and Scheme #f.
  (or (null? x) (not x)))

;;; symbol-value-safe / symbol-restore — save and restore an elisp
;;; variable that may be unbound (void-variable).  The C prologue used
;;; specbind, which binds even unbound variables and unbinds them again
;;; on unwind.  undo-auto--undoably-changed-buffers is an elisp defvar
;;; (not a C DEFVAR) so it is void during early startup.
(define (symbol-value-safe name)
  (catch 'elisp-condition
    (lambda () (list 'value (symbol-value name)))
    (lambda (key . args)
      (if (and (eq? key 'elisp-condition)
               (pair? args)
               (eq? (car args) 'void-variable))
          (list 'void)
          (apply throw key args)))))

(define (symbol-restore name saved)
  (if (eq? (car saved) 'void)
      ((force %makunbound) name)
      (set-symbol-value! name (cadr saved))))

(define (%user-error msg)
  ;; Elisp `signal' isn't bound in Scheme top-level — resolve via the
  ;; elisp symbol table.  Same pattern as (emacs recent-keys).
  ((force %signal) 'user-error (list msg)))

(define (%nesting>0?)
  ;; Resolve --command-loop-level / --minibuf-level fresh each call (not
  ;; via the cached delay) so the m4 ERT tests can mock them with
  ;; cl-letf on symbol-function.
  (or (> ((%c '--command-loop-level)) 0)
      (> ((%c '--minibuf-level))      0)))

;;; ---------------------------------------------------------------------
;;; M22 imp-2 — recursive_edit_1 body (prologue + command loop + tail).
;;; This is what both Frecursive_edit's Scheme body and read_minibuf
;;; (via the C thin dispatcher) run.  The prologue binds a few elisp vars
;;; for the duration of the loop; they are restored on the way out (the
;;; dynamic-wind after-thunk), matching the old specpdl scoping.

(define (recursive-edit-1)
  (let* ((saved-output         (symbol-value-safe 'standard-output))
         (saved-input          (symbol-value-safe 'standard-input))
         (saved-symbols-pos    (symbol-value-safe 'symbols-with-pos-enabled))
         (saved-print-bare     (symbol-value-safe 'print-symbols-bare))
         (saved-inhibit-redisp (symbol-value-safe 'inhibit-redisplay))
         (saved-undo           (symbol-value-safe 'undo-auto--undoably-changed-buffers)))
    (dynamic-wind
      ;; Entry: apply the prologue bindings.
      (lambda ()
        (when (> ((%c '--command-loop-level)) 0)
          (set-symbol-value! 'standard-output #t)
          (set-symbol-value! 'standard-input  #t)
          (set-symbol-value! 'symbols-with-pos-enabled #nil)
          (set-symbol-value! 'print-symbols-bare #nil))
        ;; The command loop started an hourglass timer; cancel it so it
        ;; does not fire during the (possibly long) recursive edit.
        ((force %cancel-hourglass))
        ;; This may have been called from a debugger inside redisplay;
        ;; allow redisplay in the debugging session.
        (set-symbol-value! 'inhibit-redisplay #nil)
        ((force %redisplaying-p-clear!))
        ;; Changes inside the recursive edit must not add undo boundaries
        ;; to buffers changed before we entered (Bug #23632).
        (set-symbol-value! 'undo-auto--undoably-changed-buffers #nil))
      ;; Body: run the editor command loop (M7h) and dispatch on its
      ;; throw value.
      (lambda ()
        (let ((val (command-loop-main)))
          (cond
           ((eq? val #t)
            ;; abort-recursive-edit threw t: quit this recursive edit.
            ((force %recursive-edit-quit!)))
           ((string? val)
            ;; read_minibuf throw with a string: signal an error.
            ((force %signal) 'error ((force %list) val)))
           ((not (%nilp ((force %functionp) val)))
            ;; A function value: call it, then return normally.
            ((force %funcall) val))
           (else
            #nil))))
      ;; After: restore the prologue bindings.
      (lambda ()
        (symbol-restore 'standard-output saved-output)
        (symbol-restore 'standard-input  saved-input)
        (symbol-restore 'symbols-with-pos-enabled saved-symbols-pos)
        (symbol-restore 'print-symbols-bare saved-print-bare)
        (symbol-restore 'inhibit-redisplay saved-inhibit-redisp)
        (symbol-restore 'undo-auto--undoably-changed-buffers saved-undo)))))

;;; ---------------------------------------------------------------------
;;; M22 imp-2 — Frecursive_edit body.  Ports the old C body exactly, in
;;; the order brief.org specifies: input-blocked check, buffer compute,
;;; level increment, kboard switch (when nested), recursive-edit-1, then
;;; buffer/level restore as the dynamic-wind after-thunk.

(define (recursive-edit)
  (if (not (%nilp ((force %input-blocked-p))))
      ;; If we enter while input is blocked, don't lock up here.  This
      ;; may happen through the debugger during redisplay.
      #nil
      (let ((buffer
             (if (and (>= ((%c '--command-loop-level)) 0)
                      (not (eq? ((force %current-buffer))
                                ((force %window-buffer)
                                 ((force %selected-window))))))
                 ((force %current-buffer))
                 #nil)))
        ((force %command-loop-level-increment!))
        ((force %update-mode-lines-set!) 17)
        (dynamic-wind
          (lambda () #f)
          (lambda ()
            ;; When nested, restore single_kboard the way command_loop_1
            ;; would (M27-owned C, reached via the shim).
            (when (> ((%c '--command-loop-level)) 0)
              ((force %temporarily-switch-to-single-kboard!)))
            (recursive-edit-1))
          (lambda ()
            ;; recursive_edit_unwind replacement.
            (when (not (%nilp ((force %buffer-p) buffer)))
              ((force %set-buffer) buffer))
            ((force %command-loop-level-decrement!))
            ((force %update-mode-lines-set!) 18))))))

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
