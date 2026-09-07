;;; single-kboard.scm --- M27 imp-1: single-kboard family policy
;;;                  ((emacs single-kboard))
;;;
;;; Moves the *policy* inside not_single_kboard_state, push_kboard,
;;; pop_kboard, and temporarily_switch_to_single_kboard out of
;;; src/keyboard.c and into Scheme, over the M2 kboard smob.  See
;;; brief.org M27 imp-1 and docs/m27-plan.org Finding 6.
;;;
;;; Cross-file C callers (frame.c, xdisp.c, callint.c, minibuf.c,
;;; term.c, and the Fc_temporarily_switch_to_single_kboard DEFUN) keep
;;; thin C dispatcher entry points of the same name/signature; each
;;; dispatches here through scm_c_public_ref.  The raw pieces that must
;;; stay C are:
;;;
;;;   - the C static single_kboard flag — Scheme only has a setter
;;;     (--kbd-single-kboard-set!, added this imp) and the pre-existing
;;;     getter (--kbd-single-kboard-p);
;;;   - pop_kboard's raw `terminal_list' walk — exposed as
;;;     --kboard-live-p;
;;;   - the selected frame's KBOARD — exposed as
;;;     --selected-frame-kboard;
;;;   - the record_unwind_protect_int frame and its
;;;     restore_kboard_configuration unwind body, which stay C (see
;;;     docs/m27-plan.org Finding 6).  Its pop_kboard () call resolves
;;;     back through the C dispatcher to pop-kboard! here.
;;;
;;; The C `struct kboard_stack' node list is replaced 1:1 by the
;;; module-level `kboard-stack' list below.  Module-level mutable state
;;; is on purpose: it mirrors the old C static kboard_stack, with the
;;; same re-entrancy characteristics.
;;;
;;; Conventions (identical to M9-M26): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp nil is #nil.  Every call
;;; re-reads the C state fresh through the shims — no module-level
;;; mutable cache of the kboard itself.

(define-module (emacs single-kboard)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:declarative? #t
  #:export (not-single-kboard-state
            push-kboard!
            pop-kboard!
            temporarily-switch-to-single-kboard!))

(defelisp %current-kboard           current-kboard)
(defelisp %set-current-kboard       set-current-kboard)
(defelisp %kboard-eq                kboard-eq)
(defelisp %--kbd-single-kboard-set! --kbd-single-kboard-set!)
(defelisp %--kboard-live-p          --kboard-live-p)
(defelisp %--selected-frame-kboard  --selected-frame-kboard)

;; Replaces C `struct kboard_stack` + `static struct kboard_stack
;; *kboard_stack`.  Module-level mutable state on purpose: it mirrors
;; the C static 1:1 (same re-entrancy as before).
(define kboard-stack '())

;; Elisp truthiness: everything except #nil is true.
(define (truthy? x)
  (not (eq? x #nil)))

(define (not-single-kboard-state kb)
  ;; Wrap the kboard-eq Qt/Qnil result in truthy? — same idiom as
  ;; kbd-buffer.scm / main-queue.scm / read-char.scm and this module's
  ;; own temporarily-switch-to-single-kboard! (cr.org F2).
  (when (truthy? ((force %kboard-eq) kb ((force %current-kboard))))
    ((force %--kbd-single-kboard-set!) #nil)))

(define (push-kboard! kb)
  (set! kboard-stack (cons ((force %current-kboard)) kboard-stack))
  ((force %set-current-kboard) kb))

(define (pop-kboard!)
  (let ((saved (car kboard-stack)))
    (if ((force %--kboard-live-p) saved)
        ((force %set-current-kboard) saved)
        (begin
          ((force %set-current-kboard)
           ((force %--selected-frame-kboard)))
          ((force %--kbd-single-kboard-set!) #nil)))
    (set! kboard-stack (cdr kboard-stack))))

(define (temporarily-switch-to-single-kboard! was-locked kb)
  (if (truthy? was-locked)
      (push-kboard! ((force %current-kboard)))
      (when (truthy? kb)
        ((force %set-current-kboard) kb)))
  ((force %--kbd-single-kboard-set!) #t))
