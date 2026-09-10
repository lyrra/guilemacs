;;; help-echo.scm --- M16 imp-2: Scheme help-echo bodies
;;;
;;; Ports three C bodies from src/keyboard.c as Scheme procedures,
;;; transliterated 1:1 from the C (docs/m16-plan.org §"Goal"):
;;; show-help-echo (show_help_echo, keyboard.c:3162-3196),
;;; gen-help-event (gen_help_event, :4744-4757), and store-help-event
;;; (kbd_buffer_store_help_event, :4763-4775).  Coexistence-only: the
;;; C bodies stay active and unchanged until the imp-3 cutover
;;; (brief.org §"Coexistence only").
;;;
;;; Reuse (brief.org §"Reuse — do not re-port"): help-echo-substitute-
;;; command-keys comes from (emacs menu-item-parse); the HELP_EVENT
;;; ring-append is kbd-buffer-store-event! (M13).  No new ring logic.
;;;
;;; Conventions (identical to M9-M15): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp variables via symbol-value /
;;; set-symbol-value!; #nil is elisp nil; no module-level mutable
;;; state — shared state lives only in the C globals the shims touch.
;;;
;;; ie-smob lifetime (M9 hard rule): an ie-smob from --ie-help-event is
;;; only valid until the enclosing C call returns.  It is passed
;;; straight to kbd-buffer-store-event! in the same call tree with no
;;; intervening funcall, and never held or cached.

(define-module (emacs help-echo)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:use-module (emacs menu-item-parse) ; help-echo-substitute-command-keys
  #:use-module (emacs kbd-buffer)     ; kbd-buffer-store-event! (M13)
  ;; M28 imp-5 family 6 — --some-mouse-moved reclaimed; call the port
  ;; directly.  (emacs kbd-buffer) already imports it, so no new cycle.
  #:use-module ((emacs read-key-sequence) #:select (some-mouse-moved))
  #:declarative? #t
  #:export (show-help-echo
            gen-help-event
            store-help-event))

;;; --- C shim references ---------------------------------------------

(defelisp %--ie-help-event            --ie-help-event)
(defelisp %--position-to-time         --position-to-time)
(defelisp %--safe-calln-or-eval       --safe-calln-or-eval)
(defelisp %--rc-help-echo-showing-set! --rc-help-echo-showing-set!)
(defelisp %--frame-set-mouse-moved!   --frame-set-mouse-moved!)
;; M28 imp-5 family 6 — --some-mouse-moved reclaimed; call the
;; (emacs read-key-sequence) port directly (imported above).
(defelisp %windowp                    windowp)
(defelisp %funcall                    funcall)

;;; --- Helpers --------------------------------------------------------

(define (truthy? x)
  "Elisp truthiness: everything except #nil is true."
  (not (eq? x #nil)))

;;; --- gen-help-event --------------------------------------------------

;;; Port of C gen_help_event (keyboard.c:4744-4757).  Field order
;;; matches C: frame_or_window = FRAME, arg = OBJECT, x = WINDOWP
;;; (WINDOW) ? WINDOW : FRAME, y = HELP, timestamp = position_to_Time
;;; (POS).  Returns nothing meaningful (C returns void).
(define (gen-help-event help frame window object pos)
  (let* ((x (if ((force %windowp) window) window frame))
         (timestamp ((force %--position-to-time) pos))
         (ie ((force %--ie-help-event) frame object x help timestamp)))
    ;; Same call tree — no intervening funcall (M9 ie-smob lifetime).
    (kbd-buffer-store-event! ie #f)))

;;; --- store-help-event -------------------------------------------------

;;; Port of C kbd_buffer_store_help_event (keyboard.c:4763-4775).
;;; arg = nil, x = nil, timestamp = 0 (hard-coded — C does not call
;;; position_to_Time here).  Returns nothing meaningful.
(define (store-help-event frame help)
  (let ((ie ((force %--ie-help-event) frame #nil #nil help 0)))
    (kbd-buffer-store-event! ie #f)))

;;; --- show-help-echo ---------------------------------------------------

;;; Port of C show_help_echo (keyboard.c:3162-3196).  Step order
;;; matters (brief.org §"Do not"):
;;;   1. non-nil, non-string HELP resolves through --safe-calln-or-eval
;;;      (the untrusted-call containment shim); a non-string result
;;;      stops — bare return, no shared-cell write.
;;;   2. noninteractive + string HELP: save mouse_moved with
;;;      --some-mouse-moved BEFORE the mouse-fixup-help-message call,
;;;      restore with --frame-set-mouse-moved! AFTER it.
;;;   3. string or nil HELP: call show-help-function (if set) with the
;;;      substituted help, then write help_echo_showing_p through
;;;      --rc-help-echo-showing-set! — the last step, unconditional in
;;;      this branch.  Returns nothing meaningful.
(define (show-help-echo help window object pos)
  (let ((help
         (if (and (not (eq? help #nil)) (not (string? help)))
             (let ((r ((force %--safe-calln-or-eval) help window object pos)))
               (if (string? r) r #:stop)) ; #:stop = C bare return
             help)))
    (unless (eq? help #:stop)
      (when (and (not (truthy? (symbol-value 'noninteractive)))
                 (string? help))
        ;; Save BEFORE the call, restore AFTER it (never before).
        (let ((f (some-mouse-moved)))
          (set! help ((force %funcall) 'mouse-fixup-help-message help))
          (when (not (eq? f #nil))
            ((force %--frame-set-mouse-moved!) f))))
      (when (or (string? help) (eq? help #nil))
        (when (not (eq? (symbol-value 'show-help-function) #nil))
          ((force %funcall) (symbol-value 'show-help-function)
           (help-echo-substitute-command-keys help)))
        ((force %--rc-help-echo-showing-set!) (string? help))))))