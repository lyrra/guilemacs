(define-module (emacs cell-accessors)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (--set-echoing!
            --echoing-p
            --set-ignore-mouse-drag-p
            --clear-ignore-mouse-drag
            --clear-display-working-on-window-p
            init-cell-accessors-registrations))

;;; M30 imp-2 — plain bool cell accessors, moved from per-cell DEFUNs
;;; in src/keyboard.c to the table-driven subrs --cell-ref and
;;; --cell-set! (see the `cell_table' in src/keyboard.c).  The old
;;; accessor names are kept, so the mod/ call sites — which resolve the
;;; name in the elisp function slot via %c — do not change.
;;;
;;; The table key is the canonical accessor name: a read uses the same
;;; name as the write.  Each bool cell reads/writes through one name:
;;;
;;;   --set-echoing!                     -> echoing
;;;   --set-ignore-mouse-drag-p          -> ignore_mouse_drag_p
;;;   --clear-display-working-on-window-p -> display_working_on_window_p
;;;
;;; A read of a clear-named cell is not needed by any caller, so only
;;; the write name is exported.
;;;
;;; `waiting_for_input' is NOT here.  It is a per-thread field
;;; (`current_thread->m_waiting_for_input', src/thread.h:164), so its
;;; address is not a constant expression and cannot enter the static
;;; `cell_table'.  Its subrs (`--clear-waiting-for-input',
;;; `--waiting-for-input-p') stay C.  See docs/m30-plan.org §imp-2.
;;;
;;; The C writers of `echoing' stay in the signal handlers.  This
;;; module is an extra reader and writer, not the only writer.

;;; --- the table subrs ------------------------------------------------

(define (%cell-ref name)
  ((%c '--cell-ref) name))

(define (%cell-set! name value)
  ((%c '--cell-set!) name value))

;;;;
;;;; echoing
;;;;

(define (--set-echoing! value)
  "Write VALUE to the C `echoing' flag through the cell table.
The C writer in the signal handlers stays; this is an extra writer."
  (%cell-set! '--set-echoing! value))

(define (--echoing-p)
  "Return the C `echoing' flag read through the cell table."
  (%cell-ref '--set-echoing!))

;;;;
;;;; ignore_mouse_drag_p
;;;;

(define (--set-ignore-mouse-drag-p value)
  "Write VALUE to `ignore_mouse_drag_p' (non-nil -> true)."
  (%cell-set! '--set-ignore-mouse-drag-p value))

(define (--clear-ignore-mouse-drag)
  "Clear `ignore_mouse_drag_p' through the cell table."
  (%cell-set! '--set-ignore-mouse-drag-p #nil))

;;;;
;;;; display_working_on_window_p
;;;;

(define (--clear-display-working-on-window-p)
  "Clear `display_working_on_window_p' through the cell table."
  (%cell-set! '--clear-display-working-on-window-p #nil))

;;; --- registration ---------------------------------------------------

(define (init-cell-accessors-registrations)
  "Register the converted bool accessors against their elisp symbols."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((--set-echoing!                     ,--set-echoing!)
              (--echoing-p                        ,--echoing-p)
              (--set-ignore-mouse-drag-p          ,--set-ignore-mouse-drag-p)
              (--clear-ignore-mouse-drag          ,--clear-ignore-mouse-drag)
              (--clear-display-working-on-window-p
               ,--clear-display-working-on-window-p))))
