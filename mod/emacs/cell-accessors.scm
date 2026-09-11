(define-module (emacs cell-accessors)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (--set-echoing!
            --echoing-p
            --set-ignore-mouse-drag-p
            --clear-ignore-mouse-drag
            --clear-display-working-on-window-p
            --set-down-mouse-line-number-width
            --set-last-mouse-button
            --set-last-mouse-x
            --set-last-mouse-y
            --set-double-click-count
            --set-menu-bar-items-index
            --set-tab-bar-items-count
            --set-tool-bar-items-count
            --set-windows-or-buffers-changed
            --set-raw-keybuf-count
            --set-frame-relative-event-pos
            --set-menu-bar-items-vector
            --set-tab-bar-items-vector
            --set-tool-bar-items-vector
            --set-menu-bar-one-keymap-changed-items
            --set-menu-bar-touch-id
            --set-internal-last-event-frame
            --set-unread-switch-frame
            --set-read-key-sequence-remapped
            --get-internal-last-event-frame
            --get-unread-switch-frame
            --get-ctag
            --set-ctag
            init-cell-accessors-registrations))

;;; M30 imp-2 / imp-3 — plain cell accessors, moved from per-cell DEFUNs
;;; in src/keyboard.c to the table-driven subrs --cell-ref and
;;; --cell-set! (see the `cell_table' in src/keyboard.c).  The old
;;; accessor names are kept, so the mod/ call sites — which resolve the
;;; name in the elisp function slot via %c — do not change.
;;;
;;; The table key is the canonical accessor name: a read uses the same
;;; name as the write.  Each cell reads/writes through one name:
;;;
;;;   --set-echoing!                     -> echoing
;;;   --set-ignore-mouse-drag-p          -> ignore_mouse_drag_p
;;;   --clear-display-working-on-window-p -> display_working_on_window_p
;;;   --set-down-mouse-line-number-width -> down_mouse_line_number_width
;;;   --set-last-mouse-button            -> last_mouse_button
;;;   --set-last-mouse-x                 -> last_mouse_x
;;;   --set-last-mouse-y                 -> last_mouse_y
;;;   --set-double-click-count           -> double_click_count
;;;   --set-menu-bar-items-index         -> menu_bar_items_index
;;;   --set-tab-bar-items-count          -> ntab_bar_items
;;;   --set-tool-bar-items-count         -> ntool_bar_items
;;;   --set-windows-or-buffers-changed   -> windows_or_buffers_changed
;;;   --set-raw-keybuf-count             -> raw_keybuf_count
;;;
;;; A read of a clear-named cell is not needed by any caller, so only
;;; the write name is exported.
;;;
;;; The bare C getters of these cells (--down-mouse-line-number-width,
;;; --last-mouse-x, --double-click-count, --menu-bar-items-index,
;;; --tab-bar-items-count, --tool-bar-items-count, --raw-keybuf-count,
;;; ...) stay C: they are outside the 74-name family list and give an
;;; independent read of the same cell.  See docs/m30-plan.org §imp-3.
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

;; Resolve the two table subrs once.  %c (symbol-function) is not free,
;; and --get-internal-last-event-frame runs on the kbd-buffer-get-event
;; hot path (once per event), so cache the subr instead of re-resolving
;; it on every call.
(defelisp %--cell-ref --cell-ref)
(defelisp %--cell-set! --cell-set!)

(define (%cell-ref name)
  ((force %--cell-ref) name))

(define (%cell-set! name value)
  ((force %--cell-set!) name value))

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

;;;;
;;;; plain fixnum cells (M30 imp-3)
;;;;
;;; Each wrapper writes one `static int' cell through the cell table.
;;; The deleted DEFUN ran CHECK_FIXNUM and stored an int; the table's
;;; CELL_FIXNUM kind does the same.  CHECK_FIXNUM accepts a negative
;;; value, so the table keeps the old setter's range (cr.org F7: no
;;; confirmed writer stores a negative value).  The bare C getter of
;;; each cell stays C and is the independent read.

(define (--set-down-mouse-line-number-width value)
  "Write VALUE to `down_mouse_line_number_width' through the cell table."
  (%cell-set! '--set-down-mouse-line-number-width value))

(define (--set-last-mouse-button value)
  "Write VALUE to `last_mouse_button' through the cell table."
  (%cell-set! '--set-last-mouse-button value))

(define (--set-last-mouse-x value)
  "Write VALUE to `last_mouse_x' through the cell table."
  (%cell-set! '--set-last-mouse-x value))

(define (--set-last-mouse-y value)
  "Write VALUE to `last_mouse_y' through the cell table."
  (%cell-set! '--set-last-mouse-y value))

(define (--set-double-click-count value)
  "Write VALUE to `double_click_count' through the cell table."
  (%cell-set! '--set-double-click-count value))

(define (--set-menu-bar-items-index value)
  "Write VALUE to `menu_bar_items_index' through the cell table."
  (%cell-set! '--set-menu-bar-items-index value))

(define (--set-tab-bar-items-count value)
  "Write VALUE to `ntab_bar_items' through the cell table."
  (%cell-set! '--set-tab-bar-items-count value))

(define (--set-tool-bar-items-count value)
  "Write VALUE to `ntool_bar_items' through the cell table."
  (%cell-set! '--set-tool-bar-items-count value))

(define (--set-windows-or-buffers-changed value)
  "Write VALUE to the C global `windows_or_buffers_changed' through the
cell table."
  (%cell-set! '--set-windows-or-buffers-changed value))

;;;;
;;;; raw_keybuf_count — a fixnum count cell (CELL_FIXNAT)
;;;;
;;; raw_keybuf_count indexes raw_keybuf, so a negative value corrupts
;;; the key buffer.  The deleted DEFUN ran CHECK_FIXNAT; the table's
;;; CELL_FIXNAT kind keeps that duty as the table becomes the only
;;; writer.

(define (--set-raw-keybuf-count n)
  "Write N to `raw_keybuf_count' through the cell table (N >= 0)."
  (%cell-set! '--set-raw-keybuf-count n))

;;;;
;;;; plain Lisp_Object cells (M30 imp-4)
;;;;
;;; Each wrapper writes or reads one `Lisp_Object' cell through the cell
;;; table (kind CELL_LISP_OBJECT).  The deleted DEFUN was a plain
;;; assignment or return of one cell.  The table key is the `--set-'
;;; name; a get/set pair shares one row.  The bare C getters that
;;; lazy-init a vector (--menu-bar-items-vector, --tab-bar-items-vector,
;;; --tool-bar-items-vector, --menu-bar-one-keymap-changed-items,
;;; --menu-bar-touch-id, --frame-relative-event-pos) and the plain C
;;; getter --read-key-sequence-remapped stay C: they are operations or
;;; an independent read, not a plain cell.

(define (--set-frame-relative-event-pos value)
  "Write VALUE to `frame_relative_event_pos' through the cell table."
  (%cell-set! '--set-frame-relative-event-pos value))

(define (--set-menu-bar-items-vector value)
  "Write VALUE to `menu_bar_items_vector' through the cell table."
  (%cell-set! '--set-menu-bar-items-vector value))

(define (--set-tab-bar-items-vector value)
  "Write VALUE to `tab_bar_items_vector' through the cell table."
  (%cell-set! '--set-tab-bar-items-vector value))

(define (--set-tool-bar-items-vector value)
  "Write VALUE to `tool_bar_items_vector' through the cell table."
  (%cell-set! '--set-tool-bar-items-vector value))

(define (--set-menu-bar-one-keymap-changed-items value)
  "Write VALUE to `menu_bar_one_keymap_changed_items' through the cell
table."
  (%cell-set! '--set-menu-bar-one-keymap-changed-items value))

(define (--set-menu-bar-touch-id value)
  "Write VALUE to `menu_bar_touch_id' through the cell table."
  (%cell-set! '--set-menu-bar-touch-id value))

(define (--set-internal-last-event-frame value)
  "Write VALUE to the C global `internal_last_event_frame' through the
cell table."
  (%cell-set! '--set-internal-last-event-frame value))

(define (--set-unread-switch-frame value)
  "Write VALUE to the C global `unread_switch_frame' through the cell
table."
  (%cell-set! '--set-unread-switch-frame value))

(define (--set-read-key-sequence-remapped value)
  "Write VALUE to `read_key_sequence_remapped' through the cell table."
  (%cell-set! '--set-read-key-sequence-remapped value))

(define (--get-internal-last-event-frame)
  "Return the C global `internal_last_event_frame' read through the cell
table."
  (%cell-ref '--set-internal-last-event-frame))

(define (--get-unread-switch-frame)
  "Return the C global `unread_switch_frame' read through the cell table
without clearing it."
  (%cell-ref '--set-unread-switch-frame))

;;;;
;;;; getctag (M30 imp-5)
;;;;
;;; getctag is the prompt tag that quit_throw_to_read_char unwinds to
;;; via abort_to_prompt.  imp-5 roots it in syms_of_keyboard (getctag =
;;; Qnil then staticpro), so it may enter the object-cell table.  The
;;; old --set-ctag returned TAG (it mirrors set-current-kboard returning
;;; its argument); main-queue.scm and test-m12-shims.scm depend on that
;;; contract, so the wrapper returns TAG after the table write.

(define (--set-ctag tag)
  "Set `getctag' to TAG through the cell table and return TAG."
  (%cell-set! '--set-ctag tag)
  tag)

(define (--get-ctag)
  "Return the current `getctag' prompt tag through the cell table."
  (%cell-ref '--set-ctag))

;;; --- registration ---------------------------------------------------

(define (init-cell-accessors-registrations)
  "Register the converted cell accessors against their elisp symbols."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((--set-echoing!                     ,--set-echoing!)
              (--echoing-p                        ,--echoing-p)
              (--set-ignore-mouse-drag-p          ,--set-ignore-mouse-drag-p)
              (--clear-ignore-mouse-drag          ,--clear-ignore-mouse-drag)
              (--clear-display-working-on-window-p
               ,--clear-display-working-on-window-p)
              (--set-down-mouse-line-number-width
               ,--set-down-mouse-line-number-width)
              (--set-last-mouse-button            ,--set-last-mouse-button)
              (--set-last-mouse-x                 ,--set-last-mouse-x)
              (--set-last-mouse-y                 ,--set-last-mouse-y)
              (--set-double-click-count           ,--set-double-click-count)
              (--set-menu-bar-items-index         ,--set-menu-bar-items-index)
              (--set-tab-bar-items-count          ,--set-tab-bar-items-count)
              (--set-tool-bar-items-count         ,--set-tool-bar-items-count)
              (--set-windows-or-buffers-changed
               ,--set-windows-or-buffers-changed)
              (--set-raw-keybuf-count             ,--set-raw-keybuf-count)
              (--set-frame-relative-event-pos
               ,--set-frame-relative-event-pos)
              (--set-menu-bar-items-vector
               ,--set-menu-bar-items-vector)
              (--set-tab-bar-items-vector
               ,--set-tab-bar-items-vector)
              (--set-tool-bar-items-vector
               ,--set-tool-bar-items-vector)
              (--set-menu-bar-one-keymap-changed-items
               ,--set-menu-bar-one-keymap-changed-items)
              (--set-menu-bar-touch-id             ,--set-menu-bar-touch-id)
              (--set-internal-last-event-frame
               ,--set-internal-last-event-frame)
              (--set-unread-switch-frame
               ,--set-unread-switch-frame)
              (--set-read-key-sequence-remapped
               ,--set-read-key-sequence-remapped)
              (--get-internal-last-event-frame
               ,--get-internal-last-event-frame)
              (--get-unread-switch-frame
               ,--get-unread-switch-frame)
              (--get-ctag                         ,--get-ctag)
              (--set-ctag                         ,--set-ctag))))
