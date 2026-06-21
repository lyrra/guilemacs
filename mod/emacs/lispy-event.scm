(define-module (emacs lispy-event)
  #:use-module (emacs-elisp runtime)
  #:use-module (emacs event-modifiers)
  #:declarative? #t
  #:export (make-lispy-event-dispatch
            make-lispy-event))

;;; M9 — make_lispy_event port to Scheme.
;;;
;;; make_lispy_event (src/keyboard.c:6450–7532) is a 1083-line
;;; switch(event->kind) that transforms a struct input_event into
;;; a Lisp event form.  It has no I/O, no syscalls, no signal
;;; handlers — pure transformation — making it the cleanest
;;; candidate for Scheme migration in keyboard.c.
;;;
;;; C-side infrastructure:
;;;   ie-smob   — foreign-pointer SMOB wrapping struct input_event *
;;;               (src/keyboard.c:874–943, tag in src/guile.c).
;;;   --ie-*    — field-accessor DEFUNs (imp-1.2).
;;;   --set-ie-* — field mutators (imp-1.3).
;;;
;;; The module's dispatch table is keyed by event_kind int; each
;;; entry is a Scheme procedure that takes an ie-smob and returns
;;; a Lisp event form.  The orchestrator looks up the kind and
;;; calls the registered procedure, falling through to C's
;;; --make-lispy-event-c for kinds not yet ported.
;;;
;;; See docs/m9-plan.org for the full implementation DAG.

(define make-lispy-event-dispatch
  ;; Hash table keyed by event_kind integers; populate with hashv-set!
  ;; and look up with hashv-ref.  Entries are added incrementally as
  ;; cases are ported (imp-3 → imp-7).
  (make-hash-table))

\f
;;; Lazy C-primitive references.  Resolved at first call so module
;;; load order is not sensitive to DEFUN registration order.

(define (%c name) (symbol-function name))

(define %--ie-kind              (delay (%c '--ie-kind)))
(define %--ie-code              (delay (%c '--ie-code)))
(define %--ie-modifiers         (delay (%c '--ie-modifiers)))
(define %--ie-arg               (delay (%c '--ie-arg)))
(define %--ie-frame-or-window   (delay (%c '--ie-frame-or-window)))
(define %--ie-x                 (delay (%c '--ie-x)))
(define %--ie-y                 (delay (%c '--ie-y)))
(define %--ie-timestamp         (delay (%c '--ie-timestamp)))
(define %--ie-part              (delay (%c '--ie-part)))
(define %--ie-clear             (delay (%c '--ie-clear)))
(define %--make-lispy-event-c   (delay (%c '--make-lispy-event-c)))
(define %--make-lispy-focus-in  (delay (%c '--make-lispy-focus-in)))
(define %--make-lispy-focus-out (delay (%c '--make-lispy-focus-out)))
(define %--make-lispy-position  (delay (%c '--make-lispy-position)))
(define %--drag-n-drop-head     (delay (%c '--drag-n-drop-head)))
(define %--time-to-position      (delay (%c '--time-to-position)))
(define %--make-scroll-bar-pos    (delay (%c '--make-scroll-bar-position)))
(define %--scroll-bar-click-head  (delay (%c '--scroll-bar-click-head)))
(define %--ie-kind-from-name    (delay (%c '--ie-kind-from-name)))
(define %--user-signal-name     (delay (%c '--user-signal-name)))

;;; Elisp predicates — not Scheme bindings; go through %c.
(define %frame-live-p           (delay (%c 'frame-live-p)))
(define %windowp                (delay (%c 'windowp)))

;;; Helper: register a per-kind handler in the dispatch table.
;;; Uses --ie-kind-from-name to convert a symbol (e.g. 'dbus-event)
;;; into its event_kind integer, then stores PROC under that key.

(define (register-kind! name-symbol proc)
  (let ((k ((force %--ie-kind-from-name) name-symbol)))
    (when (>= k 0)
      (hashv-set! make-lispy-event-dispatch k proc))))

;;; Orchestrator.

(define (make-lispy-event ie)
  "Transform an input-event SMOB into a Lisp event form.

Looks up (--ie-kind IE) in the dispatch table.  When a Scheme
procedure is registered for that kind, calls it with IE; otherwise
falls through to C's --make-lispy-event-c, which runs the original
make_lispy_event body."
  (let* ((kind ((force %--ie-kind) ie))
         (proc (hashv-ref make-lispy-event-dispatch kind)))
    (if proc
        (proc ie)
        ((force %--make-lispy-event-c) ie))))

;;; Per-kind handlers — imp-3 (trivial cases).

;;; Each handler: (cons <event-symbol> (--ie-arg ie))

(define (mle-dbus-event ie)
  (cons 'dbus-event ((force %--ie-arg) ie)))

(define (mle-thread-event ie)
  (cons 'thread-event ((force %--ie-arg) ie)))

(define (mle-xwidget-event ie)
  (cons 'xwidget-event ((force %--ie-arg) ie)))

(define (mle-xwidget-display-event ie)
  (cons 'xwidget-display-event ((force %--ie-arg) ie)))

(define (mle-file-notify-event ie)
  ;; FIX-WIN32: On W32 this would be
  ;; (file-notify DESCRIPTOR-ACTION-FILE CALLBACK)
  (cons 'file-notify ((force %--ie-arg) ie)))

;;; trivial-frame group

(define (mle-delete-window-event ie)
  (list 'delete-frame (list ((force %--ie-frame-or-window) ie))))

(define (mle-iconify-event ie)
  (list 'iconify-frame (list ((force %--ie-frame-or-window) ie))))

(define (mle-deiconify-event ie)
  (list 'make-frame-visible (list ((force %--ie-frame-or-window) ie))))

(define (mle-move-frame-event ie)
  (list 'move-frame (list ((force %--ie-frame-or-window) ie))))

(define (mle-no-event ie)
  ;; With MULTI_KBOARD, NO_EVENT acts as a placeholder used when
  ;; randomly deleting events from the queue.  (They shouldn't
  ;; otherwise be found in the buffer, but on some machines they
  ;; do show up even without MULTI_KBOARD.)  On Windows NT/9X,
  ;; NO_EVENT is also used to delete extraneous mouse events
  ;; during a popup-menu call.  Discard by returning nil.
  #nil)

;;; Dispatch table registration.
;;; Each register-kind! call maps a Lisp event symbol to its handler.
;;; When --ie-kind-from-name returns -1 the feature isn't compiled in
;;; and registration is silently skipped.

(register-kind! 'dbus-event mle-dbus-event)
(register-kind! 'thread-event mle-thread-event)
(register-kind! 'xwidget-event mle-xwidget-event)
(register-kind! 'xwidget-display-event mle-xwidget-display-event)
(register-kind! 'file-notify mle-file-notify-event)

(register-kind! 'delete-frame mle-delete-window-event)
(register-kind! 'iconify-frame mle-iconify-event)
(register-kind! 'make-frame-visible mle-deiconify-event)
(register-kind! 'move-frame mle-move-frame-event)
(register-kind! 'no-event mle-no-event)

\f
;;; imp-3.3 — simple-list group.

(define (mle-select-window-event ie)
  (list 'select-window (list ((force %--ie-frame-or-window) ie))))

(define (mle-save-session-event ie)
  (list 'save-session ((force %--ie-arg) ie)))

(define (mle-config-changed-event ie)
  (list 'config-changed-event
        ((force %--ie-arg) ie)
        ((force %--ie-frame-or-window) ie)))

(define (mle-preedit-text-event ie)
  (list 'preedit-text ((force %--ie-arg) ie)))

(define (mle-end-session-event ie)
  (list 'end-session))

(define (mle-language-change-event ie)
  (list 'language-change
        ((force %--ie-frame-or-window) ie)
        ((force %--ie-code) ie)
        ((force %--ie-modifiers) ie)))

(define (mle-user-signal-event ie)
  ;; find_user_signal_name(code) → intern → bare symbol.
  ((force %--user-signal-name) ((force %--ie-code) ie)))

(register-kind! 'select-window mle-select-window-event)
(register-kind! 'save-session mle-save-session-event)
(register-kind! 'config-changed-event mle-config-changed-event)
(register-kind! 'preedit-text mle-preedit-text-event)
(register-kind! 'end-session mle-end-session-event)
(register-kind! 'language-change mle-language-change-event)
(register-kind! 'user-signal-event mle-user-signal-event)

\f
;;; imp-4 — simple-helper cases.
;;; Each handler calls one helper C primitive or mutator.

;;; 4.3 MENU_BAR_EVENT — #ifdef HAVE_EXT_MENU_BAR.
;;; On toolkit builds, MENU_BAR_EVENT passes through event->arg.
;;; When arg == frame_or_window, it's a prefix key → (menu-bar).

(define (mle-menu-bar-event ie)
  (let ((arg ((force %--ie-arg) ie))
        (frame ((force %--ie-frame-or-window) ie)))
    (if (eq? arg frame)
        (list 'menu-bar)
        arg)))

(register-kind! 'menu-bar mle-menu-bar-event)

;;; 4.1 FOCUS_IN / FOCUS_OUT.
;;; Each calls a trivial DEFUN that wraps the original C helper.

(define (mle-focus-in-event ie)
  ((force %--make-lispy-focus-in)
   ((force %--ie-frame-or-window) ie)))

(define (mle-focus-out-event ie)
  ((force %--make-lispy-focus-out)
   ((force %--ie-frame-or-window) ie)))

(register-kind! 'focus-in mle-focus-in-event)
(register-kind! 'focus-out mle-focus-out-event)

;;; 4.5 DRAG_N_DROP_EVENT.
;;; Builds position (via --make-lispy-position) and head symbol
;;; (via --drag-n-drop-head), returns (head position files).

(define (mle-drag-n-drop-event ie)
  (let* ((fow ((force %--ie-frame-or-window) ie))
         (files ((force %--ie-arg) ie)))
    (if (not ((force %frame-live-p) fow))
        #nil
        (let ((position ((force %--make-lispy-position)
                         fow
                         ((force %--ie-x) ie)
                         ((force %--ie-y) ie)
                         ((force %--ie-timestamp) ie)))
              (head ((force %--drag-n-drop-head)
                     ((force %--ie-modifiers) ie))))
          (list head position files)))))

(register-kind! 'drag-n-drop mle-drag-n-drop-event)

;;; 4.2 HELP_EVENT.
;;; First mutation through the Scheme path.  Read ALL 5 fields
;;; before calling --ie-clear, matching the C ordering:
;;;   frame_or_window, arg, timestamp, x, y  →  clear  →  build.
;;; After clear the smob kind is NO_EVENT; if clear_event ever
;;; gets stricter and nils the Lisp_Object fields we're still safe.

(define (mle-help-event ie)
  ;; Read all fields BEFORE mutation (per user instruction #2).
  (let ((frame ((force %--ie-frame-or-window) ie))
        (object ((force %--ie-arg) ie))
        (position ((force %--time-to-position)
                   ((force %--ie-timestamp) ie)))
        (window ((force %--ie-x) ie))
        (help ((force %--ie-y) ie)))
    ;; Clear the event — sets kind = NO_EVENT.
    ((force %--ie-clear) ie)
    ;; Build and return.
    (cons 'help-echo
          (list frame help
                (if ((force %windowp) window) window #nil)
                object position))))

(register-kind! 'help-echo mle-help-event)

;;; 4.4 TAB_BAR_EVENT / TOOL_BAR_EVENT.
;;; apply-modifiers is imported from (emacs event-modifiers) —
;;; its C shim in keyboard.c dispatches to the same Scheme function.
;;; apply-modifiers returns non-symbol input unchanged, so we don't
;;; need an explicit SYMBOLP gate here.

(define (mle-tab-bar-event ie)
  (let ((res (apply-modifiers ((force %--ie-modifiers) ie)
                              ((force %--ie-arg) ie)))
        (fow ((force %--ie-frame-or-window) ie)))
    (list res (list fow 'tab-bar))))

(define (mle-tool-bar-event ie)
  (let ((res (apply-modifiers ((force %--ie-modifiers) ie)
                              ((force %--ie-arg) ie)))
        (fow ((force %--ie-frame-or-window) ie)))
    (list res (list fow 'tool-bar))))

(register-kind! 'tab-bar mle-tab-bar-event)
(register-kind! 'tool-bar mle-tool-bar-event)

;;; 4.6 SCROLL_BAR_CLICK / HORIZONTAL_SCROLL_BAR_CLICK (toolkit).
;;; #ifdef USE_TOOLKIT_SCROLL_BARS — registration silently skips on
;;; non-toolkit builds.  Modifier constants computed locally rather
;;; than crossing into (emacs event-modifiers) for two unexported
;;; values; see src/termhooks.h:428 (up_modifier=1), :435
;;; (click_modifier=8).

;; We deliberately skip --set-ie-modifiers here — the smob is
;; invalidated (data → NULL) by make_lispy_event right after
;; SCM_CALL_1 returns, so writing back would be a no-op.  The
;; computed new-mods is passed to --scroll-bar-click-head directly,
;; which is functionally equivalent to the C pattern of mutating
;; event->modifiers before calling modify_event_symbol.

(define (mle-scroll-bar-click-toolkit ie)
  (let* ((mods ((force %--ie-modifiers) ie))
         ;; Strip up_modifier (=1), add click_modifier (=8).
         (new-mods (logior (logand mods (lognot 1)) 8))
         (position ((force %--make-scroll-bar-pos)
                    ((force %--ie-frame-or-window) ie)
                    ((force %--ie-x) ie)
                    ((force %--ie-y) ie)
                    ((force %--ie-timestamp) ie)
                    ((force %--ie-part) ie)
                    'vertical-scroll-bar))
         (head ((force %--scroll-bar-click-head)
                ((force %--ie-code) ie)
                new-mods)))
    (list head position)))

(define (mle-horizontal-scroll-bar-click-toolkit ie)
  (let* ((mods ((force %--ie-modifiers) ie))
         (new-mods (logior (logand mods (lognot 1)) 8))
         (position ((force %--make-scroll-bar-pos)
                    ((force %--ie-frame-or-window) ie)
                    ((force %--ie-x) ie)
                    ((force %--ie-y) ie)
                    ((force %--ie-timestamp) ie)
                    ((force %--ie-part) ie)
                    'horizontal-scroll-bar))
         (head ((force %--scroll-bar-click-head)
                ((force %--ie-code) ie)
                new-mods)))
    (list head position)))

(register-kind! 'scroll-bar-click-toolkit mle-scroll-bar-click-toolkit)
(register-kind! 'horizontal-scroll-bar-click-toolkit
                mle-horizontal-scroll-bar-click-toolkit)
