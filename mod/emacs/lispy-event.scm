(define-module (emacs lispy-event)
  #:use-module (emacs-elisp runtime)
  #:use-module (emacs event-modifiers)
  #:use-module (emacs lispy-position)
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
;; make-lispy-position imported from (emacs lispy-position) — imp-6.3.
(define %--drag-n-drop-head     (delay (%c '--drag-n-drop-head)))
(define %--time-to-position      (delay (%c '--time-to-position)))
(define %--make-scroll-bar-pos    (delay (%c '--make-scroll-bar-position)))
(define %--scroll-bar-click-head  (delay (%c '--scroll-bar-click-head)))
(define %--ie-kind-from-name    (delay (%c '--ie-kind-from-name)))
(define %--user-signal-name     (delay (%c '--user-signal-name)))

;;; Elisp predicates — not Scheme bindings; go through %c.
(define %frame-live-p           (delay (%c 'frame-live-p)))
(define %windowp                (delay (%c 'windowp)))
(define %upcase                 (delay (%c 'upcase)))
(define %downcase               (delay (%c 'downcase)))

;;; Key-name tables — imp-5.1 (exposed as Scheme vectors).
(define %lispy-accent-codes     (delay (%c '--lispy-accent-codes)))
(define %lispy-accent-keys      (delay (%c '--lispy-accent-keys)))
(define %function-key-offset    (delay (%c '--function-key-offset)))
(define %iso-function-key-offset (delay (%c '--iso-function-key-offset)))
(define %lispy-function-keys    (delay (%c '--lispy-function-keys)))
(define %iso-lispy-function-keys (delay (%c '--iso-lispy-function-keys)))
(define %lispy-multimedia-keys  (delay (%c '--lispy-multimedia-keys)))

;;; Memoized key-table vectors and offsets — imp-5.3 perf.
;;; Each DEFUN reconstructs the vector from the C array on every call.
;;; Wrapping in a second delay calls the DEFUN once and caches the result.
(define +lispy-accent-codes+     (delay ((force %lispy-accent-codes))))
(define +function-key-offset+    (delay ((force %function-key-offset))))
(define +lispy-function-keys+    (delay ((force %lispy-function-keys))))
(define +iso-function-key-offset+ (delay ((force %iso-function-key-offset))))
(define +lispy-multimedia-keys+  (delay ((force %lispy-multimedia-keys))))

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
        (let ((position (make-lispy-position
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

\f
;;; imp-5 — keystroke cases.

;;; 5.2 ASCII_KEYSTROKE_EVENT / MULTIBYTE_CHAR_KEYSTROKE_EVENT.
;;; Caps-lock correction + ctrl-char folding + modifier-OR.
;;;
;;; button_down_time reset is intentionally skipped here — the
;;; double-click file-statics get proper Scheme mirroring under
;;; imp-7.1.  Until then the C fallback path for mouse events
;;; handles the reset.

;;; Character predicates — imp-5.2 cleanup: --uppercasep / --lowercasep
;;; are single-crossing DEFUNs wrapping the C inline functions from
;;; src/buffer.h.  The prior approach chained upcase/downcase DEFUN calls
;;; (up to 3 crossings per keystroke); this cuts it to 1 per predicate.

(define %uppercasep            (delay (%c '--uppercasep)))
(define %lowercasep            (delay (%c '--lowercasep)))

(define (keystroke-impl ie is-ascii)
  ;; Shared ASCII / MULTIBYTE_CHAR body.  is-ascii is #t for
  ;; ASCII_KEYSTROKE_EVENT, #f for MULTIBYTE_CHAR_KEYSTROKE_EVENT.
  (let* ((raw-code ((force %--ie-code) ie))
         (mods ((force %--ie-modifiers) ie))
         ;; ASCII: mask to 7 bits (C: c &= 0377).
         (c (if is-ascii
                (let ((masked (logand raw-code #o377)))
                  ;; eassert (c == event->code) — the original C
                  ;; assertion that the 7-bit mask is a no-op for
                  ;; valid ASCII input.  Violation means a non-ASCII
                  ;; code landed in ASCII_KEYSTROKE_EVENT.
                  (unless (= masked raw-code)
                    (error "ASCII keystroke code overflows 7 bits:" raw-code))
                  masked)
                raw-code)))
    ;; Caps-lock correction: if a non-shift modifier is pressed,
    ;; fix case mismatch (caps-lock inverted the letter).
    (when (not (zero? (logand mods (lognot shift-modifier))))
      (cond
       ((and ((force %uppercasep) c) (zero? (logand mods shift-modifier)))
        (set! c ((force %downcase) c)))
       ((and ((force %lowercasep) c) (not (zero? (logand mods shift-modifier))))
        (set! c ((force %upcase) c)))))
    ;; Ctrl-char folding (ASCII only): turn ctrl-letter into control char.
    (when (and is-ascii (not (zero? (logand mods ctrl-modifier))))
      (set! c (make-ctrl-char c))
      (set! mods (logand mods (lognot ctrl-modifier))))
    ;; OR in the remaining modifier bits (meta, alt, hyper, super, ctrl).
    (set! c (logior c (logand mods (logior meta-modifier alt-modifier
                                            hyper-modifier super-modifier
                                            ctrl-modifier))))
    ;; Distinguish Shift-SPC from SPC.
    (when (and (= raw-code #o40) (not (zero? (logand mods shift-modifier))))
      (set! c (logior c shift-modifier)))
    c))

(define (mle-ascii-keystroke ie)
  (keystroke-impl ie #t))

(define (mle-multibyte-char-keystroke ie)
  (keystroke-impl ie #f))

(register-kind! 'ascii-keystroke mle-ascii-keystroke)
(register-kind! 'multibyte-char-keystroke mle-multibyte-char-keystroke)

;;; 5.3 NON_ASCII_KEYSTROKE_EVENT / NS_NONKEY_EVENT / MULTIMEDIA_KEY_EVENT.
;;;
;;; Same sequence as the C switch body in make_lispy_event:
;;;   1. Search lispy_accent_codes for a match → modify_event_symbol with
;;;      accent_key_syms cache.
;;;   2. ISO function key range check → modify_event_symbol with
;;;      func_key_syms cache.
;;;   3. Function key range check (FUNCTION_KEY_OFFSET) → ditto.
;;;   4. Fall through to system-key lookup.
;;;
;;; MULTIMEDIA_KEY_EVENT is a separate handler (HAVE_NTGUI only); its
;;; registration silently skips on non-NTGUI builds.
;;;
;;; button_down_time = 0 is intentionally skipped — the double-click
;;; file-statics get proper Scheme mirroring under imp-7.1.

;;; C-side modify_event_symbol wrappers (imp-5.3).
(define %modify-event-symbol-accent
  (delay (%c '--modify-event-symbol-accent)))
(define %modify-event-symbol-func
  (delay (%c '--modify-event-symbol-func)))
(define %modify-event-symbol-system
  (delay (%c '--modify-event-symbol-system)))

;;; Accent-key linear scan.  Returns the result of modify_event_symbol
;;; on first match, or #f if no accent code matched.

(define (accent-lookup code mods)
  (let ((codes (force +lispy-accent-codes+)))
    (let loop ((i 0))
      (and (< i (vector-length codes))
           (if (= code (vector-ref codes i))
               ((force %modify-event-symbol-accent) i mods)
               (loop (+ i 1)))))))

;;; ISO function key lookup.  ISO_FUNCTION_KEY_OFFSET ≤ code < FUNCTION_KEY_OFFSET.

(define (iso-function-lookup code mods)
  (let ((iso-offset (force +iso-function-key-offset+)))
    (and (>= code iso-offset)
         (< code (force +function-key-offset+))
         ((force %modify-event-symbol-func)
          (- code iso-offset) mods 1))))  ; tag 1 = iso-function

;;; Function key lookup.  code − FUNCTION_KEY_OFFSET must be a valid
;;; index with a non-#f entry.

(define (function-key-lookup code mods)
  (let* ((fk-offset (force +function-key-offset+))
         (fk-keys (force +lispy-function-keys+))
         (idx (- code fk-offset)))
    (and (>= idx 0)
         (< idx (vector-length fk-keys))
         (vector-ref fk-keys idx)         ; non-#f slot?
         ((force %modify-event-symbol-func) idx mods 0))))  ; tag 0 = function

;;; System-key fallthrough.  Passes code directly; modify_event_symbol
;;; handles the system_key_syms cache and Vsystem_key_alist lookup.

(define (system-key-lookup code mods)
  ((force %modify-event-symbol-system) code mods))

;;; Main NON_ASCII_KEYSTROKE_EVENT handler.  Chains the four lookups;
;;; the first non-#f result wins (matching the C return-early pattern).

(define (mle-non-ascii-keystroke ie)
  (let ((code ((force %--ie-code) ie))
        (mods ((force %--ie-modifiers) ie)))
    (or (accent-lookup code mods)
        (iso-function-lookup code mods)
        (function-key-lookup code mods)
        (system-key-lookup code mods))))

;;; NS_NONKEY_EVENT shares the same body (C: fallthrough from NS_NONKEY
;;; to NON_ASCII_KEYSTROKE_EVENT).  Registration silently skipped on
;;; non-NS builds (--ie-kind-from-name returns -1).

(define mle-ns-nonkey mle-non-ascii-keystroke)

;;; MULTIMEDIA_KEY_EVENT.  Single-table lookup via lispy_multimedia_keys
;;; and the func_key_syms cache (tag 2).  Returns nil on unrecognized code
;;; or empty mm-keys vector (matching the C).  Registration silently
;;; skipped on non-NTGUI builds.

(define (mle-multimedia-key ie)
  (let ((code ((force %--ie-code) ie))
        (mods ((force %--ie-modifiers) ie))
        (mm-keys (force +lispy-multimedia-keys+)))
    (if (and (> code 0)
             (< code (vector-length mm-keys))
             (vector-ref mm-keys code))
        ((force %modify-event-symbol-func) code mods 2)  ; tag 2 = multimedia
        #nil)))

(register-kind! 'non-ascii-keystroke mle-non-ascii-keystroke)
(register-kind! 'ns-nonkey mle-ns-nonkey)
(register-kind! 'multimedia-key mle-multimedia-key)

;;; 5.4 NS_TEXT_EVENT.
;;;
;;; Single DEFUN wrapper avoids the magic-number trap (KEY_NS_PUT_WORKING_TEXT
;;; = 12345).  C side does the intern; Scheme just wraps in list1.

(define %--ns-text-event-symbol
  (delay (%c '--ns-text-event-symbol)))

(define (mle-ns-text-event ie)
  (list ((force %--ns-text-event-symbol) ((force %--ie-code) ie))))

(register-kind! 'ns-text-event mle-ns-text-event)
