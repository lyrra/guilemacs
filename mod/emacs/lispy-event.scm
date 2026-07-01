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

\f
;;; imp-7.2 — WHEEL_EVENT / HORIZ_WHEEL_EVENT.
;;;
;;; C body (keyboard.c:7115–7225): frame-live check,
;;; make_lispy_position, wheel-direction → symbol_num, fuzz
;;; computation, double-click detection (reads/mutates 5
;;; file-statics), head-symbol via modify_event_symbol with
;;; lispy_wheel_names / wheel_syms, list-shape dispatch on
;;; event->arg + modifiers.
;;;
;;; Double-click detection intentionally skipped — needs
;;; imp-7.1 file-static mirror.  Every wheel event gets
;;; click_modifier only.  The C fallback (--make-lispy-event-c)
;;; retains full double-click behavior for unported kinds.

(define %--modify-event-symbol-mouse-click
  (delay (%c '--modify-event-symbol-mouse-click)))

(define (mle-wheel-event ie horiz?)
  ;; Shared body for WHEEL_EVENT and HORIZ_WHEEL_EVENT.
  ;; horiz? is #t for HORIZ_WHEEL_EVENT, #f for WHEEL_EVENT.
  (let* ((fow ((force %--ie-frame-or-window) ie)))

    ;; Frame live check — return nil for deleted frames.
    (if (not ((force %frame-live-p) fow))
        #nil

        ;; Build position via Scheme make-lispy-position (imp-6.4).
        (let* ((position (make-lispy-position
                          fow
                          ((force %--ie-x) ie)
                          ((force %--ie-y) ie)
                          ((force %--ie-timestamp) ie)))

               ;; Wheel direction — symbol_num 0=up, 1=down,
               ;; +2 for horizontal (2=left, 3=right).
               (mods ((force %--ie-modifiers) ie))
               (symbol-num
                (cond
                 ((not (zero? (logand mods up-modifier)))
                  (set! mods (logand mods (lognot up-modifier)))
                  0)
                 ((not (zero? (logand mods down-modifier)))
                  (set! mods (logand mods (lognot down-modifier)))
                  1)
                 (else
                  (error "wheel event without up/down modifier")))))

          (when horiz?
            (set! symbol-num (+ symbol-num 2)))

          ;; Double-click detection + fuzz skipped — needs
          ;; imp-7.1 mirror.  Always emit click_modifier.
          (set! mods (logior mods click-modifier))

          ;; Head symbol via modify_event_symbol with wheel tables.
          (let* ((head ((force %--modify-event-symbol-mouse-click)
                        symbol-num mods))
                 (arg ((force %--ie-arg) ie)))

            ;; Return shape dispatch — matches C list2/list4/list5.
            ;; list3 branch (double/triple modifier) unreachable
            ;; until imp-7.1 enables double-click promotion.
            (cond
             ((pair? arg)
              (list head position 1 (car arg)
                    (if (and (pair? (cdr arg)) (pair? (cddr arg)))
                        (cons (cadr arg) (caddr arg))
                        #nil)))
             ((number? arg)
              (list head position 1 arg))
             (else
              (list head position))))))))

(define (mle-vert-wheel-event ie)
  (mle-wheel-event ie #f))

(define (mle-horiz-wheel-event ie)
  (mle-wheel-event ie #t))

(register-kind! 'wheel-event mle-vert-wheel-event)
(register-kind! 'horizontal-wheel-event mle-horiz-wheel-event)

;;; imp-7.3 — TOUCH_END_EVENT / PINCH_EVENT.
;;;
;;; Structurally different events that share no body.
;;; Both use make-lispy-position for the position list.
;;; No file-static mutations — clean single-event handlers
;;; that don't need imp-7.1's mirror.

(define %--modify-event-symbol-pinch
  (delay (%c '--modify-event-symbol-pinch)))

(define (mle-touch-end-event ie)
  ;; C body (keyboard.c:7238–7252): frame-live check,
  ;; make_lispy_position, list2(Qtouch_end, position).
  (let* ((fow ((force %--ie-frame-or-window) ie)))
    (if (not ((force %frame-live-p) fow))
        #nil
        (let ((position (make-lispy-position
                         fow
                         ((force %--ie-x) ie)
                         ((force %--ie-y) ie)
                         ((force %--ie-timestamp) ie))))
          (list 'touch-end position)))))

(define (mle-pinch-event ie)
  ;; C body (keyboard.c:7457–7471): no explicit FRAME_LIVE_P
  ;; guard in the original, but added here for consistency.
  ;; make_lispy_position + modify_event_symbol(pinch) +
  ;; cons-chain returning (head position . arg-elements).
  (let* ((fow ((force %--ie-frame-or-window) ie)))
    (if (not ((force %frame-live-p) fow))
        #nil
        (let* ((x ((force %--ie-x) ie))
               (y ((force %--ie-y) ie))
               (position (make-lispy-position
                          fow x y
                          ((force %--ie-timestamp) ie)))
               (head ((force %--modify-event-symbol-pinch)
                      ((force %--ie-modifiers) ie)))
               (arg ((force %--ie-arg) ie)))
          (cons head (cons position arg))))))

(register-kind! 'touch-end mle-touch-end-event)
(register-kind! 'pinch mle-pinch-event)

\f
;;; imp-7.4 — touchscreen group.
;;;
;;; Three structurally different events using imp-7.4.1 DEFUNs
;;; for menu-bar / tab-bar integration.

(define %--menu-bar-touch-id          (delay (%c '--menu-bar-touch-id)))
(define %--set-menu-bar-touch-id      (delay (%c '--set-menu-bar-touch-id)))
(define %--coords-in-menu-bar-window  (delay (%c '--coords-in-menu-bar-window)))
(define %--tab-bar-enrich-position    (delay (%c '--tab-bar-enrich-position)))
(define %--menu-bar-touch-consume-p   (delay (%c '--menu-bar-touch-consume-p)))
(define %--menu-bar-touch-activate    (delay (%c '--menu-bar-touch-activate)))

(define (mle-touchscreen-begin-event ie)
  ;; C body (keyboard.c:7260–7335): frame-live → menu-bar
  ;; early-return (store touch ID, return nil) → make_lispy_position
  ;; → tab-bar enrichment → (touchscreen-begin (id . position)).
  (let* ((fow ((force %--ie-frame-or-window) ie)))
    (if (not ((force %frame-live-p) fow))
        #nil
        (let* ((id ((force %--ie-arg) ie))
               (x ((force %--ie-x) ie))
               (y ((force %--ie-y) ie)))
          ;; Menu-bar early-return: if tap on menu bar,
          ;; store touch ID and return nil.
          (if ((force %--coords-in-menu-bar-window) fow x y)
              (begin
                ((force %--set-menu-bar-touch-id) id)
                #nil)
              (let* ((pos (make-lispy-position
                           fow x y
                           ((force %--ie-timestamp) ie)))
                     (pos ((force %--tab-bar-enrich-position)
                           fow x y pos)))
                (list 'touchscreen-begin (cons id pos)))))))))

(define (mle-touchscreen-end-event ie)
  ;; C body (keyboard.c:7337–7458): frame-live → menu-bar
  ;; activation (if id matches menu_bar_touch_id, return
  ;; menu-bar item event) → make_lispy_position → tab-bar
  ;; enrichment → (touchscreen-end (id . position) CANCELED).
  (let* ((fow ((force %--ie-frame-or-window) ie)))
    (if (not ((force %frame-live-p) fow))
        #nil
        (let* ((id ((force %--ie-arg) ie))
               (x ((force %--ie-x) ie))
               (y ((force %--ie-y) ie)))
          ;; Menu-bar activation: if this touch ID matches the
          ;; stored menu_bar_touch_id, consume it and try to
          ;; activate.  Short-circuit regardless of success —
          ;; matched-but-failed means menu bar disappeared
          ;; or finger slid off, return nil (C behavior).
          (if ((force %--menu-bar-touch-consume-p) id)
              ;; Consumed — activate or return nil.
              ((force %--menu-bar-touch-activate)
               fow x y fow ((force %--ie-timestamp) ie))
              ;; Not consumed — normal touch-end path.
              (let* ((pos (make-lispy-position
                           fow x y
                           ((force %--ie-timestamp) ie)))
                     (pos ((force %--tab-bar-enrich-position)
                           fow x y pos)))
                (list 'touchscreen-end (cons id pos)
                      (if (not (zero? ((force %--ie-modifiers) ie)))
                          #t
                          #nil))))))))))

(define (mle-touchscreen-update-event ie)
  ;; C body (keyboard.c:7480–7500): frame-live → loop over
  ;; event->arg triples (x y id), skip touches whose id
  ;; matches menu_bar_touch_id → make_lispy_position for each
  ;; → accumulate (id . position) → (touchscreen-update evt).
  (let* ((fow ((force %--ie-frame-or-window) ie)))
    (if (not ((force %frame-live-p) fow))
        #nil
        (let ((mb-id ((force %--menu-bar-touch-id))))
          (let loop ((tem ((force %--ie-arg) ie))
                     (evt '()))
            (if (not (pair? tem))
                (if (null? evt) #nil (list 'touchscreen-update evt))
                (let* ((it (car tem))
                       (x (car it))
                       (y (cadr it))
                       (id (caddr it)))
                  (if (eq? id mb-id)
                      (loop (cdr tem) evt)
                      (let ((position (make-lispy-position
                                       fow x y
                                       ((force %--ie-timestamp) ie))))
                        (loop (cdr tem)
                              (cons (cons id position) evt))))))))))))

(register-kind! 'touchscreen-begin mle-touchscreen-begin-event)
(register-kind! 'touchscreen-end mle-touchscreen-end-event)
(register-kind! 'touchscreen-update mle-touchscreen-update-event)

\f
;;; imp-7.5 — MOUSE_CLICK + non-toolkit SCROLL_BAR_CLICK.
;;;
;;; ~300-line C body → decomposed into sub-helpers.
;;; imp-7.5.1: menu-bar intercept (this leaf) — stub that
;;; tries menu-bar first, then falls through to C fallback
;;; until the full handler is built out in 7.5.2+.

(define %--ensure-button-down-location-size
  (delay (%c '--ensure-button-down-location-size)))
(define %--mouse-click-menu-bar-intercept
  (delay (%c '--mouse-click-menu-bar-intercept)))

;;; imp-7.5.2 — double-click detection (pure read, no mutations).
;;;
;;; Reads imp-7.1 file-statics (last_mouse_button, last_mouse_x,
;;; last_mouse_y, button_down_time) via getter DEFUNs, plus
;;; double-click-fuzz and double-click-time via %symbol-value.
;;; Returns #t if this event is a double-click, #f otherwise.
;;; No writes to file-statics — that's imp-7.5.3.

(define %symbol-value             (delay (%c 'symbol-value)))
(define %double-click-fuzz        (delay ((force %symbol-value)
                                         'double-click-fuzz)))
(define %double-click-time        (delay ((force %symbol-value)
                                         'double-click-time)))
(define %--last-mouse-button    (delay (%c '--last-mouse-button)))
(define %--last-mouse-x         (delay (%c '--last-mouse-x)))
(define %--last-mouse-y         (delay (%c '--last-mouse-y)))
(define %--button-down-time     (delay (%c '--button-down-time)))
(define %window-system          (delay (%c 'window-system)))
(define %window-frame           (delay (%c 'window-frame)))

(define (mouse-double-click-p fow code x y timestamp)
  ;; Compute is_double for mouse events.
  ;; Matches keyboard.c:6953-6971.  Also usable by wheel
  ;; handler (keyboard.c:7135-7160) — same shape.
  (let* ((frame (if ((force %windowp) fow)
                   ((force %window-frame) fow)
                   fow))
         (fuzz-raw ((force %double-click-fuzz)))
         (fuzz (if ((force %window-system) frame)
                   fuzz-raw
                   (/ fuzz-raw 8)))
         (last-btn ((force %--last-mouse-button)))
         (last-x   ((force %--last-mouse-x)))
         (last-y   ((force %--last-mouse-y)))
         (down-time ((force %--button-down-time)))
         (dbl-time ((force %double-click-time))))
    (and (= code last-btn)
         (<= (abs (- x last-x)) fuzz)
         (<= (abs (- y last-y)) fuzz)
         (not (zero? down-time))
         (or (eq? dbl-time #t)  ; Qt = always double-click
             (and (integer? dbl-time)
                  (> dbl-time 0)
                  (< (- timestamp down-time) dbl-time))))))

\f
;;; imp-7.5.3 — button-down bookkeeping (first writes to imp-7.1
;;; setters).  Reads button_down_location slot (saving old value),
;;; writes all 5 file-statics + ignore_mouse_drag_p.

(define %--set-last-mouse-button
  (delay (%c '--set-last-mouse-button)))
(define %--set-last-mouse-x
  (delay (%c '--set-last-mouse-x)))
(define %--set-last-mouse-y
  (delay (%c '--set-last-mouse-y)))
(define %--double-click-count
  (delay (%c '--double-click-count)))
(define %--set-double-click-count
  (delay (%c '--set-double-click-count)))
(define %--set-button-down-time
  (delay (%c '--set-button-down-time)))
(define %--set-frame-relative-event-pos
  (delay (%c '--set-frame-relative-event-pos)))
(define %--ignore-mouse-drag-p
  (delay (%c '--ignore-mouse-drag-p)))
(define %--set-ignore-mouse-drag-p
  (delay (%c '--set-ignore-mouse-drag-p)))
(define %--button-down-location-aref
  (delay (%c '--button-down-location-aref)))
(define %--button-down-location-aset
  (delay (%c '--button-down-location-aset)))
(define %--save-line-number-display-width
  (delay (%c '--save-line-number-display-width)))
(define %copy-alist               (delay (%c 'copy-alist)))

(define (mouse-button-down-bookkeep! fow code x y timestamp mods position)
  ;; Button-press bookkeeping (keyboard.c:6963-7006).
  ;; Reads old start_pos from button_down_location[code],
  ;; computes is_dbl using OLD last_mouse_* values, THEN
  ;; updates last_mouse_*, double_click_count, button_down_time,
  ;; button_down_location, frame_relative_event_pos,
  ;; ignore_mouse_drag_p.  Returns (values mods start-pos)
  ;; where mods may be mutated (double/triple promotion) and
  ;; start-pos is the old slot value for drag detection.

  ((force %--ensure-button-down-location-size) code)
  (let ((start-pos ((force %--button-down-location-aref) code)))
    ((force %--button-down-location-aset) code #nil)

    ;; is-dbl uses OLD last_mouse_* values (C:6984).
    ;; Must compute BEFORE updating last_mouse_* below.
    (let ((is-dbl (and (not (zero? (logand mods down-modifier)))
                       (mouse-double-click-p fow code x y timestamp))))

      ;; Now safe to update last_mouse_* (C:6987-6989).
      ((force %--set-last-mouse-button) code)
      ((force %--set-last-mouse-x) x)
      ((force %--set-last-mouse-y) y)

      (when (not (zero? (logand mods down-modifier)))
        (let ((dbl-count ((force %--double-click-count))))
          (if is-dbl
              (begin
                (set! dbl-count (+ dbl-count 1))
                (set! mods (logior mods
                                   (if (> dbl-count 2)
                                       triple-modifier
                                       double-modifier))))
              (set! dbl-count 1))
          ((force %--set-double-click-count) dbl-count)
          ((force %--set-button-down-time) timestamp)
          ((force %--button-down-location-aset) code
           ((force %copy-alist) position))
          ((force %--set-frame-relative-event-pos)
           (cons x y))
          ((force %--set-ignore-mouse-drag-p) #nil)
          ((force %--save-line-number-display-width) fow)))

      (values mods start-pos))))

(define (mle-mouse-click-event ie)
  ;; Stub — menu-bar intercept only; falls through to C for the rest.
  (let* ((fow ((force %--ie-frame-or-window) ie)))
    (if (not ((force %frame-live-p) fow))
        #nil
        (let ((mb-event
               ((force %--mouse-click-menu-bar-intercept)
                fow
                ((force %--ie-x) ie)
                ((force %--ie-y) ie)
                ((force %--ie-modifiers) ie)
                ((force %--ie-timestamp) ie)
                fow)))
          (if mb-event
              mb-event
              ;; Fall through to C until 7.5.2+ builds out the
              ;; double-click + drag/release logic.  Transient
              ;; double-eval: the C fallback re-runs menu-bar
              ;; intercept for non-menu-bar clicks.  Evaporates
              ;; when the full handler replaces the fallback.
              ((force %--make-lispy-event-c) ie)))))))

\f
;;; imp-7.5.4 — button-up drag/click resolution (keyboard.c:7011–7117).
;;; The biggest block in imp-7.5.  Decides whether a button release
;;; is a click or a drag by comparing up-event coordinates against
;;; the saved down-event position.

(define %--line-number-mode-hscroll
  (delay (%c '--line-number-mode-hscroll)))
(define %--frame-relative-event-pos
  (delay (%c '--frame-relative-event-pos)))
(define %--set-down-mouse-line-number-width
  (delay (%c '--set-down-mouse-line-number-width)))
(define %window-live-p            (delay (%c 'window-live-p)))
(define %fboundp                  (delay (%c 'fboundp)))
(define %window-edges             (delay (%c 'window-edges)))

(define (mouse-up-resolve! fow x y timestamp mods start-pos position)
  ;; Button-up drag/click resolution (keyboard.c:7011–7117).
  ;; Returns (values mods position) where mods has the final
  ;; click/drag/double modifier bits and position may be
  ;; recomputed (window-edges edge case).

  (if (not start-pos)
      ;; No prior down event — ignore this up (C:7028-7029).
      (values mods position)

      (let ((click-or-drag click-modifier))

        ;; Check ignore_mouse_drag_p first (C:7032-7035).
        (if (not (eq? #nil ((force %--ignore-mouse-drag-p))))
            ((force %--set-ignore-mouse-drag-p) #nil)
            ;; Drag detection: compare up coords against down coords.
            (let* ((fuzz ((force %double-click-fuzz)))
                   (frel ((force %--frame-relative-event-pos)))
                   (xdiff (- x (car frel)))
                   (ydiff (- y (cdr frel))))

              (if (and (> fuzz 0)
                       (< (- fuzz) xdiff) (< xdiff fuzz)
                       (< (- fuzz) ydiff) (< ydiff fuzz)
                       (or (equal? (cadr start-pos) (cadr position))
                           ((force %--line-number-mode-hscroll)
                            start-pos position)
                           (not (equal? (car start-pos)
                                        (car position)))))
                  ;; Mouse hasn't moved enough — it's a click.
                  ;; Check for window-change redisplay edge case
                  ;; (C:7067-7096).
                  (if (and (or (not (equal? (car start-pos)
                                            (car position)))
                               (not (equal? (cadr start-pos)
                                            (cadr position))))
                           (fixnum? (cadr start-pos))
                           ((force %window-live-p) (car start-pos))
                           (not (eq? #nil
                                     ((force %fboundp)
                                      'window-edges))))
                      ;; Window changed — adjust position into
                      ;; old window bounds to avoid spurious drag.
                      (let* ((edges ((force %window-edges)
                                     (car start-pos) #t #nil #t))
                             (new-x (car frel))
                             (new-y (cdr frel))
                             (left (car edges))
                             (right (caddr edges))
                             (top (cadr edges))
                             (bottom (car (cdddr edges))))
                        (when (< new-x left) (set! new-x left))
                        (when (>= new-x right)
                          (set! new-x (- right 1)))
                        (when (< new-y top) (set! new-y top))
                        (when (>= new-y bottom)
                          (set! new-y (- bottom 1)))
                        (set! position
                              (make-lispy-position
                               fow new-x new-y timestamp))))
                  ;; Mouse moved enough — it's a drag (C:7050-7057).
                  (begin
                    ((force %--set-button-down-time) 0)
                    (set! click-or-drag drag-modifier)
                    ((force %--set-down-mouse-line-number-width) -1)))))

        ;; Build final modifiers (C:7107-7114): strip up_modifier,
        ;; OR in click_or_drag_modifier + double/triple from
        ;; double_click_count (already set by bookkeep!).
        (let ((dbl-count ((force %--double-click-count))))
          (set! mods (logior (logand mods (lognot up-modifier))
                             click-or-drag
                             (cond
                              ((< dbl-count 2) 0)
                              ((= dbl-count 2) double-modifier)
                              (else triple-modifier)))))
        (values mods position))))

;; Registration deferred until handler is behavior-complete.
;; (register-kind! 'mouse-click-event mle-mouse-click-event)
