;;; kboard-lifecycle.scm --- M27 imp-2: KBOARD lifecycle field defaults
;;;   ((emacs kboard-lifecycle))
;;;
;;; Moves the field-default policy of init_kboard out of src/keyboard.c
;;; and into Scheme, over the M2 kboard smob.  src/keyboard.c keeps only
;;; the raw C-only field defaults (immediate_echo, kbd_macro_buffer,
;;; kbd_macro_bufsize, reference_count) and dispatches the rest here via
;;; init-kboard!.  See brief.org M27 imp-2.
;;;
;;; init-kboard! (KB TYPE), in order:
;;;   1.  resets the 15 nil-defaulting Lisp_Object fields through the
;;;       existing set-kboard-* accessors (M2 KBOARD_LISP_FIELD);
;;;   2.  sets window-system to TYPE;
;;;   3.  clears kbd_queue_has_data via --set-kboard-kbd-queue-has-data;
;;;   4.  makes two fresh sparse keymaps (input-decode-map and
;;;       local-function-key-map) and wires the latter's parent to
;;;       Vfunction_key_map.
;;;
;;; Conventions (same as imp-1's single-kboard.scm): defelisp delayed
;;; references for every C DEFUN ((force %--...)); elisp nil is #nil.
;;; The one non-DEFUN read is Vfunction_key_map, a DEFVAR_LISP — read it
;;; with (symbol-value 'function-key-map), not %c (which reads the
;;; function slot).
;;;
;;; The C dispatcher is invoked from allocate_kboard (during
;;; syms_of_keyboard) and init_keyboard.  The (emacs kboard-lifecycle)
;;; module is loaded by prelude/load.scm, which runs (load_guile_prelude)
;;; before syms_of_keyboard; and each setter is a DEFUN resolved lazily
;;; through its defelisp delay, so module load order is not a hazard.
;;;
;;; Live multi-terminal field-default verification (the imp-2 exit
;;; criterion) cannot run in this sandbox: creating a second terminal
;;; requires a real multi-tty session.  Recorded here explicitly instead
;;; of skipped silently; the single live boot and the stubbed-field
;;; corpus below are the achievable verification.

(define-module (emacs kboard-lifecycle)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:declarative? #t
  #:export (init-kboard!))

;; The 18 Lisp_Object field setters (KBOARD_LISP_FIELD, keyboard.c) —
;; referenced by name through defelisp delays so they resolve lazily.
(defelisp %set-kboard-overriding-terminal-local-map
  set-kboard-overriding-terminal-local-map)
(defelisp %set-kboard-last-command          set-kboard-last-command)
(defelisp %set-kboard-real-last-command     set-kboard-real-last-command)
(defelisp %set-kboard-keyboard-translate-table
  set-kboard-keyboard-translate-table)
(defelisp %set-kboard-last-repeatable-command
  set-kboard-last-repeatable-command)
(defelisp %set-kboard-prefix-arg            set-kboard-prefix-arg)
(defelisp %set-kboard-last-prefix-arg       set-kboard-last-prefix-arg)
(defelisp %set-kboard-kbd-queue             set-kboard-kbd-queue)
(defelisp %set-kboard-defining-kbd-macro    set-kboard-defining-kbd-macro)
(defelisp %set-kboard-last-kbd-macro        set-kboard-last-kbd-macro)
(defelisp %set-kboard-system-key-alist      set-kboard-system-key-alist)
(defelisp %set-kboard-system-key-syms       set-kboard-system-key-syms)
(defelisp %set-kboard-window-system         set-kboard-window-system)
(defelisp %set-kboard-local-function-key-map
  set-kboard-local-function-key-map)
(defelisp %set-kboard-input-decode-map      set-kboard-input-decode-map)
(defelisp %set-kboard-default-minibuffer-frame
  set-kboard-default-minibuffer-frame)
(defelisp %set-kboard-echo-string           set-kboard-echo-string)
(defelisp %set-kboard-echo-prompt           set-kboard-echo-prompt)

;; The raw bitfield flag setter (keyboard.c) — only way Scheme can drive
;; kbd_queue_has_data, which KBOARD_LISP_FIELD cannot cover.
(defelisp %--set-kboard-kbd-queue-has-data  --set-kboard-kbd-queue-has-data)

;; keymap.c DEFUNs used for the two fresh maps.
(defelisp %make-sparse-keymap               make-sparse-keymap)
(defelisp %set-keymap-parent                set-keymap-parent)

;; Vfunction_key_map is a DEFVAR_LISP, read via the elisp symbol-value
;; DEFUN (a Scheme-level (symbol-value ...) binding does not exist here).
(defelisp %symbol-value                     symbol-value)

(define (init-kboard! kb type)
  ;; 1. nil-defaulting Lisp_Object fields — mirrors the C body 1:1 so a
  ;;    missed setter is a diff against init_kboard (Risk 3 in brief.org).
  ((force %set-kboard-overriding-terminal-local-map) kb #nil)
  ((force %set-kboard-last-command) kb #nil)
  ((force %set-kboard-real-last-command) kb #nil)
  ((force %set-kboard-keyboard-translate-table) kb #nil)
  ((force %set-kboard-last-repeatable-command) kb #nil)
  ((force %set-kboard-prefix-arg) kb #nil)
  ((force %set-kboard-last-prefix-arg) kb #nil)
  ((force %set-kboard-kbd-queue) kb #nil)
  ((force %set-kboard-defining-kbd-macro) kb #nil)
  ((force %set-kboard-last-kbd-macro) kb #nil)
  ((force %set-kboard-system-key-alist) kb #nil)
  ((force %set-kboard-system-key-syms) kb #nil)
  ((force %set-kboard-echo-string) kb #nil)
  ((force %set-kboard-echo-prompt) kb #nil)
  ((force %set-kboard-default-minibuffer-frame) kb #nil)
  ;; 2. window-system = TYPE.
  ((force %set-kboard-window-system) kb type)
  ;; 3. kbd_queue_has_data is a raw bitfield — clear via its shim.
  ((force %--set-kboard-kbd-queue-has-data) kb #nil)
  ;; 4. two fresh keymaps; local-function-key-map's parent is
  ;;    Vfunction_key_map (a DEFVAR_LISP, read by symbol-value).
  ((force %set-kboard-input-decode-map)
   kb ((force %make-sparse-keymap) #nil))
  (let ((lfkm ((force %make-sparse-keymap) #nil)))
    ((force %set-kboard-local-function-key-map) kb lfkm)
    ((force %set-keymap-parent) lfkm ((force %symbol-value) 'function-key-map))))
