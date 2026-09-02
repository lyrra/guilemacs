;;; test-m23-imp5.el --- M23 imp-5 keyboard residue + relocation tests.
;;;
;;; imp-5 (this commit) relocates the 23 cross-file/keyboard-local
;;; DEFVAR_LISP/_INT/_BOOL call sites that imp-1 had deferred (group C,
;;; keyboard-local C readers; group D, cross-file names imp-1's audit
;;; missed) out of syms_of_keyboard in src/keyboard.c into
;;; syms_of_keyboard_globals in src/keyboard-globals.c — the same pure
;;; relocation imp-2/imp-3 performed.  It also records review reasons for
;;; the Section B residue inside syms_of_keyboard (the ie-smob
;;; registration, the head_table[] Fput loop, and the three Fset
;;; defaults), all of which correctly stay in C.
;;;
;;; This corpus mirrors test-m23-imp2.el / test-m23-imp4.el:
;;;   * each relocated name is bound and reads its load-time default
;;;     (the relocation is silent-failure-safe: a missing
;;;     syms_of_keyboard_globals call yields a void-variable, not a
;;;     build error);
;;;   * names whose default loadup.el rewrites are bound-only (same
;;;     caveat test-m23-imp1.scm recorded for its loadup-overridden
;;;     set);
;;;   * source-level regression that the DEFVAR call sites moved out of
;;;     keyboard.c into keyboard-globals.c;
;;;   * Vspecial_event_map's live bindings still resolve (now registered
;;;     from Scheme by init-m23-imp5-registrations, which keys_of_keyboard
;;;     dispatches to; the old 16-entry initial_define_lispy_key C table
;;;     is gone, less the dropped-platform / dead-branch entries that
;;;     this build does not bind);
;;;   * the head_table[]-driven event-kind / event-symbol-elements
;;;     properties survive (they are Fput at syms time, still in C);
;;;   * the three Fset-to-nil defaults survive.
;;;
;;; Plain-elisp corpus: prints PASS/FAIL lines + a summary, read from the
;;; harness output like the other test/keyboard/test-m2x-*.el corpora.

(princ "=== m23 imp-5 test suite ===\n")

(defvar gm5-pass 0)
(defvar gm5-fail 0)

(defun gm5-report (name ok expected actual)
  (if ok
      (setq gm5-pass (1+ gm5-pass))
    (setq gm5-fail (1+ gm5-fail)))
  (princ (format "%s %s%s\n" (if ok "PASS" "FAIL") name
                 (if ok "" (format " (expected %S, got %S)" expected actual)))))

;; Each case: (elisp-name expected).  expected is:
;;   * bound-only -> assert bound, do not read the value
;;   * a value    -> assert (symbol-value var) equals it
;;   * keymap     -> assert (keymapp (symbol-value var))
;; Defaults were captured live by loading this file under the built
;; emacs.  help-event-list, prefix-help-command, timer-idle-list,
;; input-method-function, debug-on-event and minibuffer-message-timeout
;; are rewrapped by loadup.el after syms, so they are bound-only (their
;; C-side default value is not the value read at test time).
(defvar gm5-cases
  '((unread-post-input-method-events nil)
    (unread-input-method-events nil)
    (auto-save-interval 300)
    (echo-keystrokes 1)
    (polling-period 2.0)
    (num-input-keys 0)
    (last-event-frame nil)
    (last-event-device nil)
    (help-char 8)
    (help-event-list bound-only)
    (prefix-help-command bound-only)
    (cannot-suspend nil)
    (special-event-map keymap)
    (timer-list nil)
    (timer-idle-list bound-only)
    (input-method-function bound-only)
    (minibuffer-message-timeout bound-only)
    (debug-on-event bound-only)
    (select-active-regions t)
    (saved-region-selection nil)
    (attempt-stack-overflow-recovery t)
    (attempt-orderly-shutdown-on-fatal-signal t)
    (disable-inhibit-text-conversion nil)))

(dolist (case gm5-cases)
  (let ((var (car case))
        (expected (cadr case)))
    (gm5-report (format "m23/imp5/%s/boundp" var)
                (boundp var) 'boundp t)
    (cond
     ((eq expected 'bound-only) nil)
     ((eq expected 'keymap)
      (gm5-report (format "m23/imp5/%s/keymapp" var)
                  (keymapp (symbol-value var)) t nil))
     (t
      (gm5-report (format "m23/imp5/%s/default" var)
                  (equal expected (symbol-value var))
                  expected (symbol-value var))))))

;; Vfunction_key_map deliberately stayed in syms_of_keyboard (its DEFVAR
;; and the sparse keymap it installs must exist before
;; allocate_kboard -> init_kboard runs, inside syms_of_keyboard and
;; before syms_of_keyboard_globals).  Assert it is still bound to a
;; keymap (the ordering exception cr.org Finding noted).
(gm5-report "m23/imp5/function-key-map/keymapp"
            (keymapp (symbol-value 'function-key-map)) t nil)

;; -------------------------------------------------------------------
;; Source-level regression: the relocated DEFVAR_* call sites no longer
;; appear in syms_of_keyboard (keyboard.c) and now live in
;; keyboard-globals.c.  Scan the exact "DEFVAR_* (\"name\"" text so a
;; bare C variable reference elsewhere does not cause a false positive.
;; -------------------------------------------------------------------
(defvar gm5-src-dir
  (expand-file-name "../../src/" (file-name-directory (or load-file-name
                                                           default-directory))))

(defun gm5-read-file (file)
  (with-temp-buffer
    (condition-case e
        (insert-file-contents file)
      (error (princ (format "READ-FAIL %s: %S\n" file e)) nil))
    (buffer-string)))

(defvar gm5-keyboard-c (gm5-read-file (concat gm5-src-dir "keyboard.c")))
(defvar gm5-globals-c (gm5-read-file (concat gm5-src-dir "keyboard-globals.c")))

(defun gm5-has-defvar? (src name)
  ;; True relocated DEFVAR site is "DEFVAR_<KIND> (\"<name>\"".
  (let ((re (concat "DEFVAR_[A-Z_]+\\s-*(\"" (regexp-quote name) "\"")))
    (string-match-p re src)))

;; True relocated DEFVAR site prefix (LISP/INT/BOOL).
(dolist (name '("unread-post-input-method-events"
                "unread-input-method-events" "auto-save-interval"
                "echo-keystrokes" "polling-period" "num-input-keys"
                "last-event-frame" "last-event-device" "help-char"
                "help-event-list" "prefix-help-command" "cannot-suspend"
                "special-event-map" "timer-list" "timer-idle-list"
                "input-method-function" "minibuffer-message-timeout"
                "debug-on-event" "select-active-regions"
                "saved-region-selection" "attempt-stack-overflow-recovery"
                "attempt-orderly-shutdown-on-fatal-signal"
                "disable-inhibit-text-conversion"))
  (gm5-report (format "m23/imp5/src/in-globals/%s" name)
              (gm5-has-defvar? gm5-globals-c name) t nil)
  (gm5-report (format "m23/imp5/src/not-in-keyboard/%s" name)
              (not (gm5-has-defvar? gm5-keyboard-c name)) t nil))

;; -------------------------------------------------------------------
;; Source-level regression: keys_of_keyboard no longer installs
;; special-event-map bindings from C.  The whole initial_define_lispy_key
;; table moved to Scheme (init-m23-imp5-registrations).  Scan for the
;; literal call site so a stray future C reintroduction is caught.
;; -------------------------------------------------------------------
(gm5-report "m23/imp5/src/keys-of-keyboard/initial_define_lispy_key"
            (not (string-match-p "initial_define_lispy_key"
                                 gm5-keyboard-c))
            t (string-match-p "initial_define_lispy_key"
                              gm5-keyboard-c))

;; -------------------------------------------------------------------
;; Vspecial_event_map live bindings, registered from Scheme by
;; init-m23-imp5-registrations (src/keyboard.c keys_of_keyboard now
;; dispatches to it — see milestone).  Assert the entries this platform
;; binds resolve to the same command symbols the old C table produced.
;; Feature-guarded entries resolve per this build's live featurep result:
;;   * dbus-event / file-notify are bound (HAVE_DBUS, USE_FILE_NOTIFY);
;;   * thread-event is not (THREADS_ENABLED undefined);
;;   * dropped-platform entries (end-session, language-change) are not
;;     ported at all.
;; config-changed-event is rebound by loadup.el (dynamic-setting
;; installs dynamic-setting-handle-config-changed-event), so it is not
;; in the exact-command table below.
(defvar gm5-special
  '((delete-frame handle-delete-frame)
    (ns-put-working-text ns-put-working-text)
    (ns-unput-working-text ns-unput-working-text)
    (iconify-frame ignore)
    (make-frame-visible ignore)
    (save-session handle-save-session)
    (dbus-event dbus-handle-event)
    (file-notify file-notify-handle-event)
    (focus-in handle-focus-in)
    (focus-out handle-focus-out)
    (move-frame handle-move-frame)))

(dolist (pair gm5-special)
  (let ((event (car pair))
        (cmd (cadr pair)))
    (gm5-report (format "m23/imp5/special/%s" event)
                (eq (lookup-key special-event-map (vector event)) cmd)
                cmd (lookup-key special-event-map (vector event)))))

;; -------------------------------------------------------------------
;; head_table[]-driven event-kind / event-symbol-elements properties.
;; The head_table Fput loop stays a C-side loop in syms_of_keyboard
;; (review-recorded reason); assert its effect survives.
;; -------------------------------------------------------------------
(defvar gm5-head-kind
  '((mouse-movement mouse-movement)
    (scroll-bar-movement mouse-movement)
    (switch-frame switch-frame)
    (focus-in focus-in)
    (focus-out focus-out)
    (move-frame move-frame)
    (delete-frame delete-frame)
    (iconify-frame iconify-frame)
    (make-frame-visible make-frame-visible)
    (touchscreen-begin touchscreen)))

(dolist (pair gm5-head-kind)
  (let ((sym (car pair))
        (kind (cadr pair)))
    (gm5-report (format "m23/imp5/head-kind/%s" sym)
                (eq (get sym 'event-kind) kind) kind (get sym 'event-kind))))

(dolist (sym '(mouse-movement focus-in delete-frame iconify-frame
                              make-frame-visible))
  (gm5-report (format "m23/imp5/head-elements/%s" sym)
              (equal (get sym 'event-symbol-elements) (list sym))
              (list sym) (get sym 'event-symbol-elements)))

;; -------------------------------------------------------------------
;; The three Fset-to-nil defaults (Section B).  These symbols are Group
;; D (still-C consumer), so their DEFSYM and paired Fset stay in C.
;; -------------------------------------------------------------------
(dolist (sym '(input-method-exit-on-first-char
               input-method-use-echo-area echo-area-clear-hook))
  (gm5-report (format "m23/imp5/fset/%s" sym)
              (null (symbol-value sym)) nil (symbol-value sym)))

(princ (format "=== %d passed, %d failed, %d total ===\n"
               gm5-pass gm5-fail (+ gm5-pass gm5-fail)))
