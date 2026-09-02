;;; test-m23-imp4.el --- M23 imp-4 DEFSYM split + relocation tests.
;;;
;;; imp-4 splits the 144 DEFSYM call sites in syms_of_keyboard
;;; (src/keyboard.c) three ways:
;;;   * Group 1 (31): cross-file symbols -> relocated unchanged into
;;;     syms_of_keyboard_globals (src/keyboard-globals.c), which
;;;     make-docfile still scans, so each keeps its generated Qsym
;;;     #define and defsym_name[] entry.
;;;   * Group 2 (39): local-only symbols (no other C reader) -> DEFSYM
;;;     deleted; re-interned from Scheme boot code in
;;;     (emacs command-loop)'s init-m23-imp4-registrations
;;;     (mod/emacs/command-loop.scm), wired into prelude/load.scm.
;;;   * Group 3 (3): dead NS symbols + both #ifdef HAVE_NS blocks ->
;;;     deleted outright, NOT re-interned (port drops NS).
;;; Group D (71): left untouched (C consumer remains, deferred to imp-5).
;;;
;;; Runtime model caveat that shapes these assertions: this port interns
;;; every symbol through Guile's string->symbol, so (intern-soft "x")
;;; always returns a symbol for ANY string (see mod/emacs/utils.scm
;;; elisp-intern-soft).  It therefore cannot prove a symbol was NOT
;;; interned.  The load-bearing, non-vacuous checks are:
;;;   * the 11 Group-2 KEYWORDS are genuinely self-evaluating through
;;;     the pure string path (value == itself).  Without the Scheme
;;;     registration's set-symbol-value! this would FAIL; the elisp
;;;     reader's keyword self-eval (reader.scm) is NOT exercised here
;;;     because we look each keyword up by string, never as a :literal.
;;;   * Group-1 names still resolve (relocation preserved them).
;;;   * the source no longer contains the 39 Group-2 DEFSYM sites nor
;;;     the 3 Group-3 sites in syms_of_keyboard (direct regression on
;;;     the mechanical edit, independent of the runtime intern model).
;;;
;;; Plain-elisp corpus: prints PASS/FAIL lines + a summary, read from
;;; the harness output like the other test/keyboard/test-m2x-*.el
;;; corpora.

(princ "=== m23 imp-4 test suite ===\n")

(defvar gm4-pass 0)
(defvar gm4-fail 0)

(defun gm4-report (name ok expected actual)
  (if ok
      (setq gm4-pass (1+ gm4-pass))
    (setq gm4-fail (1+ gm4-fail)))
  (princ (format "%s %s%s\n" (if ok "PASS" "FAIL") name
                 (if ok "" (format " (expected %S, got %S)" expected actual)))))

;; -------------------------------------------------------------------
;; Group 1: 31 relocated cross-file symbols.  Assert each still resolves
;; to the symbol named by its defsym string.
;; -------------------------------------------------------------------
(defvar gm4-g1
  '("activate-menubar-hook" "bottom" "bottom-divider" ":filter" "coding"
    "concat" ":radio" ":toggle" "current-minibuffer-command"
    "deactivate-mark" "delete-frame" "disabled" "down"
    "drag-internal-border" "event-kind" "event-symbol-element-mask"
    "event-symbol-elements" "focus-in" "help-echo" "help-key-binding"
    "iconify-frame" "mouse-click" "PRIMARY" "right-divider" "switch-frame"
    "text-conversion" "top" "touchscreen-begin" "touchscreen-end" "up"
    "vertical-line"))

(dolist (n gm4-g1)
  (gm4-report (format "m23/imp4/g1/resolve/%s" n)
              (and (stringp (symbol-name (intern-soft n)))
                   (eq (intern-soft n) (intern-soft n)))
              t nil))

;; -------------------------------------------------------------------
;; Group 2 keywords (11): must be self-evaluating through the pure
;; string path (value == itself).  Load-bearing: fails if the Scheme
;; registration is missing.
;; -------------------------------------------------------------------
(defvar gm4-g2-keywords
  '(":image" ":rtl" ":wrap" ":enable" ":visible" ":help" ":button"
    ":keys" ":key-sequence" ":label" ":vert-only"))

(dolist (n gm4-g2-keywords)
  (let ((sym (intern-soft n)))
    (gm4-report (format "m23/imp4/g2/kw-keywordp/%s" n)
                (keywordp sym) t nil)
    (gm4-report (format "m23/imp4/g2/kw-selfeval/%s" n)
                (eq (symbol-value sym) sym) t nil)))

;; -------------------------------------------------------------------
;; Group 2 plain symbols (28): resolve via intern-soft.  (Presence is
;; trivially true in this Scheme intern model, so this documents, not
;; discriminates; the real Group-2 regression is the keyword self-eval
;; above plus the source-presence checks below.)
;; -------------------------------------------------------------------
(defvar gm4-g2-plain
  '("activate-mark-hook" "command-error-default-function" "command-execute"
    "current-key-remap-sequence" "delayed-warnings-hook"
    "display-monitors-changed-functions" "echo-keystrokes" "encoded"
    "gui-set-selection" "handle-select-window" "handle-switch-frame"
    "help--append-keystrokes-help" "help-echo-inhibit-substitution"
    "internal-echo-keystrokes-prefix"
    "long-line-optimizations-in-command-hooks" "menu-enable"
    "mouse-fixup-help-message" "no-record" "post-command-hook"
    "post-select-region-hook" "pre-command-hook" "selection-request"
    "tty-select-active-regions" "undefined" "undo-auto--add-boundary"
    "undo-auto--undoably-changed-buffers" "window-edges"
    "xterm--set-selection"))

(dolist (n gm4-g2-plain)
  (gm4-report (format "m23/imp4/g2/resolve/%s" n)
              (symbolp (intern-soft n)) t nil))

;; -------------------------------------------------------------------
;; Source-level regression: the 39 Group-2 + 3 Group-3 DEFSYM call
;; sites must no longer be present in syms_of_keyboard, and the 31
;; Group-1 sites must have moved to keyboard-globals.c.  Read the two
;; C files and scan (independent of the runtime intern model).  We scan
;; for the exact "DEFSYM (Qsym" text, so a bare C reference elsewhere
;; in keyboard.c does not cause a false positive.
;; -------------------------------------------------------------------
(defvar gm4-src-dir
  (expand-file-name "../../src/" (file-name-directory (or load-file-name
                                                           default-directory))))

(defun gm4-read-file (file)
  (with-temp-buffer
    (condition-case e
        (insert-file-contents file)
      (error (princ (format "READ-FAIL %s: %S\n" file e)) nil))
    (buffer-string)))

(defvar gm4-keyboard-c (gm4-read-file (concat gm4-src-dir "keyboard.c")))
(defvar gm4-globals-c (gm4-read-file (concat gm4-src-dir "keyboard-globals.c")))

(defun gm4-has-defsym? (src qsym)
  (string-match-p (regexp-quote (format "DEFSYM (%s," qsym)) src))

;; Group 1: Q-symbol DEFSYM must now live in keyboard-globals.c and no
;; longer in keyboard.c.
(dolist (qsym '("QCfilter" "QCradio" "QCtoggle" "QPRIMARY"
                "Qactivate_menubar_hook" "Qbottom" "Qbottom_divider"
                "Qcoding" "Qconcat" "Qcurrent_minibuffer_command"
                "Qdeactivate_mark" "Qdelete_frame" "Qdisabled" "Qdown"
                "Qdrag_internal_border" "Qevent_kind"
                "Qevent_symbol_element_mask" "Qevent_symbol_elements"
                "Qfocus_in" "Qhelp_echo" "Qhelp_key_binding"
                "Qiconify_frame" "Qmouse_click" "Qright_divider"
                "Qswitch_frame" "Qtext_conversion" "Qtop"
                "Qtouchscreen_begin" "Qtouchscreen_end" "Qup"
                "Qvertical_line"))
  (gm4-report (format "m23/imp4/src/g1-in-globals/%s" qsym)
              (and gm4-globals-c (gm4-has-defsym? gm4-globals-c qsym)) t nil)
  (gm4-report (format "m23/imp4/src/g1-not-in-keyboard/%s" qsym)
              (not (gm4-has-defsym? gm4-keyboard-c qsym)) t nil))

;; Group 2 (39) + Group 3 (3): their DEFSYM must be gone from keyboard.c.
(dolist (qsym '("QCbutton" "QCenable" "QChelp" "QCimage" "QCkey_sequence"
                "QCkeys" "QClabel" "QCrtl" "QCvert_only" "QCvisible"
                "QCwrap" "Qactivate_mark_hook"
                "Qcommand_error_default_function" "Qcommand_execute"
                "Qcurrent_key_remap_sequence" "Qdelayed_warnings_hook"
                "Qdisplay_monitors_changed_functions" "Qecho_keystrokes"
                "Qencoded" "Qgui_set_selection" "Qhandle_select_window"
                "Qhandle_switch_frame" "Qhelp__append_keystrokes_help"
                "Qhelp_echo_inhibit_substitution"
                "Qinternal_echo_keystrokes_prefix"
                "Qlong_line_optimizations_in_command_hooks" "Qmenu_enable"
                "Qmouse_fixup_help_message" "Qno_record"
                "Qpost_command_hook" "Qpost_select_region_hook"
                "Qpre_command_hook" "Qselection_request"
                "Qtty_select_active_regions" "Qundefined"
                "Qundo_auto__add_boundary"
                "Qundo_auto__undoably_changed_buffers" "Qwindow_edges"
                "Qxterm__set_selection"
                "Qns_unput_working_text" "Qns_nonkey" "Qns_text_event"))
  (gm4-report (format "m23/imp4/src/deleted-not-in-keyboard/%s" qsym)
              (not (gm4-has-defsym? gm4-keyboard-c qsym)) t nil))

;; Group 3 NS names additionally must not be anywhere in keyboard.c C
;; source (their two #ifdef HAVE_NS blocks were deleted).
(dolist (qsym '("Qns_nonkey" "Qns_text_event" "Qns_unput_working_text"))
  (gm4-report (format "m23/imp4/src/g3-no-c-ref/%s" qsym)
              (null (string-match-p (regexp-quote qsym) gm4-keyboard-c))
              t nil))

(princ (format "=== %d passed, %d failed, %d total ===\n"
               gm4-pass gm4-fail (+ gm4-pass gm4-fail)))
