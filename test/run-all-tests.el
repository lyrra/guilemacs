;;; run-all-tests.el --- Run all text property tests

(load-file "test/test-framework.el")

(message "")
(message "========================================")
(message "READER TEST SUITE")
(message "========================================")
(message "")

(load-file "test/reader/test-hash-syntax.el")
(message "")

(message "")
(message "========================================")
(message "ELISP EVAL CLOSURE TEST SUITE")
(message "========================================")
(message "")

(load-file "test/elisp/test-eval-closure.el")
(message "")

(message "")
(message "========================================")
(message "INTERN/OBARRAY/MAPATOMS TEST SUITE")
(message "========================================")
(message "")

(load-file "test/obarray/test-intern-obarray.el")
(message "")

(message "")
(message "========================================")
(message "STRINGS TEST SUITE")
(message "========================================")
(message "")

(load-file "test/strings/casefiddle.el")
(message "")

(message "")
(message "========================================")
(message "GENERALIZED VARIABLES (GV) TEST SUITE")
(message "========================================")
(message "")

(load-file "test/gv/test-gv-setf.el")
(message "")

(message "")
(message "========================================")
(message "TEXT PROPERTIES TEST SUITE")
(message "========================================")
(message "")

;; Run all test files
(load-file "test/text-property/test-basic-operations.el")
(message "")

(load-file "test/text-property/test-phase5-operations.el")
(message "")

(load-file "test/text-property/test-font-lock-faces.el")
(message "")

(load-file "test/text-property/test-edge-cases.el")
(message "")

(load-file "test/text-property/test-workflow-integration.el")
(message "")

(load-file "test/text-property/test-string-operations.el")
(message "")

(load-file "test/text-property/test-interval-management.el")
(message "")

(load-file "test/text-property/test-buffer-modifications.el")
(message "")

(load-file "test/text-property/test-property-navigation.el")
(message "")

(load-file "test/text-property/test-no-properties.el")
(message "")

(load-file "test/text-property/test-narrow-widen.el")
(message "")

(load-file "test/text-property/test-substring-operations.el")
(message "")

(load-file "test/text-property/test-scheme-storage.el")
(message "")

(load-file "test/text-property/test-equal-including-properties.el")
(message "")

(load-file "test/text-property/test-known-bugs.el")
(message "")

(message "")
(message "========================================")
(message "BUFFER LOCALS TEST SUITE")
(message "========================================")
(message "")

(load-file "test/buffer/test-buffer-locals.el")
(message "")

(message "")
(message "========================================")
(message "EVAL TEST SUITE")
(message "========================================")
(message "")

;; Use eval-buffer instead of load-file to avoid Guile compilation issues
(with-temp-buffer
  (insert-file-contents "test/eval/test-throw-propagation.el")
  (eval-buffer))
(message "")

(message "")
(message "========================================")
(message "KEYBOARD PORT TEST SUITE")
(message "========================================")
(message "")

(load "test/keyboard/test-stub.el")             ; M0
(load "test/keyboard/test-event-modifiers.el")   ; M1
(load "test/keyboard/test-kboard.el")            ; M2
(load "test/keyboard/test-recent-keys.el")       ; M3
(load "test/keyboard/test-recursive-edit.el")    ; M4
(load "test/keyboard/test-this-command-keys.el") ; M5
(load "test/keyboard/test-consolidation.el")     ; Consolidation
(load "test/keyboard/test-command-loop.el")      ; M7a
(load "test/keyboard/test-read-key-sequence.el") ; M6a
(load "test/keyboard/test-read-char.el")         ; M8a
(load "test/keyboard/test-menu-item-parse.el")   ; M10 imp-1.3
(load "test/keyboard/test-tab-bar-items.el")    ; M10 imp-2.2
(load "test/keyboard/test-tool-bar-items.el")   ; M10 imp-3.1
(load "test/keyboard/test-menu-bar-items.el")  ; M10 imp-4.1
(load "test/keyboard/test-kbd-escape-shims.el")   ; M11 imp-1.3
(load "test/keyboard/test-kbd-wait-loop.el")      ; M11 imp-2
(load "test/keyboard/test-kbd-dispatch.el")       ; M11 imp-3
(load "test/keyboard/test-kbd-mouse-motion.el")   ; M11 imp-4
(load "test/keyboard/test-m12-shims.el")          ; M12 imp-1
(load "test/keyboard/test-main-queue.el")         ; M12 imp-3
(load "test/keyboard/test-m13-shims.el")          ; M13 imp-1
(load "test/keyboard/test-m13-store.el")          ; M13 imp-2
(load "test/keyboard/test-m14-shims.el")          ; M14 imp-1
(load "test/keyboard/test-m14-bodies.el")         ; M14 imp-2
(load "test/keyboard/test-m14-predicates.el")     ; M14 imp-4
(load "test/keyboard/test-m15-shims.el")          ; M15 imp-1
(load "test/keyboard/test-m15-bodies.el")         ; M15 imp-2
(load "test/keyboard/test-m15-timers.el")         ; M15 imp-4
(load "test/keyboard/test-m16-shims.el")          ; M16 imp-1
(load "test/keyboard/test-m16-bodies.el")         ; M16 imp-2
(load "test/keyboard/test-m16-help-echo.el")      ; M16 imp-3
(load "test/keyboard/test-m17-shims.el")          ; M17 imp-1
(load "test/keyboard/test-m17-bodies.el")         ; M17 imp-2
(load "test/keyboard/test-m17-record-char.el")    ; M17 imp-3
(load "test/keyboard/test-m18-shims.el")          ; M18 imp-1
(load "test/keyboard/test-m18-bodies.el")         ; M18 imp-2
(load "test/keyboard/test-m18-echo.el")           ; M18 imp-3
(load "test/keyboard/test-m19-bodies.el")         ; M19 imp-1
(load "test/keyboard/test-m19-fixes.el")          ; M19 cr.org findings
(load "test/keyboard/test-m19-shims.el")          ; M19 imp-2
(load "test/keyboard/test-m19-kind.el")           ; M19 imp-3
(load "test/keyboard/test-m19-tables.el")         ; M19 imp-4
(load "test/keyboard/test-m20-menu-prompt.el")    ; M20 imp-1 + imp-2
(message "")

(message "========================================")
(message "ALL TESTS COMPLETE")
(message "========================================")

(message "scheme->C and C->scheme calls: %S" (debug-guile-cross-count))
