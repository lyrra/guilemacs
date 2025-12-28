;;; run-all-tests.el --- Run all text property tests

(load-file "test/test-framework.el")

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

(message "========================================")
(message "ALL TESTS COMPLETE")
(message "========================================")
