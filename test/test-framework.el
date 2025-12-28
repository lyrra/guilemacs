;;; test-framework.el --- Simple test framework with parseable output

;; Test result tracking
(defvar test-framework-pass-count 0)
(defvar test-framework-fail-count 0)
(defvar test-framework-current-suite nil)

(defun test-begin (suite-name)
  "Begin a test suite."
  (setq test-framework-current-suite suite-name)
  (setq test-framework-pass-count 0)
  (setq test-framework-fail-count 0)
  (message "TEST-SUITE-BEGIN %s" suite-name))

(defun test-end ()
  "End current test suite and print summary."
  (message "TEST-SUITE-END %s PASS=%d FAIL=%d TOTAL=%d"
           test-framework-current-suite
           test-framework-pass-count
           test-framework-fail-count
           (+ test-framework-pass-count test-framework-fail-count))
  (setq test-framework-current-suite nil))

(defun test-assert (name condition)
  "Assert CONDITION is true, output result with NAME."
  (if condition
      (progn
        (setq test-framework-pass-count (1+ test-framework-pass-count))
        (message "TEST %s/%s PASS" test-framework-current-suite name))
    (progn
      (setq test-framework-fail-count (1+ test-framework-fail-count))
      (message "TEST %s/%s FAIL" test-framework-current-suite name))))

(defun test-equal (name expected actual)
  "Assert EXPECTED equals ACTUAL, output result with NAME."
  (let ((result (equal expected actual)))
    (if result
        (progn
          (setq test-framework-pass-count (1+ test-framework-pass-count))
          (message "TEST %s/%s PASS" test-framework-current-suite name))
      (progn
        (setq test-framework-fail-count (1+ test-framework-fail-count))
        (message "TEST %s/%s FAIL expected=%S actual=%S"
                 test-framework-current-suite name expected actual)))))

(defun test-eq (name expected actual)
  "Assert EXPECTED is eq to ACTUAL, output result with NAME."
  (let ((result (eq expected actual)))
    (if result
        (progn
          (setq test-framework-pass-count (1+ test-framework-pass-count))
          (message "TEST %s/%s PASS" test-framework-current-suite name))
      (progn
        (setq test-framework-fail-count (1+ test-framework-fail-count))
        (message "TEST %s/%s FAIL expected=%S actual=%S"
                 test-framework-current-suite name expected actual)))))

(defun test-not-nil (name actual)
  "Assert ACTUAL is not nil, output result with NAME."
  (if actual
      (progn
        (setq test-framework-pass-count (1+ test-framework-pass-count))
        (message "TEST %s/%s PASS" test-framework-current-suite name))
    (progn
      (setq test-framework-fail-count (1+ test-framework-fail-count))
      (message "TEST %s/%s FAIL expected=non-nil actual=nil"
               test-framework-current-suite name))))

(defun test-nil (name actual)
  "Assert ACTUAL is nil, output result with NAME."
  (if (null actual)
      (progn
        (setq test-framework-pass-count (1+ test-framework-pass-count))
        (message "TEST %s/%s PASS" test-framework-current-suite name))
    (progn
      (setq test-framework-fail-count (1+ test-framework-fail-count))
      (message "TEST %s/%s FAIL expected=nil actual=%S"
               test-framework-current-suite name actual))))

(provide 'test-framework)
