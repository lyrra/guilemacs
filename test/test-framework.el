;;; test-framework.el --- Simple test framework with parseable output (SRFI-64 compatible)

;; Test result tracking
(defvar test-framework-pass-count 0)
(defvar test-framework-fail-count 0)
(defvar test-framework-xfail-count 0)  ; expected failures
(defvar test-framework-xpass-count 0)  ; unexpected passes
(defvar test-framework-current-suite nil)
(defvar test-framework-expect-fail-count 0)  ; how many upcoming tests expected to fail

(defun test-begin (suite-name)
  "Begin a test suite."
  (setq test-framework-current-suite suite-name)
  (setq test-framework-pass-count 0)
  (setq test-framework-fail-count 0)
  (setq test-framework-xfail-count 0)
  (setq test-framework-xpass-count 0)
  (setq test-framework-expect-fail-count 0)
  (message "TEST-SUITE-BEGIN %s" suite-name))

(defun test-end ()
  "End current test suite and print summary."
  (message "TEST-SUITE-END %s PASS=%d FAIL=%d XFAIL=%d XPASS=%d TOTAL=%d"
           test-framework-current-suite
           test-framework-pass-count
           test-framework-fail-count
           test-framework-xfail-count
           test-framework-xpass-count
           (+ test-framework-pass-count test-framework-fail-count
              test-framework-xfail-count test-framework-xpass-count))
  (setq test-framework-current-suite nil))

(defun test-expect-fail (&optional count)
  "Mark the next COUNT tests as expected to fail (SRFI-64 style).
COUNT defaults to 1. When an expected-fail test fails, it reports XFAIL.
When an expected-fail test unexpectedly passes, it reports XPASS."
  (setq test-framework-expect-fail-count (or count 1)))

(defun test-framework--expecting-fail-p ()
  "Return non-nil if current test is expected to fail, decrementing counter."
  (when (> test-framework-expect-fail-count 0)
    (setq test-framework-expect-fail-count (1- test-framework-expect-fail-count))
    t))

(defun test-framework--record-result (name passed &optional details)
  "Record test result. PASSED is t if test passed, nil if failed.
DETAILS is optional string with extra info for failures."
  (let ((expecting-fail (test-framework--expecting-fail-p)))
    (cond
     ;; Expected to fail and did fail -> XFAIL
     ((and expecting-fail (not passed))
      (setq test-framework-xfail-count (1+ test-framework-xfail-count))
      (message "TEST %s/%s XFAIL (known bug)%s"
               test-framework-current-suite name
               (if details (concat " " details) "")))
     ;; Expected to fail but passed -> XPASS
     ((and expecting-fail passed)
      (setq test-framework-xpass-count (1+ test-framework-xpass-count))
      (message "TEST %s/%s XPASS (unexpectedly passed!)"
               test-framework-current-suite name))
     ;; Normal pass
     (passed
      (setq test-framework-pass-count (1+ test-framework-pass-count))
      (message "TEST %s/%s PASS" test-framework-current-suite name))
     ;; Normal fail
     (t
      (setq test-framework-fail-count (1+ test-framework-fail-count))
      (message "TEST %s/%s FAIL%s"
               test-framework-current-suite name
               (if details (concat " " details) ""))))))

(defun test-assert (name condition)
  "Assert CONDITION is true, output result with NAME."
  (test-framework--record-result name condition))

(defun test-equal (name expected actual)
  "Assert EXPECTED equals ACTUAL, output result with NAME."
  (test-framework--record-result
   name
   (equal expected actual)
   (format "expected=%S actual=%S" expected actual)))

(defun test-eq (name expected actual)
  "Assert EXPECTED is eq to ACTUAL, output result with NAME."
  (test-framework--record-result
   name
   (eq expected actual)
   (format "expected=%S actual=%S" expected actual)))

(defun test-not-nil (name actual)
  "Assert ACTUAL is not nil, output result with NAME."
  (test-framework--record-result
   name
   actual
   "expected=non-nil actual=nil"))

(defun test-nil (name actual)
  "Assert ACTUAL is nil, output result with NAME."
  (test-framework--record-result
   name
   (null actual)
   (format "expected=nil actual=%S" actual)))

(provide 'test-framework)
