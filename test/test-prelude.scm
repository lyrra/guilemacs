;; Test suite for SSDATA elevation functions
;; Tests all the new Scheme functions that replace C string operations

(import (srfi 64))

(load "../prelude/lookup-functions.scm")

;; Custom test runner with fancy output
(define (fancy-test-runner)
  (let ((runner (test-runner-null))
        (passed-tests '())
        (failed-tests '())
        (test-count 0)
        (group-stack '())
        (current-group #f))

    (test-runner-on-test-begin! runner
      (lambda (runner)
        (set! test-count (+ test-count 1))))

    (test-runner-on-test-end! runner
      (lambda (runner)
        (let* ((result (test-result-alist runner))
               (test-name (assq-ref result 'test-name))
               (result-kind (test-result-kind runner))
               (group-name (if current-group current-group "General")))
          (cond
            ((eq? result-kind 'pass)
             (set! passed-tests (cons (list group-name test-name) passed-tests))
             (display (string-append "✓ " test-name "\n")))
            ((eq? result-kind 'fail)
             (let ((expected (assq-ref result 'expected-value))
                   (actual (assq-ref result 'actual-value)))
               (set! failed-tests (cons (list group-name test-name expected actual) failed-tests))
               (display (string-append "✗ " test-name
                                       " (expected: " (format #f "~s" expected)
                                       ", got: " (format #f "~s" actual) ")\n"))))
            (else
             (set! failed-tests (cons (list group-name test-name "unknown" "unknown") failed-tests))
             (display (string-append "? " test-name " (unknown result)\n")))))))

    (test-runner-on-group-begin! runner
      (lambda (runner suite-name count)
        (set! group-stack (cons current-group group-stack))
        (set! current-group suite-name)
        (if (> (string-length suite-name) 0)
            (display (string-append "\n=== " suite-name " ===\n")))))

    (test-runner-on-group-end! runner
      (lambda (runner)
        (set! current-group (car group-stack))
        (set! group-stack (cdr group-stack))))

    (test-runner-on-final! runner
      (lambda (runner)
        (let ((total-passed (length passed-tests))
              (total-failed (length failed-tests)))
          (display "\n")
          (display "=====================================\n")
          (display "           TEST SUMMARY\n")
          (display "=====================================\n")
          (display (string-append "Total tests run: " (number->string test-count) "\n"))
          (display (string-append "✓ Passed: " (number->string total-passed) "\n"))
          (display (string-append "✗ Failed: " (number->string total-failed) "\n"))
          (display (string-append "Success rate: "
                                  (if (> test-count 0)
                                      (string-append (number->string
                                                       (inexact->exact
                                                        (round (* 100 (/ total-passed test-count)))))
                                                     "%")
                                      "N/A")
                                  "\n"))

          (when (> total-failed 0)
            (display "\n--- FAILED TESTS ---\n")
            (for-each
              (lambda (failure)
                (let ((group (car failure))
                      (name (cadr failure))
                      (expected (caddr failure))
                      (actual (cadddr failure)))
                  (display (string-append "✗ [" group "] " name "\n"))
                  (display (string-append "  Expected: " (format #f "~s" expected) "\n"))
                  (display (string-append "  Actual:   " (format #f "~s" actual) "\n\n"))))
              (reverse failed-tests)))

          (when (> total-passed 0)
            (display "\n--- PASSED TESTS SUMMARY ---\n")
            (let ((grouped-passed (group-tests-by-category passed-tests)))
              (for-each
                (lambda (group-pair)
                  (let ((group-name (car group-pair))
                        (group-tests (cdr group-pair)))
                    (display (string-append "✓ " group-name ": " (number->string (length group-tests)) " tests passed\n"))))
                grouped-passed)))

          (display "=====================================\n"))))

    runner))

(define (group-tests-by-category test-list)
  "Group tests by their category/group name"
  (let ((groups '()))
    (for-each
      (lambda (test)
        (let* ((group-name (car test))
               (existing (assoc group-name groups)))
          (if existing
              (set-cdr! existing (cons test (cdr existing)))
              (set! groups (cons (cons group-name (list test)) groups)))))
      test-list)
    groups))

;; Set up the fancy test runner
(test-runner-current (fancy-test-runner))

(test-begin "SSDATA Elevation Functions")

(test-group "Color Parsing and Validation"
  (test-equal "parse #RRGGBB hex color"
              '(255 128 64)
              (parse-color-spec "#ff8040"))

  (test-equal "parse #RGB shorthand hex color"
              '(255 0 0)
              (parse-color-spec "#f00"))

  (test-equal "parse rgb() function format"
              '(255 128 64)
              (parse-color-spec "rgb(255, 128, 64)"))

  (test-equal "parse named color red"
              '(255 0 0)
              (parse-color-spec "red"))

  (test-equal "parse named color blue"
              '(0 0 255)
              (parse-color-spec "blue"))

  (test-assert "invalid color returns #f"
               (not (parse-color-spec "invalid-color")))

  (test-equal "validate valid color name"
              'valid
              (validate-color-name "red"))

  (test-equal "validate valid hex color"
              'valid
              (validate-color-name "#ff0000"))

  (test-equal "validate invalid color name"
              'invalid
              (validate-color-name "notacolor")))

(test-group "String Pattern Matching"
  (test-assert "detect whitespace in string"
               (string-contains-whitespace? "hello world"))

  (test-assert "detect tab character"
               (string-contains-whitespace? "hello\tworld"))

  (test-assert "detect newline character"
               (string-contains-whitespace? "hello\nworld"))

  (test-assert "no whitespace in continuous string"
               (not (string-contains-whitespace? "helloworld")))

  (test-assert "empty string has no whitespace"
               (not (string-contains-whitespace? ""))))

(test-group "Frame Name Validation"
  (test-assert "valid F<number> format"
               (is-frame-name-fnn-format? "F1"))

  (test-assert "valid F<multi-digit> format"
               (is-frame-name-fnn-format? "F123"))

  (test-assert "invalid: missing F prefix"
               (not (is-frame-name-fnn-format? "123")))

  (test-assert "invalid: F without number"
               (not (is-frame-name-fnn-format? "F")))

  (test-assert "invalid: mixed alphanumeric"
               (not (is-frame-name-fnn-format? "F12a")))

  (test-assert "invalid: lowercase f"
               (not (is-frame-name-fnn-format? "f123"))))

(test-group "Font Name Validation"
  (test-equal "valid XLFD font name"
              'valid
              (validate-xlfd-font-name
               "-adobe-helvetica-medium-r-normal--12-120-75-75-p-67-iso8859-1"))

  (test-equal "invalid: too short"
              'invalid
              (validate-xlfd-font-name "helvetica"))

  (test-equal "invalid: insufficient dashes"
              'invalid
              (validate-xlfd-font-name "-adobe-helvetica-medium")))

(test-group "File Path Validation"
  (test-assert "absolute path detection"
               (is-absolute-path? "/usr/bin/emacs"))

  (test-assert "relative path detection"
               (not (is-absolute-path? "relative/path")))

  (test-assert "empty path is not absolute"
               (not (is-absolute-path? "")))

  (test-assert "detect ../ directory traversal"
               (has-directory-traversal? "../etc/passwd"))

  (test-assert "detect /../ in middle of path"
               (has-directory-traversal? "/usr/../etc/passwd"))

  (test-assert "detect .. at end of path"
               (has-directory-traversal? "/usr/bin/.."))

  (test-assert "normal path has no traversal"
               (not (has-directory-traversal? "/usr/bin/emacs"))))

(test-group "Helper Functions"
  (test-assert "string-contains returns index when found"
               (number? (string-contains "hello world" "wor")))

  (test-assert "string-contains returns #f when not found"
               (not (string-contains "hello world" "xyz")))

  (test-equal "string-split by delimiter"
              '("a" "b" "c")
              (string-split "a,b,c" #\,))

  (test-equal "string-split empty string"
              '("")
              (string-split "" #\,))

  (test-assert "string-every with all matching chars"
               (string-every char-numeric? "12345"))

  (test-assert "string-every with some non-matching chars"
               (not (string-every char-numeric? "123a5"))))

(test-group "Face Attribute Parsing"
  (test-equal "parse bold attribute"
              'true
              (parse-face-bool-attribute "bold"))

  (test-equal "parse italic attribute"
              'true
              (parse-face-bool-attribute "italic"))

  (test-equal "parse normal attribute"
              'false
              (parse-face-bool-attribute "normal"))

  (test-equal "parse unknown attribute"
              'nil
              (parse-face-bool-attribute "unknown")))

(test-group "Yes/No Response Processing"
  (test-equal "process 'yes' response"
              'yes
              (process-yesno-response "yes"))

  (test-equal "process 'y' response"
              'yes
              (process-yesno-response "y"))

  (test-equal "process 'no' response"
              'no
              (process-yesno-response "no"))

  (test-equal "process 'n' response"
              'no
              (process-yesno-response "n"))

  (test-equal "process invalid response"
              'invalid
              (process-yesno-response "maybe")))

(test-group "Special Buffer Name Detection"
  (test-assert "*scratch* buffer is special"
               (is-special-buffer-name? "*scratch*"))

  (test-assert "*messages* buffer is special"
               (is-special-buffer-name? "*messages*"))

  (test-assert "hidden buffer (space prefix) is special"
               (is-special-buffer-name? " *hidden*"))

  (test-assert "regular file is not special"
               (not (is-special-buffer-name? "README.md")))

  (test-assert "empty buffer name is special"
               (is-special-buffer-name? "")))

(test-group "Lookup Functions"
  (test-equal "color map lookup found"
              'rgb-red
              (let ((color-map '(("red" . rgb-red) ("blue" . rgb-blue))))
                (lookup-color-in-map color-map "red")))

  (test-equal "color map case-insensitive lookup"
              'rgb-red
              (let ((color-map '(("Red" . rgb-red) ("Blue" . rgb-blue))))
                (lookup-color-in-map color-map "RED")))

  (test-assert "color map lookup not found"
               (let ((color-map '(("red" . rgb-red) ("blue" . rgb-blue))))
                 (not (lookup-color-in-map color-map "green"))))

  (test-equal "case-insensitive alist lookup"
              'value1
              (let ((alist '(("Key1" . value1) ("Key2" . value2))))
                (lookup-in-alist-ci alist "key1")))

  (test-equal "case-sensitive alist lookup"
              'value1
              (let ((alist '(("key1" . value1) ("key2" . value2))))
                (lookup-in-alist alist "key1")))

  (test-assert "symbol list lookup found"
               (let ((symbol-list '(sym1 sym2 sym3)))
                 (lookup-symbol-in-list symbol-list "sym2")))

  (test-assert "symbol list lookup not found"
               (let ((symbol-list '(sym1 sym2 sym3)))
                 (not (lookup-symbol-in-list symbol-list "sym4")))))

(test-end)
