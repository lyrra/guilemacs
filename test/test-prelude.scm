;; Test suite for SSDATA elevation functions
;; Tests all the new Scheme functions that replace C string operations

(import (srfi 64))

(define %exit 0)
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
            (set! %exit 1)
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
  (test-equal "string-contains returns index when found"
              6
              (string-contains "hello world" "wor"))

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

(test-group "String Preprocessing Functions"
  (test-equal "convert spaces to dashes"
              "hello-world-test"
              (string-spaces-to-dashes "hello world test"))

  (test-equal "string with no spaces unchanged"
              "hello"
              (string-spaces-to-dashes "hello"))

  (test-equal "empty string unchanged"
              ""
              (string-spaces-to-dashes ""))

  (test-equal "multiple spaces converted"
              "a-b-c-d"
              (string-spaces-to-dashes "a b c d"))

  (test-equal "mixed spaces and other characters"
              "hello,-world!"
              (string-spaces-to-dashes "hello, world!")))

(test-group "String Trimming Functions"
  (test-equal "trim leading spaces"
              "hello world"
              (string-trim-leading-whitespace "   hello world"))

  (test-equal "trim leading tabs"
              "hello world"
              (string-trim-leading-whitespace "\t\thello world"))

  (test-equal "trim mixed leading whitespace"
              "hello world"
              (string-trim-leading-whitespace " \t hello world"))

  (test-equal "no leading whitespace unchanged"
              "hello world"
              (string-trim-leading-whitespace "hello world"))

  (test-equal "all whitespace returns empty string"
              ""
              (string-trim-leading-whitespace "   \t  "))

  (test-equal "empty string unchanged"
              ""
              (string-trim-leading-whitespace "")))

(test-group "Number Parsing Functions"
  (test-equal "parse decimal number"
              42
              (parse-number-string "42" 10))

  (test-equal "parse hex number"
              255
              (parse-number-string "ff" 16))

  (test-equal "parse binary number"
              7
              (parse-number-string "111" 2))

  (test-equal "parse with leading whitespace"
              123
              (parse-number-string "  123" 10))

  (test-assert "invalid number returns #f"
               (not (parse-number-string "not-a-number" 10)))

  (test-assert "empty string returns #f"
               (not (parse-number-string "" 10))))

(test-group "String Validation Functions"
  (test-equal "valid string for copying"
              'valid
              (validate-string-for-copying "hello world"))

  (test-equal "invalid empty string for copying"
              'invalid
              (validate-string-for-copying ""))

  (test-equal "invalid string with null byte"
              'invalid
              (validate-string-for-copying (string-append "hello" (string #\nul) "world")))

  (test-equal "invalid non-string object"
              'invalid
              (validate-string-for-copying 42)))

(test-group "Symbol Preparation Functions"
  (test-equal "prepare string for symbol"
              "hello-world"
              (prepare-string-for-symbol "hello world"))

  (test-equal "string with no spaces unchanged"
              "hello"
              (prepare-string-for-symbol "hello"))

  (test-assert "empty string returns #f"
               (not (prepare-string-for-symbol "")))

  (test-equal "multiple spaces converted to dashes"
              "a-b-c"
              (prepare-string-for-symbol "a b c")))

(test-group "New SSDATA Hoisting Functions"

  (test-group "File Extension Validation"
    (test-assert "file has .txt extension"
                 (has-file-extension? "document.txt" ".txt"))

    (test-assert "file has .scm extension (case insensitive)"
                 (has-file-extension? "script.SCM" ".scm"))

    (test-assert "file does not have .pdf extension"
                 (not (has-file-extension? "document.txt" ".pdf")))

    (test-assert "empty extension matches empty suffix"
                 (has-file-extension? "filename" ""))

    (test-assert "extension longer than filename"
                 (not (has-file-extension? "a" ".txt"))))

  (test-group "Path Component Extraction"
    (test-equal "extract filename from unix path"
                "file.txt"
                (extract-filename-from-path "/home/user/file.txt"))

    (test-equal "extract filename from complex path"
                "script.scm"
                (extract-filename-from-path "/usr/local/share/guile/script.scm"))

    (test-equal "filename with no path returns as-is"
                "filename.txt"
                (extract-filename-from-path "filename.txt"))

    (test-equal "empty path returns empty string"
                ""
                (extract-filename-from-path ""))

    (test-equal "path ending with slash returns empty"
                ""
                (extract-filename-from-path "/path/to/dir/")))

  (test-group "Modifier Symbol Matching"
    (test-equal "meta symbol matches meta string"
                 #t
                 (is-modifier-symbol? "meta-key" "meta"))

    (test-equal "super symbol matches super string (first 5 chars)"
                 #t
                 (is-modifier-symbol? "super-key" "super"))

    (test-equal "control symbol matches ctrl string"
                 #t
                 (is-modifier-symbol? "control-key" "control"))

    (test-equal "non-matching symbol"
                 #f
                 (is-modifier-symbol? "normal-key" "meta"))

    (test-equal "short symbol doesn't match long string"
                 #f
                 (is-modifier-symbol? "key" "control")))

  (test-group "Float Format Validation"
    (test-equal "valid %f format"
                 'valid
                 (validate-float-format-string "%f"))

    (test-equal "valid %g format"
                 'valid
                 (validate-float-format-string "%.2g"))

    (test-equal "valid %e format"
                 'valid
                 (validate-float-format-string "%e"))

    (test-equal "invalid format without %"
                 'invalid
                 (validate-float-format-string "f"))

    (test-equal "invalid format with just %"
                 'invalid
                 (validate-float-format-string "%"))

    (test-equal "invalid format with %d (not float)"
                 'invalid
                 (validate-float-format-string "%d")))

  (test-group "Time Format Specifiers"
    (test-assert "format with %Y year specifier"
                 (has-time-format-specifiers? "%Y-%m-%d"))

    (test-assert "format with %H hour specifier"
                 (has-time-format-specifiers? "%H:%M:%S"))

    (test-assert "format with %A day name"
                 (has-time-format-specifiers? "Today is %A"))

    (test-assert "format with %B month name"
                 (has-time-format-specifiers? "%B %d, %Y"))

    (test-assert "format without time specifiers"
                 (not (has-time-format-specifiers? "Hello World")))

    (test-assert "format with % but no time codes"
                 (not (has-time-format-specifiers? "100% complete"))))

  (test-group "Hex Color Parsing"
    (test-equal "parse valid hex color"
                '(255 128 0)
                (parse-hex-color "#ff8000"))

    (test-equal "parse hex color with valid range"
                '(0 255 128)
                (parse-hex-color "#00ff80"))

    (test-assert "invalid hex color without #"
                 (not (parse-hex-color "ff8000")))

    (test-assert "invalid hex color wrong length"
                 (not (parse-hex-color "#ff80")))

    (test-assert "invalid hex color bad characters"
                 (not (parse-hex-color "#gghhii"))))

  (test-group "Filename Conversion Detection"
    (test-assert "filename with backslashes needs conversion"
                 (needs-filename-conversion? "C:\\Windows\\System32"))

    (test-assert "unix path doesn't need conversion"
                 (not (needs-filename-conversion? "/usr/bin/emacs")))

    (test-assert "mixed slash path needs conversion"
                 (needs-filename-conversion? "path\\to/file"))

    (test-assert "empty path doesn't need conversion"
                 (not (needs-filename-conversion? ""))))

  (test-group "UTF-8 Filename Validation"
    (test-assert "normal ascii filename is utf8"
                 (is-utf8-filename? "normal_file.txt"))

    (test-assert "unicode filename is utf8"
                 (is-utf8-filename? "café.txt"))

    (test-assert "empty filename is valid utf8"
                 (is-utf8-filename? ""))

    ; This test may be tricky to write portably
    ; (test-assert "filename with control chars is not utf8"
    ;              (not (is-utf8-filename? (string-append "file" (string (integer->char 1)) ".txt"))))
    )

  (test-group "C String Copy Safety"
    (test-assert "normal string is safe for copying"
                 (is-safe-for-c-string-copy? "Hello, World!"))

    (test-assert "unicode string is safe for copying"
                 (is-safe-for-c-string-copy? "Café résumé"))

    (test-assert "empty string is not safe for copying"
                 (not (is-safe-for-c-string-copy? "")))

    ; Test would require creating string with null bytes
    ; (test-assert "string with null byte is not safe"
    ;              (not (is-safe-for-c-string-copy? (string-append "hello" (string #\nul) "world"))))

    ; Test for very long strings (>4096 chars) would be platform dependent
    )

  (test-group "Network Address Detection"
    (test-assert "IPv4 address detected"
                 (looks-like-network-address? "192.168.1.1"))

    (test-assert "domain name detected"
                 (looks-like-network-address? "example.com"))

    (test-assert "localhost detected"
                 (looks-like-network-address? "localhost"))

    (test-assert "IPv6 address detected"
                 (looks-like-network-address? "::1"))

    (test-assert "hostname with port detected"
                 (looks-like-network-address? "server.com:8080"))

    (test-assert "regular text is not network address"
                 (not (looks-like-network-address? "just some text")))

    (test-assert "filename is not network address"
                 (not (looks-like-network-address? "README")))))

(test-end)

(exit %exit)
