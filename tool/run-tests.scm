(use-modules (ice-9 match)
             (ice-9 format)
             (ice-9 popen)
             (ice-9 regex)
             (rnrs io ports)
             (utils))
; accumulate all testfiles and run them in a single guile-emacs program
;
; by stating the word RUN on a single line, all
; accumulated test files so far will be run,
; this is useful if tests needs to be run isolated
;
; if you are debugging and need to quit early, state DONE
; on a single line
;
; try to sort the test from most primordial elisp functionallity
; towards more complex elisp applications

(define %tests '(
(group (prelude)
  "test/pre/value-cmp.scm"
  "test/pre/bignum.scm")
(group
; "test/src/timefns-tests.el"
  "test/src/fns-tests.el"
  "test/src/floatfns-tests.el"
  )
;; in the following group, all of the test files works with guilemacs
(group
  "test/lisp/allout-widgets-tests.el"
  "test/lisp/ansi-color-tests.el"
  "test/lisp/ansi-osc-tests.el"
  "test/lisp/auth-source-pass-tests.el"
  "test/lisp/autoinsert-tests.el"
  "test/lisp/battery-tests.el"
  "test/lisp/buff-menu-tests.el"
  "test/lisp/button-tests.el"
  "test/lisp/calculator-tests.el"
  "test/lisp/cedet/cedet-files-tests.el"
  "test/lisp/cedet/semantic-utest-c.el"
  "test/lisp/cedet/semantic/bovine/gcc-tests.el"
  "test/lisp/cedet/semantic/fw-tests.el"
  "test/lisp/cedet/srecode/fields-tests.el"
  "test/lisp/color-tests.el"
  "test/lisp/completion-tests.el"
  "test/lisp/cus-edit-tests.el"
  "test/lisp/delim-col-tests.el"
  "test/lisp/desktop-tests.el"
  ;
  "test/lisp/edmacro-tests.el"
  ;
  ;"test/lisp/elide-head-tests.el"
  ;
  "test/lisp/emacs-lisp/byte-run-tests.el"
  "test/lisp/emacs-lisp/check-declare-tests.el"
  "test/lisp/emacs-lisp/cl-preloaded-tests.el"
  "test/lisp/emacs-lisp/cl-print-tests.el"
  "test/lisp/emacs-lisp/cl-seq-tests.el"
  "test/lisp/emacs-lisp/copyright-tests.el"
  "test/lisp/emacs-lisp/derived-tests.el"
  "test/lisp/emacs-lisp/easy-mmode-tests.el"
  "test/lisp/emacs-lisp/faceup-tests/faceup-test-basics.el"
  "test/lisp/emacs-lisp/faceup-tests/faceup-test-files.el"
  "test/lisp/emacs-lisp/float-sup-tests.el"
  "test/lisp/emacs-lisp/hierarchy-tests.el"
  "test/lisp/emacs-lisp/icons-tests.el"
  "test/lisp/emacs-lisp/lisp-mnt-tests.el"
  "test/lisp/emacs-lisp/lisp-mode-tests.el"
  "test/lisp/emacs-lisp/memory-report-tests.el"
  "test/lisp/emacs-lisp/pp-tests.el"
  "test/lisp/emacs-lisp/range-tests.el"
  "test/lisp/emacs-lisp/regexp-opt-tests.el"
  "test/lisp/emacs-lisp/ring-tests.el"
  "test/lisp/emacs-lisp/seq-tests.el"
  "test/lisp/emacs-lisp/shadow-tests.el"
  "test/lisp/emacs-lisp/syntax-tests.el"
  "test/lisp/emacs-lisp/tabulated-list-tests.el"
  "test/lisp/emacs-lisp/text-property-search-tests.el"
  "test/lisp/emacs-lisp/thunk-tests.el"
  "test/lisp/emacs-lisp/unsafep-tests.el"
  "test/lisp/emacs-lisp/vtable-tests.el"
  "test/lisp/env-tests.el"
  "test/lisp/faces-tests.el"
  "test/lisp/find-cmd-tests.el"
  "test/lisp/font-lock-tests.el"
  "test/lisp/format-spec-tests.el"
  "test/lisp/hfy-cmap-tests.el"
  "test/lisp/hi-lock-tests.el"
  "test/lisp/htmlfontify-tests.el"
  "test/lisp/ido-tests.el"
  "test/lisp/image-file-tests.el"
  "test/lisp/imenu-tests.el"
  "test/lisp/info-tests.el"
  "test/lisp/international/mule-util-tests.el"
  "test/lisp/isearch-tests.el"
  "test/lisp/jit-lock-tests.el"
  "test/lisp/json-tests.el"
  "test/lisp/lpr-tests.el"
  "test/lisp/md4-tests.el"
  "test/lisp/misc-tests.el"
  "test/lisp/mwheel-tests.el"
  "test/lisp/nxml/nxml-mode-tests.el"
  "test/lisp/nxml/xsd-regexp-tests.el"
  "test/lisp/paren-tests.el"
  "test/lisp/password-cache-tests.el"
  "test/lisp/pcmpl-linux-tests.el"
  "test/lisp/pcomplete-tests.el"
  "test/lisp/progmodes/asm-mode-tests.el"
  "test/lisp/progmodes/autoconf-tests.el"
  "test/lisp/progmodes/bat-mode-tests.el"
  "test/lisp/progmodes/bug-reference-tests.el"
  "test/lisp/progmodes/executable-tests.el"
  "test/lisp/progmodes/gdb-mi-tests.el"
  "test/lisp/progmodes/glasses-tests.el"
  "test/lisp/progmodes/opascal-tests.el"
  "test/lisp/progmodes/pascal-tests.el"
  "test/lisp/progmodes/ps-mode-tests.el"
  "test/lisp/progmodes/sh-script-tests.el"
  "test/lisp/progmodes/subword-tests.el"
  "test/lisp/progmodes/tcl-tests.el"
  "test/lisp/ps-print-tests.el"
  "test/lisp/register-tests.el"
  "test/lisp/rot13-tests.el"
  "test/lisp/scroll-lock-tests.el"
  "test/lisp/ses-tests.el"
  )
;; in the rest of the groups, most test file has some test that
;; had to be disabled to work with guilemacs, they are counted as
;; false positives. So if you count total passed tests,
;; they need to be subtracted.
(group
  ;; these doesn't want to play with others
  "test/lisp/emacs-lisp/find-func-tests.el" ; doesn't like test/lisp/emacs-lisp/checkdoc-tests.el
  "test/lisp/help-mode-tests.el"
  "test/lisp/help-fns-tests.el"
  )
(group
  "test/lisp/dired-tests.el"
  "test/lisp/progmodes/compile-tests.el"
  "test/lisp/progmodes/js-tests.el"
  "test/lisp/simple-tests.el"
  "test/lisp/emacs-lisp/pcase-tests.el"
  "test/lisp/emacs-lisp/package-tests.el"
  "test/lisp/replace-tests.el"
  "test/lisp/international/mule-tests.el"
  "test/lisp/mouse-tests.el"
  "test/lisp/auth-source-tests.el"
  "test/lisp/dabbrev-tests.el"
  "test/lisp/emacs-lisp/macroexp-tests.el"
  "test/lisp/ls-lisp-tests.el"
  "test/lisp/loadhist-tests.el"
  "test/lisp/abbrev-tests.el"
  "test/lisp/emacs-lisp/let-alist-tests.el"
  "test/lisp/info-xref-tests.el"
  "test/lisp/image-tests.el"
  "test/lisp/ibuffer-tests.el"
  "test/lisp/hl-line-tests.el"
  "test/lisp/help-tests.el"
  "test/lisp/obarray-tests.el"
  "test/lisp/emacs-lisp/gv-tests.el"
  "test/lisp/files-tests.el"
  "test/lisp/ffap-tests.el"
  "test/lisp/progmodes/f90-tests.el"
  "test/lisp/progmodes/elisp-mode-tests.el"
  "test/lisp/emacs-lisp/ert-x-tests.el"
  )
(group
  "test/lisp/emacs-lisp/ert-tests.el"
  "test/lisp/progmodes/flymake-tests.el"
  )
(group
  "test/lisp/emacs-lisp/lisp-tests.el"
  "test/lisp/emacs-lisp/subr-x-tests.el"
  "test/lisp/emacs-lisp/timer-tests.el"
  "test/lisp/emacs-lisp/warnings-tests.el"
  "test/lisp/emacs-lisp/cl-generic-tests.el"
  "test/lisp/emacs-lisp/cl-lib-tests.el"
  "test/lisp/emacs-lisp/cl-macs-tests.el"
  "test/lisp/emacs-lisp/comp-cstr-tests.el"
  "test/lisp/emacs-lisp/ert-font-lock-tests.el"
  "test/lisp/emacs-lisp/map-tests.el"
  "test/lisp/emacs-lisp/rmc-tests.el"
  "test/lisp/emacs-lisp/rx-tests.el"
  "test/lisp/emacs-lisp/backquote-tests.el"
  "test/lisp/emacs-lisp/benchmark-tests.el"
  "test/lisp/emacs-lisp/bindat-tests.el"
  "test/lisp/emacs-lisp/cconv-tests.el"
  "test/lisp/emacs-lisp/cl-extra-tests.el"
  "test/lisp/emacs-lisp/checkdoc-tests.el" ; run this not with test/lisp/emacs-lisp/find-func-tests.el

  "test/lisp/saveplace-tests.el"
  "test/lisp/shell-tests.el"
  "test/lisp/international/ccl-tests.el"
  "test/lisp/minibuffer-tests.el"
  "test/lisp/align-tests.el"
  "test/lisp/allout-tests.el"
  "test/lisp/arc-mode-tests.el"
  "test/lisp/bookmark-tests.el"
  "test/lisp/completion-preview-tests.el"
  "test/lisp/custom-tests.el"
  "test/lisp/descr-text-tests.el"
  "test/lisp/dired-aux-tests.el"
  "test/lisp/dired-x-tests.el"
  "test/lisp/dnd-tests.el"
  "test/lisp/dom-tests.el"

  "test/lisp/progmodes/cperl-mode-tests.el"
  "test/lisp/progmodes/csharp-mode-tests.el"
  "test/lisp/progmodes/project-tests.el"
  "test/lisp/progmodes/ruby-mode-tests.el"
  "test/lisp/progmodes/scheme-tests.el"
  "test/lisp/progmodes/sql-tests.el"
  )
 ))

(define %total-defined-tests 0)
(define %total-runned-tests 0)
(define %total-failed-tests '())
(define %total-passed-tests 0)

(define-syntax el-expr
  (syntax-rules ()
    ((_ expr)
     (begin
       (format (current-output-port) "~s~%" expr)))))

(define-syntax deftest
  (lambda (x)
    (syntax-case x ()
      ((_ name (expect) . body)
       #'(begin
           (set! %total-defined-tests (1+ %total-defined-tests))
           (format (current-output-port) "(princ \"\\n-- test begin: ~s\\n\")~%" 'name)
           (format (current-output-port) "(princ \"\\n-- test expect: ~s\\n\")~%" 'expect)
           (begin . body)
           (format (current-output-port) "(princ \"\\n-- test end: ~s\\n\")~%" 'name))))))

;; take a test-specification in scheme and generate an elisp test file
(define (testcompile-file file)
  (let ((elfile (substring (substring file 0 (- (string-length file) 4)) 5)))
    (with-output-to-file (string-concatenate (list elfile ".el"))
      (lambda ()
        (primitive-load (substring file 5))))
    elfile))

(define (testcompile-files files)
  (map (lambda (file)
         (cond
          ;; scheme file, first compile it
          ((= (- (string-length file) 4) (or (string-contains file ".scm") 0))
           (testcompile-file file))
          ;; raw elisp file, feed it to test target (emacs)
          (else
           ;; remove "/test" prefix and ".el" suffix
           (let ((s (substring file 5)))
             (substring s 0 (- (string-length s) 3))))))
       files))

(define (run-tests-bare-emacs files keys)
  (let* ((files (randomize-list (testcompile-files files)))
         (args (append
                '("../src/emacs" "-nl" "-Q" "--batch")
                (list
                 (string-concatenate
                  (apply append (map (lambda (file)
                                       (list "--prelude " (getcwd) "/" file " "))
                                     files))))
                '(" 2>&1"))))
    (format #t "Running prelude test files: ~a~%" files)
    (format #t "running ===> ~a~%" args)
    (let* ((port (open-input-pipe (string-join args " ")))
           (tot 0) (pass 0) (fail '())
           (curname #f)
           (prevres #f)
           (expected #f)
           (curstr ""))
      (let loop ((line (get-line port)))
        (cond
         ((eof-object? line) #f)
         (else
          (cond
           ((string-contains line "-- test begin: ") =>
            (lambda (idx)
              ;; catch if a test-protocol didn't report TEST-END
              (if (and curname (not prevres))
                (set! fail (cons curname fail)))
              (let ((name (substring line (+ idx (string-length "-- test begin: ")))))
                (set! prevres #f)
                (set! curname name)
                (set! tot (1+ tot))
                (format #t "TEST-BEGIN: name [~s]~%" name))))
           ((string-contains line "-- test end: ") =>
            (lambda (idx)
              (let ((name (substring line (+ idx (string-length "-- test end: ")))))
                (format #t "TEST-END: name [~s]~%" name))
              (cond
               ((equal? expected curstr)
                (format #t "    Ok.~%")
                (set! pass (1+ pass))
                (set! prevres #t))
               (else
                (format #t "    FAIL!~%")
                (set! prevres #t) ;; avoid reporting failure again after loop-end
                (set! fail (cons curname fail))))
              (set! expected #f)
              (set! curstr "")))
           ((string-contains line "-- test expect: ") =>
            (lambda (idx)
              (let ((val (substring line (+ idx (string-length "-- test expect: ")))))
                (set! expected val)
                (format #t "  TEST-EXPECT: val [~s]~%" val))))
           (else
            (if curname
                (set! curstr (string-concatenate (list curstr line))))
            (format #t "~a/~a/~a [~a] >>> ~a~%"
                    %total-runned-tests (+ pass %total-passed-tests)
                    (+ (length fail) (length %total-failed-tests))
                    curname line)))
          (loop (get-line port)))))
      (if (and curname (not prevres))
          (set! fail (cons curname fail)))
      (list tot pass fail))))

(define (run-tests-loadup-emacs files keys)
  (let* ((files (randomize-list (testcompile-files files)))
         (args (append
                '("../src/emacs" "--no-init-file" "--no-site-file" "--no-site-lisp" "-L" ":." "-l" "ert")
                (apply append (map (lambda (file)
                                     (list "-l" file))
                                   files))
                '("--batch" "--eval" "'(ert-run-tests-batch-and-exit (quote (not (or (tag :expensive-test) (tag :unstable) (tag :nativecomp)))))' 2>&1"))))
    (format #t "Running test files: ~a~%" files)
    (format #t "running ===> ~a~%" args)
    (let* ((port (open-input-pipe (string-join args " ")))
           (tot 0)
           (re (make-regexp ".* passed[ ]*([0-9]*)/.*")))
      (let loop ((line (get-line port)))
        (cond
         ((eof-object? line) #f)
         (else
          (format #t "~a >>> ~a~%" (+ tot %total-passed-tests) line)
          (cond
           ((string-contains line " passed ")
            (let ((f (list-matches re line)))
              (unless (null? f)
                (let ((pos (vector-ref (car f) 2)))
                  (let ((str (substring line (car pos) (cdr pos))))
                    (set! tot (string->number str))))))
            (loop (get-line port)))
           (else (loop (get-line port)))))))
      (list tot tot '()))))

(define (run-tests files keys)
  (match ((if (memq 'prelude keys)
              run-tests-bare-emacs
              run-tests-loadup-emacs)
          files keys)
    ((tot pass fail)
     (set! %total-runned-tests (+ %total-runned-tests tot))
     (set! %total-passed-tests (+ %total-passed-tests pass))
     (set! %total-failed-tests (append %total-failed-tests fail))
     (format #t "tests result over files: ~a runned, ~a passed, ~a failed~%" tot pass (length fail))
     (if (not (null? fail))
         (format #t "  failed tests: ~s~%" fail)))))

(define (match-keys keys fils)
  ;; check prelude
  (let ((pass #t))
    (if (memq 'prelude fils)
        (if (not (memq 'prelude keys))
            (set! pass #f)))
    pass))

(define (main args)
  (let ((test-filter '()))
    (for-each (lambda (arg)
                (if (string=? "--prelude" arg)
                    (set! test-filter (cons 'prelude test-filter))))
              args)
    (set! *random-state* (random-state-from-platform))
    (let ((files '())
          (done #f))
      (for-each (lambda (line)
                  (when (and (not done)
                             (not (equal? "" line)))
                    (cond
                     ((eq? 'done line) (set! done #t))
                     ((and (pair? line)
                           (eq? 'group (car line)))
                      (let ((keys (if (and (pair? (cdr line)) (pair? (cadr line)))
                                      (cadr line)
                                      '())))
                        (if (not (null? keys)) ; skip the keys
                            (set! line (cdr line)))
                        ;; run any currently collected files
                        (unless (null? files)
                          (run-tests files '()))
                        ;; run the files in the group
                        (if (match-keys keys test-filter)
                            (run-tests (cdr line) keys))
                        (set! files '())))
                     (else
                      (set! files (cons line files))))))
                %tests)
      (unless (null? files)
        (run-tests files '()))
      (if (not (null? %total-failed-tests))
          (format #t "~%~%failed tests ~s~%" %total-failed-tests))
      (format #t "total number of defined tests: ~a~%" %total-defined-tests)
      (format #t "total number of runned tests: ~a~%" %total-runned-tests)
      (format #t "total number of passed tests: ~a~%" %total-passed-tests)
      (format #t "total number of failed tests: ~a~%" (length %total-failed-tests))
      (exit))))
