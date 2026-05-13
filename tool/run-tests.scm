;; todo:
;; - unique names for generated tests
;; - --filter flag

(use-modules (ice-9 match)
             (ice-9 format)
             (ice-9 popen)
             (ice-9 regex)
             (srfi srfi-1)
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
  ;; emacs-elisp -- core language
  "test/pre/parse.scm"
  "test/pre/dynamic-binding.scm"
  "test/pre/forwarded-binding.scm"
  "test/pre/condition-case.scm"
  "test/pre/handler-bind.scm"
  "test/pre/bindings.scm"
  "test/pre/complex-binding.scm"
  "test/pre/specpdl-introspection.scm"
  "test/pre/eq.scm"
  "test/pre/arith.scm"
  "test/pre/value-cmp.scm"
  "test/pre/bignum.scm"
  "test/pre/bitwise.scm"
  "test/pre/fixnum.scm"
  "test/pre/float.scm"
  "test/pre/string2.scm"
  "test/pre/reader-integers.scm"
  "test/pre/reader-utf8.scm"
  "test/pre/list.scm"
  "test/pre/predicate-simple.scm"
  "test/pre/predicate-comprehensive.scm"
  "test/pre/stringp.scm"
  "test/pre/string-funs.scm"
  "test/pre/natnump.scm"
  "test/pre/record.scm"
  "test/pre/integer-or-marker-p.scm"
  "test/pre/number-or-marker-p.scm"
  "test/pre/eval.scm"
  "test/pre/fns.scm"
  "test/pre/random.scm"
  "test/pre/time.scm"
  "test/pre/buffer-basic.scm"
  "test/pre/buffer-string.scm"
  "test/pre/clear-string.scm"
  "test/pre/string-match-utf8.scm"
  "test/pre/string-cache-debug.scm"
  "test/pre/string-length-bytes-match.scm"
  "test/pre/ensure-empty-lines-arithmetic.scm"
  "test/pre/string-print-utf8.scm"
  "test/pre/string-char.scm"
  "test/pre/text-property-navigation.scm"
  ;; emacs -- as an editor
  "test/pre/miscvar.scm"
  ;; uncategorized LLM generated tests
  "test/pre/bitwise-comprehensive.scm"
  "test/pre/core-comprehensive.scm"
  "test/pre/float-comprehensive.scm"
  "test/pre/type-predicates.scm"
  )
(group ; keyboard.c → Guile port (see docs/keyboard.org)
  "test/keyboard/ertest-stub.el"            ; M0
  "test/keyboard/ertest-event-modifiers.el" ; M1
  "test/keyboard/ertest-kboard.el"          ; M2
  "test/keyboard/ertest-recent-keys.el"     ; M3
  )
(group
  "test/src/eval-tests.el"
  "test/src/timefns-tests.el"
  "test/src/fns-tests.el"
  "test/src/floatfns-tests.el"
  "test/lisp/sort-tests.el"
  "test/src/data-tests.el"
  )
;; in the following group, all of the test files works with guilemacs
(group
  "test/lisp/ansi-color-tests.el" ;; fails
)(group
  "test/lisp/allout-widgets-tests.el"
  "test/lisp/ansi-osc-tests.el"
)(group
  "test/lisp/auth-source-pass-tests.el" ;; fails
;;;  )(group
  )
(group
  "test/lisp/autoinsert-tests.el"
  )
(group
  "test/lisp/battery-tests.el"
  )
   (group "test/lisp/buff-menu-tests.el") ;; fails
   (group "test/lisp/button-tests.el" ) ;; fails

(group
  "test/lisp/calculator-tests.el"
  "test/lisp/cedet/cedet-files-tests.el"
  "test/lisp/cedet/semantic-utest-c.el"
  "test/lisp/cedet/semantic/bovine/gcc-tests.el"
  )
(group
  "test/lisp/cedet/semantic/fw-tests.el"
  )
(group
  "test/lisp/cedet/srecode/fields-tests.el"
  )
(group
  "test/lisp/completion-tests.el"
  )
   (group "test/lisp/color-tests.el" ) ;; fails
  (group
  "test/lisp/cus-edit-tests.el"
  )
  (group
  "test/lisp/delim-col-tests.el"
  "test/lisp/desktop-tests.el"
  "test/lisp/elide-head-tests.el"
  )
  (group "test/lisp/edmacro-tests.el") ;; fails
  (group
  "test/lisp/emacs-lisp/byte-run-tests.el"
  "test/lisp/emacs-lisp/check-declare-tests.el"
  "test/lisp/emacs-lisp/cl-preloaded-tests.el"
  )
   (group "test/lisp/emacs-lisp/cl-print-tests.el" ) ;; fails
(group
  "test/lisp/emacs-lisp/cl-seq-tests.el"
  "test/lisp/emacs-lisp/copyright-tests.el"
  "test/lisp/emacs-lisp/derived-tests.el"
;;;  "test/lisp/emacs-lisp/easy-mmode-tests.el"
  )
   ; faceup uses syntax for string text-property #("ABC") but guile reader doesn't support  that
   ;(group "test/lisp/emacs-lisp/faceup-tests/faceup-test-files.el") ;; fails
   ;(group "test/lisp/emacs-lisp/faceup-tests/faceup-test-basics.el" ) ; fails
  (group
  "test/lisp/emacs-lisp/float-sup-tests.el"
  ; "test/lisp/emacs-lisp/hierarchy-tests.el" ;; fails, strings are eq in guilemacs, internalized
  )
  (group "test/lisp/emacs-lisp/lisp-mode-tests.el" ) ;; fails
  (group
  "test/lisp/emacs-lisp/icons-tests.el"
  ; "test/lisp/emacs-lisp/lisp-mnt-tests.el" ; fails
  ;"test/lisp/emacs-lisp/memory-report-tests.el" ; fails
  )
(group ;; fails
  "test/lisp/emacs-lisp/pp-tests.el"
;;;  "test/lisp/emacs-lisp/range-tests.el"
  "test/lisp/emacs-lisp/regexp-opt-tests.el"
  "test/lisp/emacs-lisp/ring-tests.el"
  )
(group
  "test/lisp/emacs-lisp/seq-tests.el" ;; pass
  )
(group
  "test/lisp/emacs-lisp/shadow-tests.el" ;; pass
  )
(group
  "test/lisp/emacs-lisp/syntax-tests.el" ;; pass
  "test/lisp/emacs-lisp/tabulated-list-tests.el" ;; fails -- depends on text-properties
 )
  (group "test/lisp/emacs-lisp/text-property-search-tests.el" ) ;; fails
  (group
  "test/lisp/emacs-lisp/thunk-tests.el"
  ;"test/lisp/emacs-lisp/unsafep-tests.el" ;; fail
  )
  (group
  "test/lisp/emacs-lisp/vtable-tests.el"
  )(group
  "test/lisp/faces-tests.el" ;; fails
  )(group
  "test/lisp/env-tests.el"
  ;"test/lisp/find-cmd-tests.el" ; fails
  "test/lisp/font-lock-tests.el" ; fails
  )
(group
  "test/lisp/format-spec-tests.el"
  "test/lisp/hfy-cmap-tests.el"
  "test/lisp/hi-lock-tests.el"
;;;  "test/lisp/htmlfontify-tests.el"
  )
  (group
  "test/lisp/ido-tests.el" ;; fails
  )
  ;(group
  ; "test/lisp/image-file-tests.el" ; fails
  ; )
  (group
  "test/lisp/imenu-tests.el"
  )
  (group
  "test/lisp/info-tests.el"
  )
  ; (group "test/lisp/international/mule-util-tests.el" ) ;; fails
  (group
   "test/lisp/isearch-tests.el" ; fails
   "test/lisp/jit-lock-tests.el" ; fails
   "test/lisp/json-tests.el" ; fails
  )
  (group
   "test/src/json-tests.el"
   )
  (group
  "test/lisp/misc-tests.el" ;; fails
  "test/lisp/lpr-tests.el"
  "test/lisp/md4-tests.el"
  "test/lisp/mwheel-tests.el"
  )
   ;(group "test/lisp/nxml/nxml-mode-tests.el" ) ;; fails
  (group
  ; "test/lisp/nxml/xsd-regexp-tests.el" ; fails
  "test/lisp/paren-tests.el"
  )(group
  "test/lisp/password-cache-tests.el"
  )(group
  "test/lisp/progmodes/asm-mode-tests.el" ;; fails
  )(group
  ;"test/lisp/pcmpl-linux-tests.el"
  "test/lisp/pcomplete-tests.el"
  ; "test/lisp/progmodes/autoconf-tests.el" ; fails
 )
;;; (group
;;;  "test/lisp/progmodes/bat-mode-tests.el"
;;;  "test/lisp/progmodes/bug-reference-tests.el"
;;;  "test/lisp/progmodes/executable-tests.el"
;;;  "test/lisp/progmodes/gdb-mi-tests.el"
;;;  )
;;; (group
;;;  "test/lisp/progmodes/glasses-tests.el"
;;;  "test/lisp/progmodes/opascal-tests.el"
;;;  "test/lisp/progmodes/pascal-tests.el"
;;;  "test/lisp/progmodes/ps-mode-tests.el"
;;;  )
   (group "test/lisp/progmodes/sh-script-tests.el")
  (group
  "test/lisp/progmodes/subword-tests.el"
  )
  (group
  "test/lisp/progmodes/tcl-tests.el"
  "test/lisp/ps-print-tests.el"
  )
;;;(group
;;;  "test/lisp/register-tests.el"
;;;  "test/lisp/rot13-tests.el"
;;;  "test/lisp/scroll-lock-tests.el"
;;;  "test/lisp/ses-tests.el"
;;;  )
;; in the rest of the groups, most test file has some test that
;; had to be disabled to work with guilemacs, they are counted as
;; false positives. So if you count total passed tests,
;; they need to be subtracted.
(group
  ;; these doesn't want to play with others
   "test/lisp/emacs-lisp/find-func-tests.el" ; doesn't like test/lisp/emacs-lisp/checkdoc-tests.el fails
;  "test/lisp/help-mode-tests.el" ; fails
   "test/lisp/help-fns-tests.el" ; fails
  )
(group
  "test/lisp/dired-tests.el"
  "test/lisp/progmodes/compile-tests.el"
;;;  "test/lisp/progmodes/js-tests.el"
  "test/lisp/simple-tests.el"
  )
(group ;; hangs
  "test/lisp/emacs-lisp/pcase-tests.el"
;;;  "test/lisp/emacs-lisp/package-tests.el"
  "test/lisp/replace-tests.el"
;;;  "test/lisp/international/mule-tests.el"
  )
;;;(group
;;; "test/lisp/mouse-tests.el"
  ; "test/lisp/auth-source-tests.el" ; fails
;;;  "test/lisp/dabbrev-tests.el"
;;;  "test/lisp/emacs-lisp/macroexp-tests.el"
;;;  )
(group
  "test/lisp/ls-lisp-tests.el"
  ; "test/lisp/loadhist-tests.el" ; fails
  )
(group
  ;"test/lisp/abbrev-tests.el" ;; hangs (or group)
   "test/lisp/emacs-lisp/let-alist-tests.el" ; fails
  )
(group
  "test/lisp/info-xref-tests.el"
;;;  "test/lisp/image-tests.el"
;;;  "test/lisp/ibuffer-tests.el"
  "test/lisp/hl-line-tests.el"
  )
(group
  "test/lisp/help-tests.el"
;;;  "test/lisp/obarray-tests.el" ;; pass
  "test/lisp/emacs-lisp/gv-tests.el"
  "test/lisp/files-tests.el"
  )
  (group "test/lisp/ffap-tests.el" ) ;; multibyte bug ; fails
  (group
  "test/lisp/progmodes/f90-tests.el" ;; crashes
  )(group
  "test/lisp/progmodes/elisp-mode-tests.el"
  )
(group "test/lisp/emacs-lisp/ert-x-tests.el" )
(group
  "test/lisp/emacs-lisp/ert-tests.el"
  )
(group
  "test/lisp/progmodes/flymake-tests.el"
  )
(group
  "test/lisp/emacs-lisp/lisp-tests.el"
  "test/lisp/emacs-lisp/subr-x-tests.el"
  "test/lisp/emacs-lisp/timer-tests.el"
  "test/lisp/emacs-lisp/warnings-tests.el"
;;;  "test/lisp/emacs-lisp/cl-generic-tests.el"
  )
 (group ; segfaults
   "test/lisp/emacs-lisp/cl-lib-tests.el"
   "test/lisp/emacs-lisp/cl-macs-tests.el"
   "test/lisp/emacs-lisp/comp-cstr-tests.el"
;;;   "test/lisp/emacs-lisp/ert-font-lock-tests.el"
   )
 (group
   "test/lisp/emacs-lisp/map-tests.el"
;;;   "test/lisp/emacs-lisp/rmc-tests.el"
   "test/lisp/emacs-lisp/rx-tests.el"
   "test/lisp/emacs-lisp/backquote-tests.el"
   )
 (group
;;;   "test/lisp/emacs-lisp/benchmark-tests.el"
   "test/lisp/emacs-lisp/bindat-tests.el"
;;;   "test/lisp/emacs-lisp/cconv-tests.el"
   "test/lisp/emacs-lisp/cl-extra-tests.el"
  )
(group
  "test/lisp/emacs-lisp/checkdoc-tests.el" ; run this not with test/lisp/emacs-lisp/find-func-tests.el

  "test/lisp/saveplace-tests.el"
  "test/lisp/shell-tests.el"
  "test/lisp/international/ccl-tests.el"
  )
(group
  "test/lisp/minibuffer-tests.el"
;;;  "test/lisp/align-tests.el"
  "test/lisp/allout-tests.el"
  "test/lisp/arc-mode-tests.el"
  "test/lisp/descr-text-tests.el"
  )
(group
;;;  "test/lisp/bookmark-tests.el"
;;;  "test/lisp/completion-preview-tests.el"
;;;  "test/lisp/custom-tests.el"
  )
  (group
;;;  "test/lisp/dired-aux-tests.el"
  "test/lisp/dired-x-tests.el"
;;;  "test/lisp/dnd-tests.el"
  "test/lisp/dom-tests.el"
  )
;;;  (group
;;;  "test/lisp/progmodes/cperl-mode-tests.el"
;;;  "test/lisp/progmodes/csharp-mode-tests.el"
;;;  "test/lisp/progmodes/project-tests.el"
;;;  )
 (group
  "test/lisp/progmodes/ruby-mode-tests.el"
  )
;;;(group
;;;  "test/lisp/progmodes/scheme-tests.el"
;;;  )
   (group "test/lisp/progmodes/sql-tests.el") ; fails

 ))

(define %emacs-exec "../src/temacs")

;; keep track manually of which tests are expensive or unstable
(define %skipped-tests '(
 "cperl-test-bug-10483" "info-xref-test-emacs-manuals" "package-test-update-archives-async" "password-cache-tests-add/expires-key" "test-htmlfontify-load-rgb-file" "cl-seq-test-bug24264" "srecode-field-utest-impl" "semantic-test-c-preprocessor-simulation"
 "dnd-tests-open-remote-url"))

(define %read-failures 0)
(define %total-passed-tests 0)
(define %total-failed-tests 0)
(define %total-gen-tests '())
(define %total-ert-tests '())
(define %total-found-gen-tests '())
(define %total-found-ert-tests '())
(define %total-failed-gen-tests '())
(define %total-failed-ert-tests '())
(define %total-passed-gen-tests '())
(define %total-passed-ert-tests '())

(define (elfmt-walk form)
  (cond
   ((and (pair? form) (eq? 'raw (car form)))
    (format #f "~a" (cadr form)))
   ((pair? form)
    (cons (elfmt-walk (car form)) (elfmt-walk (cdr form))))
   ((string? form)
    (format #f "~s" form))
   (else
    form)))

(define (elfmt form)
  (display (elfmt-walk form)
           (current-output-port))
  (newline (current-output-port)))

(define (el-expr form)
  (format (current-output-port) "~a" form))

(define (el-str str)
  (format #f "~a" str))

(define-syntax deftest
  (lambda (x)
    (syntax-case x ()
      ((_ name (expect) . body)
       #'(emit-test 'name #f 'expect (lambda () . body))))))

(define-syntax deftestf
  (lambda (x)
    (syntax-case x ()
      ((_ name (expect) . body)
       #'(emit-test name #f expect (lambda () . body)))
      ((_ name (type expect) . body)
       #'(emit-test name 'type expect (lambda () . body))))))

(define %testnum 0)

(define (emit-test name type expect thunk)
  ;; ensure name is unique
  (let* ((name (format #f "~a" name))
         (name (if (member name %total-gen-tests)
                   (let ((num (1+ %testnum)))
                     (set! %testnum num)
                     (string-concatenate (list name (format #f "-~a" num))))
                   name)))
    (push! %total-gen-tests name)
    (format (current-output-port) "(princ \"\\n-- test begin: ~a\\n\")~%" name)
    (format (current-output-port) "(princ \"\\n-- test expect: ~a\\n\")~%"
            (cond
             ((eq? type 'text) (format #f "~a" expect))
             ((string? expect) (format #f "\\\"~a\\\"" expect))
             (else expect)))
    (thunk)
    (format (current-output-port) "(princ \"\\n-- test end: ~a\\n\")~%" name)
    (format (current-output-port) "(flush-standard-output)~%")))

;; use the scheme-parser to read through the elisp-file
;; and search for deftest forms.
(define (scan-testfile filename)
  (let* ((failure #f)
         (r (lambda (port)
              (with-exception-handler
                  (lambda (exn)
                    (apply (lambda args
                             (format (current-error-port) "SCAN ERROR: filename: ~s, error: ~s~%" filename args)
                             (set! failure #t)
                             (set! %read-failures (1+ %read-failures))
                             #f)
                           (exception-kind exn)
                           (exception-args exn)))
                (lambda () (read port))
                #:unwind? #t
                #:unwind-for-type #t))))
    (call-with-input-file filename
      (lambda (port)
        (do ((form (r port) (r port)))
            ((eof-object? form))
          (if (and (pair? form) (eq? 'ert-deftest (car form)))
              (if (and (pair? (cdr form)) (symbol? (cadr form)))
                  (set! %total-ert-tests (assoc-set! %total-ert-tests
                                                     (symbol->string (cadr form))
                                                     '())))))))
    (when failure
      (format #t "Need to rescan file ~s.~%" filename)
      (call-with-input-file filename
        (lambda (port)
          (do ((line (get-line port) (get-line port)))
              ((eof-object? line))
            (cond
             ;; dont account skipped tests
             ((string-contains line "'(SIGSEGV-guilemacs") #f)
             ((string-contains line "'(DISABLE-guilemacs") #f)
             ((string-contains line "'(ert-deftest") #f)
             ((= 0 (or (string-contains line ";") -1)) #f)
             (else
              (let ((n (string-contains line "ert-deftest")))
                (when n
                  (let* ((name (substring line (+ 1 n (string-length "ert-deftest"))))
                         (name (substring name 0 (string-contains name " "))))
                    (if (and (not (string-contains name ",")) ; emit deftest through macro
                             (not (string-contains name ",(intern")) ; ditto
                             (not (string=? name "")))
                        (set! %total-ert-tests (assoc-set! %total-ert-tests name '()))))))))))))))

;; take a test-specification in scheme and generate an elisp test file
(define (testcompile-file file)
  (let ((elfile (substring (substring file 0 (- (string-length file) 4)) 5)))
    (with-output-to-file (string-concatenate (list elfile ".el"))
      (lambda ()
        (primitive-load (substring file 5)))
      #:encoding "UTF-8")
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
             (scan-testfile s)
             (substring s 0 (- (string-length s) 3))))))
       files))

(define (run-tests-bare-emacs files keys)
  (let* ((files (randomize-list (testcompile-files files)))
         (args (append
                `(,%emacs-exec "-nl" "-Q" "--batch")
                (list
                 (string-concatenate
                  (apply append (map (lambda (file)
                                       (list "--prelude " (getcwd) "/" file " "))
                                     files))))
                '(" 2>&1"))))
    (format #t "Running prelude test files: ~a~%" files)
    (format #t "running ===> ~a~%" args)
    (let* ((port (open-input-pipe (string-join args " ")))
           (found '()) (pass '()) (fail '())
           (curname #f)
           (prevres #f)
           (expected #f)
           (curstr ""))
      (let loop ((line (get-line port)))
        (cond
         ((eof-object? line) #f)
         (else
          (cond
           ((equal? 0 (string-contains line "loading ")) #f) ; load messages
           ((equal? 0 (string-contains line ";;; ")) #f) ; guile notes and warnings
           ((equal? 0 (string-contains line ";; ")) #f) ; guile notes and warnings
           ((string-contains line "Symbol's elisp-function definition is void") #f)
           ((and (string-contains line "Loading ")
                 (string-contains line "(source)"))
            #f)
           ((string-contains line "-- test begin: ") =>
            (lambda (idx)
              ;; catch if a test-protocol didn't report TEST-END
              (if (and curname (not prevres))
                (push! fail curname))
              (let ((name (substring line (+ idx (string-length "-- test begin: ")))))
                (set! prevres #f)
                (set! curname name)
                (push! found name)
                (format #t "TEST-BEGIN: name [~s]~%" name))))
           ((string-contains line "-- test end: ") =>
            (lambda (idx)
              (let ((name (substring line (+ idx (string-length "-- test end: ")))))
                (format #t "TEST-END: name [~s]~%" name))
              (cond
               ((equal? expected curstr)
                (format #t "    Ok ~s.~%" curname)
                (push! pass curname)
                (set! prevres #t))
               (else
                (format #t "    FAIL!~%")
                (format #t "    EXPECTED: ~s~%" expected)
                (format #t "    GOT: ~s~%" curstr)
                (set! prevres #t) ;; avoid reporting failure again after loop-end
                (push! fail curname)))
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
            (format #t "~a:~a [~a] >>> ~a~%"
                    (+ %total-passed-tests (length pass))
                    (+ %total-failed-tests (length fail))
                    curname line)))
          (loop (get-line port)))))
      (if (and curname (not prevres))
          (push! fail curname))
      (list found pass fail))))

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
           (pass '())
           (tot 0)
           ;; match: ^   passed  1/1  allout-test-range-overlaps (0.000 sec)$
           (re (make-regexp ".* passed[ ]*([0-9]*)/[0-9]*[ ]*([^ ]*) .*")))
      (let loop ((line (get-line port)))
        (cond
         ((eof-object? line) #f)
         (else
          (format #t "~a:~a >>> ~a~%" (+ (length pass) %total-passed-tests)
                  %total-failed-tests line)
          (cond
           ((string-contains line " passed ")
            (let ((f (list-matches re line)))
              (unless (null? f)
                (let* ((pos-cnt (vector-ref (car f) 2))
                       (pos-name (vector-ref (car f) 3))
                       (pass-count (substring line (car pos-cnt) (cdr pos-cnt)))
                       (test-name (substring line (car pos-name) (cdr pos-name))))
                  (push! pass test-name)
                  (set! tot (string->number pass-count)))))
            (loop (get-line port)))
           (else (loop (get-line port)))))))
      (if (not (= (length pass) tot)) ; assert test protocol
          (format #t "ERROR: ~a passed, but ~a counted pass.~%" (length pass) tot))
      (list pass pass '()))))

(define (run-tests files keys)
  (flush-all-ports)
  (match (cond
          ((memq 'prelude keys)
           (match (run-tests-bare-emacs files keys)
             ((found pass fail)
              (push-append! %total-found-gen-tests found)
              (push-append! %total-passed-gen-tests pass)
              (push-append! %total-failed-gen-tests fail)
              (list found pass fail))))
          (else
           (match (run-tests-loadup-emacs files keys)
             ((found pass fail)
              (push-append! %total-found-ert-tests found)
              (push-append! %total-passed-ert-tests pass)
              (push-append! %total-failed-ert-tests fail)
              (list found pass fail)))))
    ((found pass fail)
     (set! %total-failed-tests (+ (length fail) %total-failed-tests))
     (format #t "tests result in group: ~a found tests (atleast), ~a passed, ~a failed~%"
                (length found) (length pass) (length fail))
     (if (not (null? fail))
         (format #t "  failed tests: ~s~%" fail)))))

(define (maybe-run-tests files keys test-filter)
  (when (or (null? (memq 'prelude keys))
            ;; check prelude
            (if (memq 'prelude test-filter)
                (memq 'prelude keys)
                #t))
    ;; check filter
    (let ((filters (filter string? test-filter)))
      (if (not (null? filters))
          (set! files
                (filter (lambda (file)
                          (fold (lambda (a m)
                                  (or m
                                      (string-contains file a)))
                                #f
                                filters))
                        files)))
      (if (not (null? files))
          (run-tests files keys)))))

(define (main args)
  (let ((test-filter '()))
    (for-each (lambda (arg)
                (if (string=? "--prelude" arg)
                    (push! test-filter 'prelude))
                (if (string-contains arg "--filter=")
                    (push! test-filter (substring arg 9))))
              args)
    (set! *random-state* (random-state-from-platform))
    ;; test
    (let* ((files '())
           (done #f))
      (for-each (lambda (line)
                  (when (not done)
                    (cond
                     ((eq? 'done line) (set! done #t))
                     ((and (pair? line)
                           (eq? 'quote (car line)))
                      #f)
                     ((and (pair? line)
                           (eq? 'group (car line)))
                      (let ((keys (if (and (pair? (cdr line)) (pair? (cadr line)))
                                      (cadr line)
                                      '())))
                        (if (not (null? keys)) ; skip the keys
                            (set! line (cdr line)))
                        ;; run any currently collected files
                        (unless (null? files)
                          (maybe-run-tests files '() test-filter))
                        ;; run the files in the group
                        (maybe-run-tests (cdr line) keys test-filter)
                        (set! files '())))
                     (else
                      (push! files line)))))
                %tests)
      (unless (null? files)
        (maybe-run-tests files '() test-filter)))
    (flush-all-ports)
    ;; report
    (format #t "~%#################################################################~%")
    (format #t "# * ERT test -- a test that comes from the Emacs Regression Test framework.~%")
    (format #t "#   These test files are scanned and counted before being run~%")
    (format #t "#   (because running the target may abort and not report totals).~%")
    (format #t "# * gen test -- a simple test protocol, where Scheme is used to generated test cases in elisp-files, these are counted during emit.~%")
    (format #t "# * found -- a test that is either emitted during test generation, or found when search the ERT suite~%")
    (format #t "# * passed -- a test that explicitly reports success~%")
    (format #t "# * failed -- a test that explicitly reports a failure mode~%")
    (format #t "# * missing -- a test that was found during search, but has not reported its result, the test has either aborted during run,~%")
    (format #t "#   or hasn't been runned, both cases are counted as a failed test (ie, not a controlled skip).~%")
    (format #t "# * found: known tests found during emit or search~%")
    (let* ((num-total-gen-tests (length %total-gen-tests))
           (num-total-ert-tests (length %total-ert-tests))
           (num-total-found-gen-tests (length %total-found-gen-tests))
           (num-total-found-ert-tests (length %total-found-ert-tests))
           (num-total-passed-gen-tests (length %total-passed-gen-tests))
           (num-total-passed-ert-tests (length %total-passed-ert-tests))
           (num-total-failed-gen-tests (length %total-failed-gen-tests))
           (num-total-missing-ert-tests ; (length %total-failed-ert-tests)
                    (- num-total-ert-tests num-total-passed-ert-tests))
           (failed-gen (filter (lambda (x)
                                 (not (member x %total-passed-gen-tests)))
                               %total-gen-tests))
           (failed-ert (filter (lambda (x)
                                 (and (not (member (car x) %total-passed-ert-tests))
                                      (not (member (car x) %skipped-tests))))
                               %total-ert-tests))
           (num-total-failed-ert-tests (length failed-ert)))
      (format #t "~%")
      (if (not (null? %total-failed-gen-tests))
          (format #t "~%~%* failed generated tests ~s~%" %total-failed-gen-tests))
      (if (not (null? %total-failed-ert-tests))
          (format #t "* failed ERT tests ~s~%" %total-failed-ert-tests))
      (if (not (null? failed-gen))
          (format #t "~%failed gen tests: ~s~%~%" failed-gen))
      (if (not (null? failed-ert))
          (format #t "failed ERT tests: ~s~%~%" failed-ert))
      (format #t "Read failures when reading ERT test files: ~s~%" %read-failures)
      (format #t "Total number of missing tests: ~a   ;; found during emit/scan, but never runned, ie most probably failed~%"
              (length failed-ert))
      (format #t "--------------------------------------------~%")
      (print-report-table
       (list '("" "gen" "ERT" "total" "")
             (list "found"
                   num-total-gen-tests
                   num-total-ert-tests
                   (+ num-total-gen-tests num-total-ert-tests)
                   ; #f
                   )
             (list "runned"
                   num-total-found-gen-tests
                   num-total-found-ert-tests
                   (+ num-total-found-gen-tests num-total-found-ert-tests)
                   ; #f
                   )
             (list "pass"
                   num-total-passed-gen-tests
                   num-total-passed-ert-tests
                   (+ num-total-passed-gen-tests num-total-passed-ert-tests)
                   ; %total-passed-tests
                   )
             (list "fail"
                   num-total-failed-gen-tests
                   num-total-failed-ert-tests
                   (+ num-total-failed-gen-tests num-total-failed-ert-tests)
                   ; %total-failed-tests
                   )))
      (exit (if (> (+ num-total-failed-gen-tests num-total-failed-ert-tests) 0)
                1 0)))))
