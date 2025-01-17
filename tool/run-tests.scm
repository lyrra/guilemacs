(use-modules (ice-9 popen)
             (ice-9 rdelim)
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

; these doesn't want to play with others
(define %tests '(
(group
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


(define (run-tests files)
  (let* ((files (map (lambda (file)
                       (let ((s (substring file 5)))
                         (substring s 0 (- (string-length s) 3))))
                     files))
         (files (randomize-list files))
         (cmd1 "../src/emacs  --no-init-file --no-site-file --no-site-lisp -L ':.' -l ert -l ")
         (cmd2 " --batch --eval '(ert-run-tests-batch-and-exit (quote (not (or (tag :expensive-test) (tag :unstable) (tag :nativecomp)))))'")
         (cmd (string-concatenate (list cmd1 (string-join files " -l ") cmd2))))
    (format #t "Running test files: ~a~%" files)
    (format #t "running ===> ~a~%" cmd)
    (let ((port (open-input-pipe cmd)))
      (do ((line (read-line port) (read-line port))
           (eof-object? port))
          (format #t "~a~%" line))
      (let ((rc (close-pipe port)))
        (if (not (= rc 0))
            (error "test FAIL rc:" (status:exit-val rc)))))))

(define (main args)
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
                    ; run any currently collected files
                    (unless (null? files)
                      (run-tests files))
                    ; run the files in the group
                    (run-tests (cdr line))
                    (set! files '()))
                   (else
                    (set! files (cons line files))))))
              %tests)
    (unless (null? files)
      (run-tests files))
    (exit)))
