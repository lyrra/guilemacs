;;; test-m36-imp1.scm --- M36 imp-1: retire swallow_events and timer_check.
;;;
;;; brief.org (M36 imp-1) retires two C stubs.  Their only live callers
;;; are in process.c's wait_reading_process_output.  The decision moves
;;; into (emacs process-wait); the C keeps the loop control and the
;;; static dispatch.  timer_check has no live buildable caller at HEAD
;;; (its only in-tree call sat in the dead "#else /* not subprocesses */"
;;; MS-DOS copy, now deleted); its one remaining caller is NS-only
;;; (src/nsmenu.m), which does not count because HAVE_NS is undefined.
;;;
;;; This corpus pins the retirement so the claims are checked
;;; automatically and not only by hand.
;;;
;;; Checks:
;;;   1. keyboard.c holds no definition of either stub.
;;;   2. keyboard.h holds no extern for either stub.
;;;   3. No buildable C caller remains: a whole-token scan of src/*.c and
;;;      src/*.h finds the names in comments only.  The NS caller is
;;;      named (src/nsmenu.m:1972) and the HAVE_NS guard is pinned.
;;;   4. (emacs process-wait) exports the two new procedures and
;;;      process.c calls them.
;;;   5. The dead "#else /* not subprocesses */" copy is gone; the live
;;;      update_processes_for_thread_death stays.
;;;   6. The (SEC . NSEC) -> struct timespec conversion stays C.
;;;   7. The brief.org §9 surface anchors hold.
;;;
;;; The corpus also pins the registration in tool/run-tests.scm.
;;;
;;; All checks read files, so the corpus is batch-safe.
;;;
;;; The repo root is bound by the .el wrapper as %m36-root.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))
(use-modules (srfi srfi-1))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (info name value)
  (report name (list 'INFO value)))

(define (slurp path)
  "Return the whole file at PATH as a string, or #f when it is absent."
  (if (not (file-exists? path))
      #f
      (call-with-input-file path
        (lambda (port)
          (let loop ((chars '()))
            (let ((c (read-char port)))
              (if (eof-object? c)
                  (list->string (reverse chars))
                  (loop (cons c chars)))))))))

(define (contains? text needle)
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (word-char? c)
  (or (char-alphabetic? c) (char-numeric? c) (char=? c #\_)))

(define (contains-token? text token)
  "True when TOKEN occurs in TEXT as a whole identifier (\\bTOKEN\\b)."
  (if (not (string? text))
      #f
      (let ((n (string-length token))
            (len (string-length text)))
        (let loop ((i 0))
          (if (> (+ i n) len)
              #f
              (if (and (string=? token (substring text i (+ i n)))
                       (or (= i 0)
                           (not (word-char? (string-ref text (1- i)))))
                       (or (= (+ i n) len)
                           (not (word-char? (string-ref text (+ i n))))))
                  #t
                  (loop (1+ i))))))))

(define (contains-token-in-code? text token)
  "True when TOKEN occurs in TEXT outside a C comment, a string, or a
character literal.  This is the whole-token scan with comment blindness:
it matches `rg' on source lines that a compiler would see.  It tracks
/* */ blocks and // lines so a comment mention does not count as a
caller."
  (if (not (string? text))
      #f
      (let ((n (string-length token))
            (len (string-length text)))
        (let loop ((i 0) (in-block #f))
          (if (>= i len)
              #f
              (let ((c (string-ref text i)))
                (cond
                 ;; block comment start /* (also a /*-started line)
                 ((and (not in-block) (char=? c #\/)
                       (< (+ i 1) len) (char=? (string-ref text (+ i 1)) #\*))
                  (loop (+ i 2) #t))
                 (in-block
                  (if (and (char=? c #\*) (< (+ i 1) len)
                           (char=? (string-ref text (+ i 1)) #\/))
                      (loop (+ i 2) #f)
                      (loop (+ i 1) #t)))
                 ;; line comment //
                 ((and (char=? c #\/) (< (+ i 1) len)
                       (char=? (string-ref text (+ i 1)) #\/))
                  (let skip ((j i))
                    (if (>= j len)
                        #f
                        (if (char=? (string-ref text j) #\newline)
                            (loop (+ j 1) #f)
                            (skip (+ j 1))))))
                 ;; string literal
                 ((char=? c #\")
                  (let skip ((j (+ i 1)))
                    (cond ((>= j len) #f)
                          ((char=? (string-ref text j) #\\) (skip (+ j 2)))
                          ((char=? (string-ref text j) #\") (loop (+ j 1) #f))
                          (else (skip (+ j 1))))))
                 ;; character literal
                 ((char=? c #\')
                  (let skip ((j (+ i 1)))
                    (cond ((>= j len) #f)
                          ((char=? (string-ref text j) #\\) (skip (+ j 2)))
                          ((char=? (string-ref text j) #\') (loop (+ j 1) #f))
                          (else (skip (+ j 1))))))
                 (else
                  (if (and (<= (+ i n) len)
                           (string=? token (substring text i (+ i n)))
                           (or (= i 0)
                               (not (word-char? (string-ref text (1- i)))))
                           (or (= (+ i n) len)
                               (not (word-char? (string-ref text (+ i n))))))
                      #t
                      (loop (+ i 1) #f))))))))))

(define (repo path) (string-append %m36-root "/" path))

(define (split-lines text)
  (call-with-input-string text
    (lambda (port)
      (let loop ((acc '()))
        (let ((line (read-line port)))
          (if (eof-object? line) (reverse acc) (loop (cons line acc))))))))

(define (files-with-ext dir suffix)
  "Names of the files in DIR whose name ends with SUFFIX."
  (if (not (file-exists? dir))
      '()
      (scandir dir (lambda (n) (string-suffix? suffix n)))))

(define (count-substr text sub)
  "Number of non-overlapping occurrences of SUB in TEXT."
  (if (not (string? text)) 0
      (let ((n (string-length sub)))
        (let loop ((i 0) (acc 0))
          (if (> (+ i n) (string-length text))
              acc
              (if (string=? sub (substring text i (+ i n)))
                  (loop (+ i n) (1+ acc))
                  (loop (1+ i) acc)))))))

(define (count-prefix text prefix)
  "Number of lines of TEXT that start with PREFIX."
  (if (not (string? text)) 0
      (count (lambda (l) (string-prefix? prefix l)) (split-lines text))))

(define (src-code-files)
  "The buildable top-level C sources and headers of src/."
  (append (map (lambda (n) (string-append (repo "src") "/" n))
               (files-with-ext (repo "src") ".c"))
          (map (lambda (n) (string-append (repo "src") "/" n))
               (files-with-ext (repo "src") ".h"))))

(define (src-site-count)
  "grep -rn 'scm_c_public_ref' src/*.c src/*.h | wc -l"
  (let loop ((fs (src-code-files)) (acc 0))
    (if (null? fs)
        acc
        (let ((t (slurp (car fs))))
          (loop (cdr fs)
                (+ acc (count (lambda (l) (string-contains l "scm_c_public_ref"))
                              (if t (split-lines t) '()))))))))

(define (scheme-comment-index line)
  "Index of the first `;' in LINE, or #f."
  (let loop ((i 0))
    (cond ((>= i (string-length line)) #f)
          ((char=? (string-ref line i) #\;) i)
          (else (loop (1+ i))))))

(define (scheme-code-occurs? text token)
  "True when TOKEN occurs in a Scheme CODE line of TEXT (not after a
`;' comment).  Mirrors the comment-blind token scan for C, adapted to
Scheme comments."
  (any (lambda (l)
         (let ((pos (string-contains l token)))
           (and pos
                (let ((semi (scheme-comment-index l)))
                  (or (not semi) (< pos semi))))))
       (split-lines text)))

(define (strip-scheme-strings text)
  "Return TEXT with every \"...\" Scheme string literal removed (a
backslash escapes the next character).  This exposes the code inside a
definition without its docstring, so a `#f' mentioned in prose does not
count as a returned value."
  (if (not (string? text)) ""
      (call-with-output-string
        (lambda (out)
          (let ((len (string-length text)))
            (let loop ((i 0))
              (if (>= i len)
                  #t
                  (let ((c (string-ref text i)))
                    (if (char=? c #\")
                        (let skip ((j (+ i 1)))
                          (cond ((>= j len) (loop j))
                                ((char=? (string-ref text j) #\\) (skip (+ j 2)))
                                ((char=? (string-ref text j) #\") (loop (+ j 1)))
                                (else (skip (+ j 1)))))
                        (begin (write-char c out) (loop (+ i 1))))))))))))

(define (def-region text sig)
  "The text of the top-level definition whose head is SIG, up to the
next top-level `(define ' or the end of TEXT.  #f when SIG is absent."
  (let ((start (string-contains text sig)))
    (if (not start)
        #f
        (let* ((rest (substring text start (string-length text)))
               (next (string-contains rest "\n(define ")))
          (if next (substring rest 0 next) rest)))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m36-root))
    (begin (report "m36/imp1/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m36-root "."))
    (report "m36/imp1/root-bound" 'PASS))

(define kbd   (slurp (repo "src/keyboard.c")))
(define kbd-h (slurp (repo "src/keyboard.h")))
(define proc-c (slurp (repo "src/process.c")))
(define pgobble (slurp (repo "mod/emacs/process-wait.scm")))
(define nsmenu-m (slurp (repo "src/nsmenu.m")))
(define config-h (slurp (repo "src/config.h")))
(define kg (slurp (repo "src/keyboard-globals.c")))

;;; --- 1. No definition remains in keyboard.c -----------------------
(if (not kbd)
    (report "m36/imp1/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m36/imp1/def/swallow-events-gone" #f
             (contains? kbd "swallow_events (bool do_display)"))
      (check "m36/imp1/def/timer-check-gone" #f
             (contains? kbd "timer_check (void)"))
      ;; A definition would be a whole code token; comments may still
      ;; mention the retired names.
      (check "m36/imp1/code/swallow-events-gone" #f
             (contains-token-in-code? kbd "swallow_events"))
      (check "m36/imp1/code/timer-check-gone" #f
             (contains-token-in-code? kbd "timer_check"))))

;;; --- 2. No extern remains in keyboard.h ---------------------------
(if (not kbd-h)
    (report "m36/imp1/scan/keyboard.h" (cons 'FAIL "src/keyboard.h missing"))
    (begin
      (check "m36/imp1/extern/swallow-events-gone" #f
             (contains? kbd-h "extern void swallow_events"))
      (check "m36/imp1/extern/timer-check-gone" #f
             (contains? kbd-h "extern struct timespec timer_check"))))

;;; --- 3. No live buildable C caller remains ------------------------
;;; The whole-token, comment-blind scan must find neither name in any
;;; buildable src/*.c or src/*.h file.  The only remaining caller is
;;; NS-only (src/nsmenu.m:1972) and does not count.
(define (any-code-token? token)
  (let loop ((fs (src-code-files)))
    (cond ((null? fs) #f)
          ((contains-token-in-code? (slurp (car fs)) token)
           (car fs))
          (else (loop (cdr fs))))))
(info "m36/imp1/caller/swallow-events/code-file" (or (any-code-token? "swallow_events") "none"))
(info "m36/imp1/caller/timer-check/code-file" (or (any-code-token? "timer_check") "none"))
(check "m36/imp1/caller/swallow-events/no-code-caller" #f (any-code-token? "swallow_events"))
(check "m36/imp1/caller/timer-check/no-code-caller" #f (any-code-token? "timer_check"))
;; The recorded NS caller stays and is not buildable.
(check "m36/imp1/caller/timer-check/ns-nsmenu" #t
       (contains? nsmenu-m "struct timespec next_time = timer_check ()"))
(check "m36/imp1/caller/have-ns-undefined" #t
       (contains? config-h "/* #undef HAVE_NS */"))

;;; --- 4. The ported decisions live in (emacs process-wait) ---------
(if (not pgobble)
    (report "m36/imp1/scan/process-wait.scm" (cons 'FAIL "module missing"))
    (begin
      (check "m36/imp1/module/exports-wait-swallow" #t
             (contains? pgobble "wait-swallow!"))
      (check "m36/imp1/module/exports-wait-input-pending" #t
             (contains? pgobble "wait-input-pending?"))
      (check "m36/imp1/module/defines-wait-swallow" #t
             (contains? pgobble "(define (wait-swallow! read-kbd do-display)"))
      (check "m36/imp1/module/defines-wait-input-pending" #t
             (contains? pgobble "(define (wait-input-pending? read-kbd do-display)"))
      ;; The swallow mechanism is the existing (emacs kbd-buffer) proc.
      (check "m36/imp1/module/swallows-via-kbd-buffer" #t
             (contains? pgobble "kbd-buffer-swallow-events!"))))
(if (not proc-c)
    (report "m36/imp1/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      (check "m36/imp1/process.c/dispatch-wait-swallow" #t
             (contains? proc-c "scm_c_public_ref (\"emacs process-wait\", \"wait-swallow!\")"))
      (check "m36/imp1/process.c/dispatch-wait-input-pending" #t
             (contains? proc-c "scm_c_public_ref (\"emacs process-wait\", \"wait-input-pending?\")"))
      (check "m36/imp1/process.c/calls-wait-swallow" #t
             (contains? proc-c "wait_swallow (read_kbd, do_display)"))
      (check "m36/imp1/process.c/calls-wait-input-pending" #t
             (contains? proc-c "wait_input_pending (read_kbd, do_display)"))))

;;; --- 4b. The module returns elisp booleans, not Scheme #f (cr.org
;;; F-3).  Both procedures must return elisp nil (#nil) for false: this
;;; Guile reads #f as elisp true (src/frame.c:66), and the C dispatcher
;;; wait_swallow reads the result with !NILP, so #nil is the only
;;; correct false value.  Strip the docstrings first, so a `#f' cited in
;;; prose does not count.
(if (not pgobble)
    (report "m36/imp1/scan/process-wait.scm-bools" (cons 'FAIL "module missing"))
    (let* ((ws (def-region pgobble "(define (wait-swallow!"))
           (wip (def-region pgobble "(define (wait-input-pending?"))
           (ws-code (strip-scheme-strings (or ws "")))
           (wip-code (strip-scheme-strings (or wip ""))))
      (check "m36/imp1/module/wait-swallow-returns-nil" #t
             (contains? ws-code "#nil"))
      (check "m36/imp1/module/wait-swallow-no-scheme-false" #f
             (contains? ws-code "#f"))
      (check "m36/imp1/module/wait-input-pending-returns-nil" #t
             (contains? wip-code "#nil"))
      (check "m36/imp1/module/wait-input-pending-no-scheme-false" #f
             (contains? wip-code "#f"))
      ;; F-2: site B ignores the result on purpose; the docstring must
      ;; record the removed #if 0 retest so a reader does not "fix" it.
      (check "m36/imp1/module/wait-input-pending-doc-ignores-result" #t
             (and (contains? (or wip "") "#if 0")
                  (contains? (or wip "") "ignores the result")))))

;;; --- 5. The dead not-subprocesses copy is gone --------------------
(if (not proc-c)
    (report "m36/imp1/scan/process.c-dead" (cons 'FAIL "src/process.c missing"))
    (begin
      (check "m36/imp1/dead/no-not-subprocesses-else" #f
             (contains? proc-c "#else  /* not subprocesses */"))
      (check "m36/imp1/dead/live-thread-death-stays" #t
             (contains? proc-c
                       "update_processes_for_thread_death (Lisp_Object dying_thread)"))
      (check "m36/imp1/dead/one-definition" 1
             (count-substr proc-c
                           "update_processes_for_thread_death (Lisp_Object dying_thread)"))))

;;; --- 6. The conversion stays C ------------------------------------
;;; process.c's wait_run_timers still folds the (SEC . NSEC) pair into a
;;; struct timespec; the module returns the Scheme pair and never names a
;;; timespec.
(check "m36/imp1/conv/c-forms-timespec" #t
       (contains? proc-c
                 "make_timespec (XFIXNUM (XCAR (result)), XFIXNUM (XCDR (result)))"))
(check "m36/imp1/conv/module-no-timespec-in-code" #f
       (scheme-code-occurs? pgobble "timespec"))

;;; --- 7. The brief.org §9 surface anchors hold ---------------------
(if (not kbd)
    (report "m36/imp1/scan/keyboard.c-counts" (cons 'FAIL "missing"))
    (begin
      (check "m36/imp1/count/keyboard.c-lines" 11305
             (count-substr kbd "\n"))
      (check "m36/imp1/count/keyboard.c-defuns" 449
             (count-prefix kbd "DEFUN (\""))
      (check "m36/imp1/count/keyboard.c-shims" 423
             (count-prefix kbd "DEFUN (\"--"))))
(info "m36/imp1/count/keyboard-globals.c-lines" (count-substr kg "\n"))
(check "m36/imp1/count/combined-lines" 11795
       (+ (count-substr kbd "\n") (count-substr kg "\n")))
(check "m36/imp1/count/under-budget" #t
       (<= (+ (count-substr kbd "\n") (count-substr kg "\n")) 11960))
(check "m36/imp1/count/scm-c-public-ref-sites" 155
       (src-site-count))

;;; --- 8. Static: the corpus is registered in the keyboard group ----
(define run-tests (slurp (repo "tool/run-tests.scm")))
(define (line-index-with lines needle)
  (list-index (lambda (l) (string-contains l needle)) lines))
(define (group-close-index lines start)
  (let loop ((i start))
    (cond ((>= i (length lines)) #f)
          ((equal? ")" (string-trim (list-ref lines i))) i)
          (else (loop (1+ i))))))
(let* ((rt-lines (and run-tests (split-lines run-tests)))
       (kg-start (and rt-lines
                      (line-index-with rt-lines "(group ; keyboard.c")))
       (kg-end (and kg-start (group-close-index rt-lines (1+ kg-start))))
       (reg-idx (and rt-lines
                     (line-index-with rt-lines
                                      "\"test/keyboard/test-m36-imp1.el\""))))
  (check "m36/imp1/run-tests.scm/registers-el" #t
         (and (string? run-tests)
              (and reg-idx
                   (contains? (list-ref rt-lines reg-idx)
                              "\"test/keyboard/test-m36-imp1.el\""))
              (and kg-end
                   (< kg-start reg-idx)
                   (< reg-idx kg-end)))))
