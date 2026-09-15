;;; test-m36-imp2.scm --- M36 imp-2: retire the last keyboard.c stubs.
;;;
;;; brief.org (M36 imp-2) retires three C stubs: pop_kboard,
;;; detect_input_pending, and detect_input_pending_run_timers.  Each
;;; loses its definition, its extern, and its last live buildable C
;;; caller.  The decision moves into (emacs single-kboard), (emacs
;;; kbd-buffer), and (emacs process-wait); the C keeps the mechanism and
;;; the static dispatch.  The three --=-shims that wrapped the detect
;;; family are gone.
;;;
;;; This corpus pins the retirement so the claims are checked
;;; automatically and not only by hand.
;;;
;;; Checks:
;;;    1. keyboard.c holds no definition of the three stubs.
;;;    2. keyboard.h / lisp.h hold no extern for them.
;;;    3. No buildable C caller remains: a whole-token, comment-blind
;;;       scan of src/*.c and src/*.h finds none of the three names.
;;;    4. The three --=-shims are gone from keyboard.c.
;;;    5. (emacs kbd-buffer) exports the two detect procedures.
;;;    6. (emacs process-wait) exports wait-skip-select? and reads
;;;       detect-input-pending?.
;;;    7. The four consumers no longer name the deleted shims.
;;;    8. No Scheme #f remains in the new procedure bodies.
;;;    9. The kbd_pop_kboard dispatcher calls (emacs single-kboard)
;;;       pop-kboard!.
;;;   10. keyboard.c keeps detect_input_pending_ignore_squeezables.
;;;   11. The brief.org §9 surface anchors hold.
;;;   12. tool/run-tests.scm registers test/keyboard/test-m36-imp2.el.
;;;   13. cr.org F1/F2/F3: no C source names the retired detect family
;;;       in a comment; read-char.scm passes #nil (never #f) for a
;;;       false do_display.
;;;   14. cr.org re-review F2/F3: the single-kboard module note and the
;;;       m22 test header are repaired.
;;;   15. cr.org G1/G2: the M35 close-out record check pins the frozen
;;;       M35 counts, and the m34-imp6 pop_kboard pin uses the anchored
;;;       retired form.
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
                 ((and (not in-block) (char=? c #\/)
                       (< (+ i 1) len) (char=? (string-ref text (+ i 1)) #\*))
                  (loop (+ i 2) #t))
                 (in-block
                  (if (and (char=? c #\*) (< (+ i 1) len)
                           (char=? (string-ref text (+ i 1)) #\/))
                      (loop (+ i 2) #f)
                      (loop (+ i 1) #t)))
                 ((and (char=? c #\/) (< (+ i 1) len)
                       (char=? (string-ref text (+ i 1)) #\/))
                  (let skip ((j i))
                    (if (>= j len)
                        #f
                        (if (char=? (string-ref text j) #\newline)
                            (loop (+ j 1) #f)
                            (skip (+ j 1))))))
                 ((char=? c #\")
                  (let skip ((j (+ i 1)))
                    (cond ((>= j len) #f)
                          ((char=? (string-ref text j) #\\) (skip (+ j 2)))
                          ((char=? (string-ref text j) #\") (loop (+ j 1) #f))
                          (else (skip (+ j 1))))))
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

(define (scheme-code-occurs? text token)
  "True when TOKEN occurs in a Scheme CODE line of TEXT (not after a
`;' comment)."
  (any (lambda (l)
         (let ((pos (string-contains l token)))
           (and pos
                (let ((semi (let loop ((i 0))
                              (cond ((>= i (string-length l)) #f)
                                    ((char=? (string-ref l i) #\;) i)
                                    (else (loop (1+ i)))))))
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
    (begin (report "m36/imp2/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m36-root "."))
    (report "m36/imp2/root-bound" 'PASS))

(define kbd   (slurp (repo "src/keyboard.c")))
(define kbd-h (slurp (repo "src/keyboard.h")))
(define lisp-h (slurp (repo "src/lisp.h")))
(define proc-c (slurp (repo "src/process.c")))
(define pgobble (slurp (repo "mod/emacs/process-wait.scm")))
(define xterm-scm (slurp (repo "mod/emacs/xterm.scm")))
(define display-scm (slurp (repo "mod/emacs/display.scm")))
(define readchar-scm (slurp (repo "mod/emacs/read-char.scm")))
(define kbd-buffer-scm (slurp (repo "mod/emacs/kbd-buffer.scm")))
(define kg (slurp (repo "src/keyboard-globals.c")))

;;; --- 1. No definition remains in keyboard.c -----------------------
(if (not kbd)
    (report "m36/imp2/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      ;; A definition is a whole code token outside a comment.  The
      ;; retirements leave only comments and the kbd_pop_kboard
      ;; dispatcher (kbd_ prefix), which is not a bare token.
      (check "m36/imp2/code/pop-kboard-gone" #f
             (contains-token-in-code? kbd "pop_kboard"))
      (check "m36/imp2/code/detect-input-pending-gone" #f
             (contains-token-in-code? kbd "detect_input_pending"))
      (check "m36/imp2/code/detect-input-pending-run-timers-gone" #f
             (contains-token-in-code? kbd "detect_input_pending_run_timers"))))

;;; --- 2. No extern remains in the headers --------------------------
(if (not kbd-h)
    (report "m36/imp2/scan/keyboard.h" (cons 'FAIL "src/keyboard.h missing"))
    (check "m36/imp2/extern/pop-kboard-gone" #f
           (contains? kbd-h "extern void pop_kboard (void)")))
(if (not lisp-h)
    (report "m36/imp2/scan/lisp.h" (cons 'FAIL "src/lisp.h missing"))
    (begin
      (check "m36/imp2/extern/detect-input-pending-gone" #f
             (contains? lisp-h "extern bool detect_input_pending (void)"))
      (check "m36/imp2/extern/detect-input-pending-run-timers-gone" #f
             (contains? lisp-h "extern bool detect_input_pending_run_timers (bool)"))))

;;; --- 3. No live buildable C caller remains ------------------------
(define (any-code-token? token)
  (let loop ((fs (src-code-files)))
    (cond ((null? fs) #f)
          ((contains-token-in-code? (slurp (car fs)) token)
           (car fs))
          (else (loop (cdr fs))))))
(info "m36/imp2/caller/pop-kboard/code-file" (or (any-code-token? "pop_kboard") "none"))
(info "m36/imp2/caller/detect-input-pending/code-file" (or (any-code-token? "detect_input_pending") "none"))
(check "m36/imp2/caller/pop-kboard/no-code-caller" #f (any-code-token? "pop_kboard"))
(check "m36/imp2/caller/detect-input-pending/no-code-caller" #f
       (any-code-token? "detect_input_pending"))
(check "m36/imp2/caller/detect-input-pending-run-timers/no-code-caller" #f
       (any-code-token? "detect_input_pending_run_timers"))

;;; --- 4. The three --=-shims are gone from keyboard.c --------------
(if (not kbd)
    (report "m36/imp2/scan/shim" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m36/imp2/shim/detect-input-pending-gone" #f
             (contains? kbd "\"--detect-input-pending\""))
      (check "m36/imp2/shim/detect-input-pending-run-timers-gone" #f
             (contains? kbd "\"--detect-input-pending-run-timers\""))
      (check "m36/imp2/shim/rc-detect-input-pending-run-timers-gone" #f
             (contains? kbd "\"--rc-detect-input-pending-run-timers\""))
      ;; No source file may name the shims, comments included.
      (check "m36/imp2/shim/no-mention-anywhere" #f
             (any (lambda (fs) (contains? (slurp fs) "--detect-input-pending"))
                  (src-code-files)))
      (check "m36/imp2/shim/no-rc-mention-anywhere" #f
             (any (lambda (fs) (contains? (slurp fs) "--rc-detect-input-pending-run-timers"))
                  (src-code-files)))))

;;; --- 5. (emacs kbd-buffer) exports the two detect procedures ------
(if (not kbd-buffer-scm)
    (report "m36/imp2/scan/kbd-buffer.scm" (cons 'FAIL "module missing"))
    (begin
      (check "m36/imp2/kbd-buffer/defines-detect-input-pending" #t
             (contains? kbd-buffer-scm "(define (detect-input-pending?)"))
      (check "m36/imp2/kbd-buffer/defines-detect-input-pending-run-timers" #t
             (contains? kbd-buffer-scm "(define (detect-input-pending-run-timers? do-display)"))
      (check "m36/imp2/kbd-buffer/exports-detect-input-pending" #t
             (contains? kbd-buffer-scm "detect-input-pending?"))
      (check "m36/imp2/kbd-buffer/exports-detect-input-pending-run-timers" #t
             (contains? kbd-buffer-scm "detect-input-pending-run-timers?"))
      (check "m36/imp2/kbd-buffer/no-new-c-primitive" #f
             (contains? kbd-buffer-scm "--detect-input-pending"))))

;;; --- 6. (emacs process-wait) exports wait-skip-select? ------------
(if (not pgobble)
    (report "m36/imp2/scan/process-wait.scm" (cons 'FAIL "module missing"))
    (begin
      (check "m36/imp2/process-wait/exports-wait-skip-select" #t
             (contains? pgobble "wait-skip-select?"))
      (check "m36/imp2/process-wait/defines-wait-skip-select" #t
             (contains? pgobble "(define (wait-skip-select? read-kbd)"))
      (check "m36/imp2/process-wait/calls-detect-input-pending" #t
             (contains? pgobble "%detect-input-pending?"))))
(if (not proc-c)
    (report "m36/imp2/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      (check "m36/imp2/process.c/dispatch-wait-skip-select" #t
             (contains? proc-c "scm_c_public_ref (\"emacs process-wait\", \"wait-skip-select?\")"))
      (check "m36/imp2/process.c/calls-wait-skip-select" #t
             (contains? proc-c "wait_skip_select (read_kbd)"))))

;;; --- 7. The four consumers no longer name the deleted shims -------
(define (consumer-clean? text)
  (and (not (contains? text "--detect-input-pending"))
       (not (contains? text "--rc-detect-input-pending-run-timers"))))
(if (not pgobble) (report "m36/imp2/consumer/process-wait" (cons 'FAIL "missing"))
    (check "m36/imp2/consumer/process-wait/shim-gone" #t (consumer-clean? pgobble)))
(if (not display-scm) (report "m36/imp2/consumer/display" (cons 'FAIL "missing"))
    (check "m36/imp2/consumer/display/shim-gone" #t (consumer-clean? display-scm)))
(if (not xterm-scm) (report "m36/imp2/consumer/xterm" (cons 'FAIL "missing"))
    (check "m36/imp2/consumer/xterm/shim-gone" #t (consumer-clean? xterm-scm)))
(if (not readchar-scm) (report "m36/imp2/consumer/read-char" (cons 'FAIL "missing"))
    (check "m36/imp2/consumer/read-char/shim-gone" #t (consumer-clean? readchar-scm)))

;;; --- 8. No Scheme #f in the new procedure bodies (cr.org F-3) -----
;;; The C dispatchers read the results with !NILP; this Guile reads #f
;;; as elisp true (src/frame.c:66).  Return elisp #nil for false.
(if (not kbd-buffer-scm)
    (report "m36/imp2/scan/bools" (cons 'FAIL "kbd-buffer.scm missing"))
    (let* ((ip (def-region kbd-buffer-scm "(define (kbd-buffer-input-pending?)"))
           (di (def-region kbd-buffer-scm "(define (detect-input-pending?)"))
           (dr (def-region kbd-buffer-scm "(define (detect-input-pending-run-timers? do-display)"))
           (ip-c (strip-scheme-strings (or ip "")))
           (di-c (strip-scheme-strings (or di "")))
           (dr-c (strip-scheme-strings (or dr ""))))
      (check "m36/imp2/kbd-buffer/input-pending-returns-nil" #t
             (contains? ip-c "#nil"))
      (check "m36/imp2/kbd-buffer/input-pending-no-scheme-false" #f
             (contains? ip-c "#f"))
      (check "m36/imp2/kbd-buffer/detect-input-pending-returns-nil" #t
             (contains? di-c "#nil"))
      (check "m36/imp2/kbd-buffer/detect-input-pending-no-scheme-false" #f
             (contains? di-c "#f"))
      (check "m36/imp2/kbd-buffer/detect-run-timers-returns-nil" #t
             (contains? dr-c "#nil"))
      (check "m36/imp2/kbd-buffer/detect-run-timers-no-scheme-false" #f
             (contains? dr-c "#f"))))
(if (not pgobble)
    (report "m36/imp2/scan/bools-wait" (cons 'FAIL "process-wait.scm missing"))
    (let* ((ws (def-region pgobble "(define (wait-skip-select? read-kbd)"))
           (ws-c (strip-scheme-strings (or ws ""))))
      (check "m36/imp2/process-wait/wait-skip-select-returns-nil" #t
             (contains? ws-c "#nil"))
      (check "m36/imp2/process-wait/wait-skip-select-no-scheme-false" #f
             (contains? ws-c "#f"))))

;;; --- 9. The kbd_pop_kboard dispatcher -----------------------------
(if (not kbd)
    (report "m36/imp2/scan/dispatcher" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m36/imp2/dispatcher/kbd-pop-kboard-def" #t
             (contains? kbd "kbd_pop_kboard (void)"))
      (check "m36/imp2/dispatcher/kbd-pop-kboard-call" #t
             (contains? kbd "kbd_pop_kboard ();"))
      (check "m36/imp2/dispatcher/calls-single-kboard" #t
             (contains? kbd "scm_c_public_ref (\"emacs single-kboard\", \"pop-kboard!\")"))))

;;; --- 10. keyboard.c keeps detect_input_pending_ignore_squeezables -
(if (not kbd)
    (report "m36/imp2/scan/keep" (cons 'FAIL "src/keyboard.c missing"))
    (check "m36/imp2/keep/detect-input-pending-ignore-squeezables" #t
           (contains? kbd "detect_input_pending_ignore_squeezables (void)")))

;;; --- 11. The brief.org §9 surface anchors hold --------------------
(if (not kbd)
    (report "m36/imp2/scan/keyboard.c-counts" (cons 'FAIL "missing"))
    (begin
      (check "m36/imp2/count/keyboard.c-lines" 11238
             (count-substr kbd "\n"))
      (check "m36/imp2/count/keyboard.c-defuns" 446
             (count-prefix kbd "DEFUN (\""))
      (check "m36/imp2/count/keyboard.c-shims" 420
             (count-prefix kbd "DEFUN (\"--"))))
(info "m36/imp2/count/keyboard-globals.c-lines" (count-substr kg "\n"))
(check "m36/imp2/count/combined-lines" 11728
       (+ (count-substr kbd "\n") (count-substr kg "\n")))
(check "m36/imp2/count/under-budget" #t
       (<= (+ (count-substr kbd "\n") (count-substr kg "\n")) 11960))
(check "m36/imp2/count/scm-c-public-ref-sites" 156
       (src-site-count))

;;; --- 12. Static: the corpus is registered in the keyboard group ---
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
                                      "\"test/keyboard/test-m36-imp2.el\""))))
  (check "m36/imp2/run-tests.scm/registers-el" #t
         (and (string? run-tests)
              (and reg-idx
                   (contains? (list-ref rt-lines reg-idx)
                              "\"test/keyboard/test-m36-imp2.el\""))
              (and kg-end
                   (< kg-start reg-idx)
                   (< reg-idx kg-end)))))

;;; --- 13. cr.org findings (F1, F2, F3) -----------------------------
;;; These checks pin the repairs the review asked for.  They are not in
;;; brief.org, so they are labelled with cr.org.
;;;
;;; F-1: no C source may still name the retired detect family in a
;;; comment.  A plain whole-token scan catches a standalone name; the
;;; surviving detect_input_pending_ignore_squeezables does not match,
;;; because `_' is a word character.
(define (any-plain-token? token)
  (any (lambda (fs) (contains-token? (slurp fs) token)) (src-code-files)))
(check "m36/imp2/cr/F1/no-stale-detect-input-pending" #f
       (any-plain-token? "detect_input_pending"))
(check "m36/imp2/cr/F1/no-stale-detect-input-pending-run-timers" #f
       (any-plain-token? "detect_input_pending_run_timers"))
(check "m36/imp2/cr/F1/keep-detect-input-pending-ignore-squeezables" #t
       (contains-token? kbd "detect_input_pending_ignore_squeezables"))

;;; F-2: the bug#46935 comment names the ported input-pending test.
(check "m36/imp2/cr/F2/bug-46935-names-wait-skip-select" #t
       (contains? proc-c "wait-skip-select? in (emacs process-wait)) returns"))

;;; F-3: read-char.scm passes #nil, never #f, for a false do_display.
;;; A Scheme #f reads as elisp true, so it would turn the redisplay on.
(check "m36/imp2/cr/F3/read-char-no-false-do-display" #f
       (contains? readchar-scm "%swallow-events) #f"))
(check "m36/imp2/cr/F3/read-char-nil-do-display" #t
       (contains? readchar-scm "%swallow-events) #nil"))
(check "m36/imp2/cr/F3/read-char-comment-updated" #f
       (contains? readchar-scm "callers pass #f"))

;;; --- 14. cr.org re-review findings (F2, F3) -----------------------
;;; The second review (cr.org §4) found two stale comments outside the
;;; C tree.  These checks pin the repairs.  Both files are tracked, so
;;; the corpus stays batch-safe.
(define skb-scm (slurp (repo "mod/emacs/single-kboard.scm")))
(define m22-el  (slurp (repo "test/keyboard/test-m22-input-pending.el")))

;;; F-2: the single-kboard module note must not claim the pop_kboard ()
;;; call resolves through the deleted C dispatcher.  It must name the
;;; static kbd_pop_kboard dispatcher instead.
(check "m36/imp2/cr2/F2/single-kboard-note-repaired" #f
       (contains? skb-scm "back through the C dispatcher"))
(check "m36/imp2/cr2/F2/single-kboard-note-names-dispatcher" #t
       (contains? skb-scm "kbd_pop_kboard dispatcher"))

;;; F-3: the m22 test header must not name the retired
;;; detect_input_pending as a bare token.  It may name the surviving
;;; detect_input_pending_ignore_squeezables, because `_' is a word char.
(check "m36/imp2/cr2/F3/m22-comment-drops-retired-name" #f
       (contains-token? m22-el "detect_input_pending"))
(check "m36/imp2/cr2/F3/m22-comment-names-ignore-squeezables" #t
       (contains-token? m22-el "detect_input_pending_ignore_squeezables"))

;;; --- 15. cr.org G1/G2 findings ------------------------------------
;;; The cr.org review (G1, G2) found two stale test pins that imp-2
;;; left behind.  These checks pin the repairs.  Both corpora are
;;; tracked, so the checks stay batch-safe.

;;; G-1: test/keyboard/test-m35-imp3.scm §8 compares the M35 doc record
;;; to the live tree.  The M35 record is history, so §8 must pin the
;;; recorded M35 close-out counts, not the live counts.  Check the
;;; frozen values are present, and the old live comparison is gone.
(define m35-imp3 (slurp (repo "test/keyboard/test-m35-imp3.scm")))
(check "m36/imp2/cr/G1/m35-imp3-pins-keyboard.c-lines" #t
       (contains? m35-imp3 "(comma-format 11338)"))
(check "m36/imp2/cr/G1/m35-imp3-pins-combined-lines" #t
       (contains? m35-imp3 "(comma-format 11828)"))
(check "m36/imp2/cr/G1/m35-imp3-pins-scp-sites" #t
       (contains? m35-imp3 "(comma-format 155)"))
(check "m36/imp2/cr/G1/m35-imp3-no-live-count-compare" #f
       (contains? m35-imp3 "(comma-format (count-substr kbd"))

;;; G-2: test/keyboard/test-m34-imp6.scm must pin pop_kboard as
;;; retired, with the anchored form \npop_kboard (void), so the static
;;; kbd_pop_kboard dispatcher does not match.  It must not keep the old
;;; unanchored "pop-still-defined" check.
(define m34-imp6 (slurp (repo "test/keyboard/test-m34-imp6.scm")))
(check "m36/imp2/cr/G2/m34-imp6-pop-retired" #t
       (contains? m34-imp6 "m34/imp6/keyboard.c/pop-retired"))
(check "m36/imp2/cr/G2/m34-imp6-no-stale-pop-still-defined" #f
       (contains? m34-imp6 "pop-still-defined"))
(check "m36/imp2/cr/G2/m34-imp6-anchored-pop-token" #t
       (contains? m34-imp6 "kbd \"\\npop_kboard (void)\""))
