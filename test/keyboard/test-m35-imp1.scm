;;; test-m35-imp1.scm --- M35 imp-1: the two reclaimed comment anchors.
;;;
;;; brief.org (M35 imp-1) repairs two stale comment line numbers and
;;; changes no code:
;;;
;;;   - src/xdisp.c:582 -- "(src/xdisp.c:27739, :28525)" became
;;;     "(src/xdisp.c:27788, :28574)".  The two xdisp_pop_kboard call
;;;     sites moved in M34 imp-6.
;;;   - src/keyboard.c:3927 -- "(term.c:3566)" became "(term.c:3595)".
;;;     The tty_menu_discard_mouse_events caller moved in M33 imp-1.
;;;
;;; brief.org §5 notes that no test reads these two comment texts, so a
;;; line number can come back with no signal.  This corpus pins both:
;;;
;;;   - the comment text holds the current numbers, and holds no stale
;;;     number;
;;;   - the numbers are not hard-coded guesses: they equal the real
;;;     1-based line numbers of the live call sites in src/xdisp.c and
;;;     src/term.c.  A future move of a call site fails this test until
;;;     the comment is repaired again.
;;;
;;; The repo root is bound by the .el wrapper as %m35-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m35-imp1.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

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

(define (lines-of text)
  (call-with-input-string text
    (lambda (port)
      (let loop ((acc '()))
        (let ((l (read-line port)))
          (if (eof-object? l) (reverse acc) (loop (cons l acc))))))))

(define (all-line-numbers text needle)
  "1-based numbers of every line of TEXT that equals NEEDLE exactly.
The exact equality is the anchor: an indented call site is counted, a
comment mention of the same text is not."
  (let loop ((ls (lines-of text)) (n 1) (acc '()))
    (cond ((null? ls) (reverse acc))
          ((string=? (car ls) needle) (loop (cdr ls) (1+ n) (cons n acc)))
          (else (loop (cdr ls) (1+ n) acc)))))

(define (repo path) (string-append %m35-root "/" path))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m35-root))
    (begin (report "m35-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m35-root "."))
    (report "m35-root-bound" 'PASS))

;;; --- 1. src/xdisp.c: the pop_kboard comment ------------------------
(define xdisp-c (slurp (repo "src/xdisp.c")))
(if (not xdisp-c)
    (report "m35/imp1/scan/xdisp.c" (cons 'FAIL "src/xdisp.c missing"))
    (begin
      ;; The comment holds the current numbers and no stale number.
      (check "m35/imp1/xdisp.c/comment-pop_kboard" #t
             (contains? xdisp-c "(src/xdisp.c:27788, :28574)"))
      (check "m35/imp1/xdisp.c/no-stale-pop_kboard" #f
             (contains? xdisp-c "(src/xdisp.c:27739, :28525)"))
      ;; The numbers are the real call-site lines: there are exactly two
      ;; bare "  xdisp_pop_kboard ();" call lines, at 27788 and 28574.
      (check "m35/imp1/xdisp.c/pop-sites" '(27788 28574)
             (all-line-numbers xdisp-c "  xdisp_pop_kboard ();"))))

;;; --- 2. src/term.c: the discard_mouse_events caller ----------------
(define term-c (slurp (repo "src/term.c")))
(if (not term-c)
    (report "m35/imp1/scan/term.c" (cons 'FAIL "src/term.c missing"))
    (begin
      (check "m35/imp1/term.c/discard-caller" '(3595)
             (all-line-numbers term-c "  tty_menu_discard_mouse_events ();"))))

;;; --- 3. src/keyboard.c: the discard_mouse_events comment -----------
(define kbd (slurp (repo "src/keyboard.c")))
(if (not kbd)
    (report "m35/imp1/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m35/imp1/keyboard.c/comment-term" #t
             (contains? kbd "(term.c:3595)"))
      (check "m35/imp1/keyboard.c/no-stale-term" #f
             (contains? kbd "(term.c:3566)"))))

;;; --- 4. Static: the test is registered -----------------------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m35/imp1/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m35-imp1.el"))

;;; --- 5. Static: the ERT name is the corpus name verbatim -----------
;;; The corpus name is already namespaced (m35/imp1/...), so the
;;; wrapper must register each ERT test under the bare name.  A
;;; second "m35-imp1/" prefix would make the ERT name
;;; "m35-imp1/m35/imp1/...".  This pins that form.
(define wrapper (slurp (repo "test/keyboard/test-m35-imp1.el")))
(check "m35/imp1/wrapper/ert-name-bare" #t
       (contains? wrapper "(intern name)"))
(check "m35/imp1/wrapper/no-double-prefix" #f
       (contains? wrapper "(intern (format \"m35-imp1/%s\" name))"))
