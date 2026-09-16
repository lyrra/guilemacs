;;; test-m37-imp3.scm --- M37 imp-3: the close-out.
;;;
;;; brief.org (M37 imp-3) is the close-out.  It ports no new read-path
;;; decision and changes no C file.  It re-measures the surface, runs
;;; the gates, and records the accounting.  This corpus pins the facts
;;; the close-out rests on.
;;;
;;; Checks:
;;;    0. The repo root is bound by the wrapper (%m37-root).
;;;    1. The surface anchors are unchanged (imp-3 changes no C file):
;;;       keyboard.c 11,221 lines, 446 DEFUNs, 420 --=-shims;
;;;       keyboard-globals.c 490; combined 11,711; 159 scm_c_public_ref
;;;       sites.
;;;    2. The budget: combined <= 11,960.
;;;    3. Verdict Q1 -- the kbd_buffer[] ring stays C.  The seven
;;;       raw-array consumers hold their symbol at their line:
;;;       x_defer_selection_requests (xterm.c:905),
;;;       x_delete_selection_requests (:31826),
;;;       x_find_monitors_changed_event (:18660), the kbd_fetch_ptr
;;;       compares in textconv.c (:591, :1607), kbd_store_ptr (:1716),
;;;       and the fatal-safe drain in emacs.c (:2829).  The two memmove
;;;       storage moves hold (xterm.c:31848, :31856).
;;;    4. Verdict Q2 -- the read path is decision-complete.  The
;;;       decision owners live in Scheme: gobble-input!
;;;       (mod/emacs/gobble.scm:180), tty-read-avail-input! (:234), and
;;;       x-input-pending? (mod/emacs/xterm.scm:80).  Each name is
;;;       pinned in code at its line.
;;;    5. The empty reclaim set.  Each of the five read-path shims keeps
;;;       a definition, a src/keyboard.x registration, a live Scheme
;;;       caller at its line, and no C code caller (by DEFUN name or by
;;;       C symbol) in any live buildable src/*.c file.
;;;    6. The kept remnant: gobble_input (keyboard.c:6693),
;;;       kbd_buffer_store_event (:3782), and
;;;       detect_input_pending_ignore_squeezables (:9218) stay C.
;;;       imp-2 pinned the first and the third; imp-3 adds
;;;       kbd_buffer_store_event.
;;;    7. Registration: tool/run-tests.scm names
;;;       test/keyboard/test-m37-imp3.el in the keyboard group, after
;;;       the m37-imp2 row.
;;;    8. The accounting: docs/kb.org ** M37 carries the imp-3
;;;       close-out, the close-out hash, the status line, and the
;;;       recorded gate result.  Skip with an INFO line when absent.
;;;    9. Drift guard: the sibling corpora (M37 imp-1, M37 imp-2) still
;;;       carry their anchors.
;;;
;;; The docs/ checks read untracked files.  When a doc file is absent,
;;; the check prints an INFO line and skips; it does not fail.
;;;
;;; All checks read files, so the corpus needs no C entry point and is
;;; batch-safe.  The repo root is bound by the .el wrapper as %m37-root.

(use-modules (ice-9 rdelim))
(use-modules (ice-9 ftw))
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

(define (code-token-lines text token)
  "Return the 1-based line numbers of TEXT where TOKEN occurs as a whole
token in code (outside a C comment, a string, or a character literal).
This is the whole-token scan with comment blindness.  It matches `rg' on
the source lines that a compiler would see."
  (if (not (string? text))
      '()
      (let ((n (string-length token))
            (len (string-length text)))
        (let loop ((i 0) (line 1) (in-block #f) (acc '()))
          (if (>= i len)
              (reverse acc)
              (let ((c (string-ref text i)))
                (cond
                 ((char=? c #\newline)
                  (loop (+ i 1) (+ line 1) in-block acc))
                 ((and (not in-block) (char=? c #\/)
                       (< (+ i 1) len) (char=? (string-ref text (+ i 1)) #\*))
                  (loop (+ i 2) line #t acc))
                 (in-block
                  (if (and (char=? c #\*) (< (+ i 1) len)
                           (char=? (string-ref text (+ i 1)) #\/))
                      (loop (+ i 2) line #f acc)
                      (loop (+ i 1) line #t acc)))
                 ((and (char=? c #\/) (< (+ i 1) len)
                       (char=? (string-ref text (+ i 1)) #\/))
                  (let skip ((j i))
                    (if (or (>= j len)
                            (char=? (string-ref text j) #\newline))
                        (loop j line #f acc)
                        (skip (+ j 1)))))
                 ((char=? c #\")
                  (let skip ((j (+ i 1)))
                    (cond ((>= j len) (loop j line #f acc))
                          ((char=? (string-ref text j) #\newline)
                           (loop (+ j 1) (+ line 1) #f acc))
                          ((char=? (string-ref text j) #\\) (skip (+ j 2)))
                          ((char=? (string-ref text j) #\") (loop (+ j 1) line #f acc))
                          (else (skip (+ j 1))))))
                 ((char=? c #\')
                  (let skip ((j (+ i 1)))
                    (cond ((>= j len) (loop j line #f acc))
                          ((char=? (string-ref text j) #\newline)
                           (loop (+ j 1) (+ line 1) #f acc))
                          ((char=? (string-ref text j) #\\) (skip (+ j 2)))
                          ((char=? (string-ref text j) #\') (loop (+ j 1) line #f acc))
                          (else (skip (+ j 1))))))
                 (else
                  (if (and (<= (+ i n) len)
                           (string=? token (substring text i (+ i n)))
                           (or (= i 0)
                               (not (word-char? (string-ref text (1- i)))))
                           (or (= (+ i n) len)
                               (not (word-char? (string-ref text (+ i n))))))
                      (loop (+ i n) line #f (cons line acc))
                      (loop (+ i 1) line #f acc))))))))))

(define (repo path) (string-append %m37-root "/" path))

(define (split-lines text)
  (call-with-input-string text
    (lambda (port)
      (let loop ((acc '()))
        (let ((line (read-line port)))
          (if (eof-object? line) (reverse acc) (loop (cons line acc))))))))

(define (files-with-ext dir suffix)
  (if (not (file-exists? dir))
      '()
      (scandir dir (lambda (n) (string-suffix? suffix n)))))

(define (count-substr text sub)
  (if (not (string? text)) 0
      (let ((n (string-length sub)))
        (let loop ((i 0) (acc 0))
          (if (> (+ i n) (string-length text))
              acc
              (if (string=? sub (substring text i (+ i n)))
                  (loop (+ i n) (1+ acc))
                  (loop (1+ i) acc)))))))

(define (count-prefix text prefix)
  (if (not (string? text)) 0
      (count (lambda (l) (string-prefix? prefix l)) (split-lines text))))

(define (count-lines-with text needle)
  (if (not (string? text)) 0
      (count (lambda (l) (string-contains l needle)) (split-lines text))))

(define (line-n text n)
  (and (string? text)
       (let ((ls (split-lines text)))
         (and (>= (length ls) n) (list-ref ls (1- n))))))

(define (basename path)
  (let ((i (string-rindex path #\/)))
    (if i (substring path (1+ i) (string-length path)) path)))

(define (src-code-files)
  "The buildable top-level C sources and headers of src/."
  (append (map (lambda (n) (string-append (repo "src") "/" n))
               (files-with-ext (repo "src") ".c"))
          (map (lambda (n) (string-append (repo "src") "/" n))
               (files-with-ext (repo "src") ".h"))))

(define (src-site-count)
  (let loop ((fs (src-code-files)) (acc 0))
    (if (null? fs)
        acc
        (let ((t (slurp (car fs))))
          (loop (cdr fs)
                (+ acc (count (lambda (l) (string-contains l "scm_c_public_ref"))
                              (if t (split-lines t) '()))))))))

(define (pgtk-file? name) (string-prefix? "pgtk" name))

;;; The C word census.  code-token-lines is O(file) per token, so a
;;; per-token scan of the whole tree is slow.  Strip every live
;;; buildable src/*.c file once, then answer caller queries from a
;;; word -> files index.
(define word-chars
  (string->char-set
   "_0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"))

(define (skip-line-comment text i len)
  "Return the index just past the line comment that starts at I (at the
terminating newline, which is not consumed)."
  (let loop ((j i))
    (if (or (>= j len) (char=? (string-ref text j) #\newline))
        j
        (loop (+ j 1)))))

(define (skip-c-literal text i len quote out)
  "Skip the string or char literal that opens at I and closes at QUOTE.
Emit a newline for any embedded newline.  Return the index just past the
literal."
  (let loop ((j (+ i 1)))
    (cond ((>= j len) j)
          ((char=? (string-ref text j) #\newline)
           (write-char #\newline out) (loop (+ j 1)))
          ((char=? (string-ref text j) #\\) (loop (+ j 2)))
          ((char=? (string-ref text j) quote) (+ j 1))
          (else (loop (+ j 1))))))

(define (strip-c-literals text)
  "Replace C comments, string literals and char literals in TEXT with
spaces, keeping the newlines.  This is the comment-blind view a
compiler sees."
  (if (not (string? text))
      ""
      (call-with-output-string
       (lambda (out)
         (let ((len (string-length text)))
           (define (emit c) (write-char c out))
           (let loop ((i 0) (in-block #f))
             (if (>= i len)
                 #t
                 (let ((c (string-ref text i)))
                   (cond
                    ((char=? c #\newline) (emit c) (loop (+ i 1) in-block))
                    ((and (not in-block) (char=? c #\/) (< (+ i 1) len)
                          (char=? (string-ref text (+ i 1)) #\*))
                     (emit #\space) (emit #\space) (loop (+ i 2) #t))
                    (in-block
                     (if (and (char=? c #\*) (< (+ i 1) len)
                              (char=? (string-ref text (+ i 1)) #\/))
                         (begin (emit #\space) (emit #\space) (loop (+ i 2) #f))
                         (begin (emit #\space) (loop (+ i 1) #t))))
                    ((and (char=? c #\/) (< (+ i 1) len)
                          (char=? (string-ref text (+ i 1)) #\/))
                     (loop (skip-line-comment text i len) in-block))
                    ((char=? c #\")
                     (emit #\space)
                     (loop (skip-c-literal text i len #\" out) in-block))
                    ((char=? c #\')
                     (emit #\space)
                     (loop (skip-c-literal text i len #\' out) in-block))
                    (else (emit c) (loop (+ i 1) in-block)))))))))))

;; token -> list of live buildable src/*.c basenames where token appears
;; as a whole code word on a line that does not start with DEFUN (a DEFUN
;; line registers the subr; it is not a caller).  The unbuilt pgtk*.c
;; files and the headers are excluded (cr.org F5/F7).
(define code-word-files
  (let ((h (make-hash-table)))
    (for-each
     (lambda (f)
       (let ((b (basename f)))
         (if (and (string-suffix? ".c" b) (not (pgtk-file? b)))
             (for-each
              (lambda (line)
                (if (not (string-prefix? "DEFUN" (string-trim line)))
                    (for-each
                     (lambda (w)
                       (hash-set! h w (cons b (hash-ref h w '()))))
                     (string-tokenize line word-chars))))
              (split-lines (strip-c-literals (slurp f)))))))
     (src-code-files))
    h))

(define (live-code-callers token)
  "Names of the live buildable src/*.c files that call TOKEN in code.
The unbuilt pgtk*.c files and the headers are excluded.  A comment, a
string literal and the DEFUN definition line are not callers (cr.org
F5/F7)."
  (delete-duplicates (hash-ref code-word-files token '())))

;;; --- Scheme comment-blind scan -------------------------------------
;;; The shim callers live in mod/emacs/*.scm.  A `;' starts a Scheme
;;; line comment, so a doc-comment mention is not a caller.
(define (scheme-code-line? line)
  (let ((s (string-trim line)))
    (and (not (string-null? s))
         (not (char=? (string-ref s 0) #\;)))))

(define (scheme-code-lines-with text token)
  "1-based line numbers of TEXT where TOKEN occurs whole in a non-comment
line.  A `;' line comment is not a caller (M36 review F4)."
  (if (not (string? text))
      '()
      (let ((ls (split-lines text)))
        (let loop ((i 0) (acc '()))
          (if (>= i (length ls))
              (reverse acc)
              (let ((l (list-ref ls i)))
                (if (and (scheme-code-line? l)
                         (pair? (code-token-lines l token)))
                    (loop (1+ i) (cons (1+ i) acc))
                    (loop (1+ i) acc))))))))

(define (scheme-code-names? text token)
  (pair? (scheme-code-lines-with text token)))

;;; --- org helpers ---------------------------------------------------
(define (stars line)
  (let loop ((i 0))
    (if (and (< i (string-length line)) (char=? (string-ref line i) #\*))
        (loop (1+ i)) i)))

(define (heading-line? line)
  (let ((n (stars line)))
    (and (> n 0)
         (< n (string-length line))
         (char=? (string-ref line n) #\space))))

(define (org-section text heading)
  "The org-mode section of TEXT introduced by the heading line that
starts with HEADING, up to the next same-or-shallower heading."
  (and (string? text)
       (let* ((ls (split-lines text))
              (level (stars heading))
              (start (list-index (lambda (l) (string-prefix? heading l)) ls)))
         (and start
              (let loop ((i (1+ start)))
                (cond
                 ((>= i (length ls))
                  (string-concatenate
                   (map (lambda (l) (string-append l "\n"))
                        (list-head (list-tail ls start) (- i start)))))
                 ((and (heading-line? (list-ref ls i))
                       (<= (stars (list-ref ls i)) level))
                  (string-concatenate
                   (map (lambda (l) (string-append l "\n"))
                        (list-head (list-tail ls start) (- i start)))))
                 (else (loop (1+ i)))))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m37-root))
    (begin (report "m37/imp3/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m37-root "."))
    (report "m37/imp3/root-bound" 'PASS))

(define kbd    (slurp (repo "src/keyboard.c")))
(define kg     (slurp (repo "src/keyboard-globals.c")))
(define kbd-x  (slurp (repo "src/keyboard.x")))
(define xterm-c (slurp (repo "src/xterm.c")))
(define textconv-c (slurp (repo "src/textconv.c")))
(define emacs-c (slurp (repo "src/emacs.c")))
(define gobble-scm (slurp (repo "mod/emacs/gobble.scm")))
(define xterm-scm (slurp (repo "mod/emacs/xterm.scm")))

;;; --- 1. The surface anchors (imp-3 changes no C file) --------------
(if (not kbd)
    (report "m37/imp3/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m37/imp3/count/keyboard.c-lines" 11221 (count-substr kbd "\n"))
      (check "m37/imp3/count/keyboard.c-defuns" 446 (count-prefix kbd "DEFUN (\""))
      (check "m37/imp3/count/keyboard.c-shims" 420 (count-prefix kbd "DEFUN (\"--"))))
(if (not kg)
    (report "m37/imp3/scan/keyboard-globals.c" (cons 'FAIL "missing"))
    (check "m37/imp3/count/keyboard-globals.c-lines" 490 (count-substr kg "\n")))
(define combined (+ (count-substr kbd "\n") (count-substr kg "\n")))
(check "m37/imp3/count/combined-lines" 11711 combined)
(check "m37/imp3/count/scm-c-public-ref-sites" 159 (src-site-count))

;;; --- 2. The budget ------------------------------------------------
(check "m37/imp3/budget/under-11960" #t (<= combined 11960))
(info "m37/imp3/budget/margin" (- 11960 combined))

;;; --- 3. Verdict Q1: the ring stays C, seven consumers -------------
;;; Each row pins the named symbol at the named line.  Rows 1-3 name
;;; the consumer function at its definition line; rows 4-7 name the
;;; raw-pointer comparison.
(define (line-holds-token? text line token)
  (and (string? text)
       (let ((l (line-n text line)))
         (and l (pair? (code-token-lines l token))))))

(check "m37/imp3/ring/1/x_defer_selection_requests-905" #t
       (line-holds-token? xterm-c 905 "x_defer_selection_requests"))
(check "m37/imp3/ring/2/x_delete_selection_requests-31826" #t
       (line-holds-token? xterm-c 31826 "x_delete_selection_requests"))
(check "m37/imp3/ring/3/x_find_monitors_changed_event-18660" #t
       (line-holds-token? xterm-c 18660 "x_find_monitors_changed_event"))
(check "m37/imp3/ring/4/textconv-591-kbd_fetch_ptr" #t
       (line-holds-token? textconv-c 591 "kbd_fetch_ptr"))
(check "m37/imp3/ring/5/textconv-1607-kbd_fetch_ptr" #t
       (line-holds-token? textconv-c 1607 "kbd_fetch_ptr"))
(check "m37/imp3/ring/6/textconv-1716-kbd_store_ptr" #t
       (line-holds-token? textconv-c 1716 "kbd_store_ptr"))
(check "m37/imp3/ring/7/emacs-2829-kbd_fetch_ptr" #t
       (line-holds-token? emacs-c 2829 "kbd_fetch_ptr"))
;;; The storage proof: the raw union move.  These two memmove calls are
;;; the reason the ring stays C (brief.org §3.3).
(check "m37/imp3/ring/memmove-31848" #t
       (contains? (line-n xterm-c 31848) "memmove (kbd_buffer + 1, kbd_buffer"))
(check "m37/imp3/ring/memmove-31856" #t
       (contains? (line-n xterm-c 31856) "memmove (kbd_fetch_ptr + 1, kbd_fetch_ptr"))

;;; --- 4. Verdict Q2: the decision owners live in Scheme -------------
;;; Each owner is defined in a Scheme module at its line.  Pin the name
;;; in code (a `;' comment does not count).
(check "m37/imp3/readpath/owner/gobble-input!-180" #t
       (and gobble-scm
            (let ((l (line-n gobble-scm 180)))
              (and l (scheme-code-line? l)
                   (pair? (code-token-lines l "gobble-input!"))))))
(check "m37/imp3/readpath/owner/tty-read-avail-input!-234" #t
       (and gobble-scm
            (let ((l (line-n gobble-scm 234)))
              (and l (scheme-code-line? l)
                   (pair? (code-token-lines l "tty-read-avail-input!"))))))
(check "m37/imp3/readpath/owner/x-input-pending?-80" #t
       (and xterm-scm
            (let ((l (line-n xterm-scm 80)))
              (and l (scheme-code-line? l)
                   (pair? (code-token-lines l "x-input-pending?"))))))
;;; The owners are defined, not just mentioned: each keeps a Scheme
;;; definition line in its module.
(check "m37/imp3/readpath/owner/gobble-input!-defined" #t
       (pair? (scheme-code-lines-with gobble-scm "(define (gobble-input!")))
(check "m37/imp3/readpath/owner/tty-read-avail-input!-defined" #t
       (pair? (scheme-code-lines-with gobble-scm "(define (tty-read-avail-input!")))
(check "m37/imp3/readpath/owner/x-input-pending?-defined" #t
       (pair? (scheme-code-lines-with xterm-scm "(define (x-input-pending?")))

;;; --- 5. The empty reclaim set: the five read-path shims -----------
;;; Each shim keeps a definition, a live Scheme caller at the recorded
;;; line, and a keyboard.x registration.  It also has no C caller in
;;; any live buildable src/*.c file.  So neither condition of the
;;; dead-shim rule (no Scheme caller AND no C caller) holds, and no
;;; shim is dead.  The checks are whole-token and comment-blind.
(define (shim-definition-present? name)
  (>= (count-prefix kbd (string-append "DEFUN (\"" name "\"")) 1))

(define (shim-registered? name)
  (contains? kbd-x (string-append "defsubr (\"" name "\"")))

(define (c-symbol-of shim-name)
  "The C symbol of a --=-shim: drop the leading '--', turn the dashes
into underscores, and prefix 'F'.  A C caller calls this symbol, not the
DEFUN name string (cr.org F7).  For example
--terminal-read-socket-hook-p -> Fterminal_read_socket_hook_p."
  (string-append
   "F"
   (list->string
    (map (lambda (c) (if (char=? c #\-) #\_ c))
         (string->list (string-drop shim-name 2))))))

(define (check-shim name module line)
  ;; The check name includes the module, because --pending-signals-p is
  ;; a live caller in two modules.  A duplicate ERT test name would
  ;; make the harness abort, so every name must be unique.
  (let ((label (string-append "m37/imp3/shim/"
                              (string-drop-right module 4) "/" name)))
    (check (string-append label "/definition") #t
           (shim-definition-present? name))
    (check (string-append label "/registered-keyboard.x") #t
           (shim-registered? name))
    (let ((mod (slurp (repo (string-append "mod/emacs/" module)))))
      (check (string-append label "/module-names-in-code") #t
             (and mod (scheme-code-names? mod name)))
      (check (string-append label "/caller-line") #t
             (and mod
                  (let ((l (line-n mod line)))
                    (and l
                         (scheme-code-line? l)
                         (pair? (code-token-lines l name)))))))
    ;; A dead shim needs no Scheme caller AND no C caller.  The checks
    ;; above prove the first condition.  This proves the second too: no
    ;; live buildable src/*.c file calls the shim.  The DEFUN name never
    ;; appears as a C caller (it is a string literal, which the scanner
    ;; skips), so scan for the C symbol F<name> as well (cr.org F7).
    (check (string-append label "/no-c-code-caller") '()
           (live-code-callers name))
    (check (string-append label "/no-c-symbol-caller") '()
           (live-code-callers (c-symbol-of name)))))

(for-each (lambda (row) (apply check-shim row))
          '(("--terminal-read-socket-hook-p" "gobble.scm" 202)
            ("--terminal-read-socket-hook!" "gobble.scm" 210)
            ("--frame-make-pointer-visible!" "gobble.scm" 221)
            ("--pending-signals-set!"       "gobble.scm" 229)
            ("--pending-signals-p"          "process-wait.scm" 93)
            ("--pending-signals-p"          "process-error.scm" 94)))

;;; The five shims share one registration block in src/keyboard.x.  Pin
;;; the block by scanning for the five defsubr rows in a small window,
;;; so a new row above the block does not fail the check (cr.org F9).
(define registration-names
  '("--terminal-read-socket-hook-p" "--terminal-read-socket-hook!"
    "--frame-make-pointer-visible!" "--pending-signals-set!"
    "--pending-signals-p"))
(define (keyboard-x-defsubr-line name)
  (let loop ((ls (split-lines kbd-x)) (n 1))
    (cond ((null? ls) #f)
          ((contains? (car ls) (string-append "defsubr (\"" name "\"")) n)
          (else (loop (cdr ls) (1+ n))))))
(let ((lines (filter-map keyboard-x-defsubr-line registration-names)))
  (check "m37/imp3/shim/registration-block" #t
         (and (= (length lines) (length registration-names))
              (<= (- (apply max lines) (apply min lines)) 8)))
  (info "m37/imp3/shim/registration-block-first-line"
        (or (keyboard-x-defsubr-line "--terminal-read-socket-hook-p") 0)))

;;; --- 6. The kept remnant (§4 of the plan) -------------------------
(check "m37/imp3/keep/gobble_input-6693" #t
       (contains? (line-n kbd 6693) "gobble_input (void)"))
(check "m37/imp3/keep/kbd_buffer_store_event-3782" #t
       (contains? (line-n kbd 3782) "kbd_buffer_store_event (register struct input_event *event)"))
(check "m37/imp3/keep/detect_input_pending_ignore_squeezables-9218" #t
       (contains? (line-n kbd 9218) "detect_input_pending_ignore_squeezables (void)"))

;;; --- 7. Static: registered in the keyboard group ------------------
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
       (imp2-idx (and rt-lines
                      (line-index-with rt-lines
                                       "\"test/keyboard/test-m37-imp2.el\"")))
       (reg-idx (and rt-lines
                     (line-index-with rt-lines
                                      "\"test/keyboard/test-m37-imp3.el\""))))
  (check "m37/imp3/run-tests.scm/registers-el" #t
         (and (string? run-tests)
              (and reg-idx
                   (contains? (list-ref rt-lines reg-idx)
                              "\"test/keyboard/test-m37-imp3.el\""))
              (and kg-end
                   (< kg-start reg-idx)
                   (< reg-idx kg-end))))
  (check "m37/imp3/run-tests.scm/after-imp2-row" #t
         (and imp2-idx reg-idx (< imp2-idx reg-idx))))

;;; --- 8. The accounting: docs/kb.org ** M37 (untracked) ------------
;;; The close-out record must carry the close-out hash, the status line,
;;; and the real gate result (cr.org F6).  A substring-only scan would
;;; pass while the numbers and the status field were wrong.
(define kb (slurp (repo "docs/kb.org")))
(if (not kb)
    (info "m37/imp3/kb.org/skipped" "docs/kb.org absent (untracked)")
    (let ((kb-m37 (org-section kb "** M37")))
      (if (not kb-m37)
          (report "m37/imp3/kb.org/section" (cons 'FAIL "no ** M37 section"))
          (begin
            (check "m37/imp3/kb.org/close-out-recorded" #t
                   (contains? kb-m37 "imp-3 close-out"))
            (check "m37/imp3/kb.org/verdict-stays-c" #t
                   (contains? kb-m37 "stays C"))
            (check "m37/imp3/kb.org/remnant-named" #t
                   (contains? kb-m37 "kbd_buffer_store_event"))
            ;; F5: the entry itself (not just the paragraph) must be closed.
            (check "m37/imp3/kb.org/status-closed" #t
                   (contains? kb-m37 "status :: closed"))
            (check "m37/imp3/kb.org/summary-closed" #t
                   (contains? kb-m37 "CLOSED (imp-3 close-out"))
            ;; F6: pin the close-out hash.
            (check "m37/imp3/kb.org/close-out-hash" #t
                   (contains? kb-m37 "973983f"))
            ;; F1/F2: the gate is not green, and the deterministic ERT
            ;; failures are named as real failures, not as hidden noise.
            (check "m37/imp3/kb.org/gate-not-green" #t
                   (contains? kb-m37 "not green"))
            (check "m37/imp3/kb.org/ert-failures-named" #t
                   (and (contains? kb-m37 "m29-imp5/kbd:no-dropped-token")
                        (contains? kb-m37 "m29-imp6/kbd:no-dropped-token")))
            ;; F3/F4: the order-dependent leak set, and the no-owner verdict.
            (check "m37/imp3/kb.org/leak-device-named" #t
                   (contains? kb-m37 "last-event-device"))
            (check "m37/imp3/kb.org/leak-set-varies" #t
                   (contains? kb-m37 "varies by run"))
            (check "m37/imp3/kb.org/leak-owner-verdict" #t
                   (contains? kb-m37 "leak has no single owner"))))))

;;; --- 8b. The other three records (criterion 6) --------------------
;;; Criterion 6 asks for four records.  Each skips with an INFO line
;;; when the untracked file is absent.
(let ((a (slurp (repo "docs/arch.org"))))
  (if a
      (check "m37/imp3/doc/arch.org/m37-close" #t
             (and (contains? a "M37 close")
                  (contains? a "no architecture change")))
      (info "m37/imp3/doc/arch.org/skipped" "docs/arch.org absent")))
(let ((o (slurp (repo "docs/milestone-overview.org"))))
  (if o
      (check "m37/imp3/doc/milestone-overview/m37-closed" #t
             (and (contains? o "M37") (contains? o "CLOSED 2026-09-16")))
      (info "m37/imp3/doc/milestone-overview/skipped" "absent")))
;; milestone.org is the LIVE tracker: a later milestone rewrite replaces
;; the M37 text.  Same guard as test-m35-imp3.scm:542 (brief.org §7):
;; pin the close-out anchor only while milestone.org still tracks M37.
(define (tracks-milestone? text tag)
  "True when TEXT's first org heading starts with TAG (e.g. \"* M37\")."
  (and (string? text)
       (let ((ls (split-lines text)))
         (and (pair? ls) (string-prefix? tag (car ls))))))
(let ((m (slurp (repo "milestone.org"))))
  (cond
   ((not m)
    (info "m37/imp3/doc/milestone.org/skipped" "milestone.org absent"))
   ((not (tracks-milestone? m "* M37"))
    (info "m37/imp3/doc/milestone.org/skipped"
          "milestone.org no longer tracks M37 (live tracker)"))
   (else
    (check "m37/imp3/doc/milestone.org/close-out" #t
           (and (contains? m "M37 is CLOSED")
                (contains? m "973983f"))))))

;;; --- 9. Drift guard: the sibling corpora carry the anchors -------
;;; The checks prove only that the sibling corpus FILES contain the
;;; anchor strings.  Live greenness is proven by the keyboard gate.
(define imp1 (slurp (repo "test/keyboard/test-m37-imp1.scm")))
(define imp2 (slurp (repo "test/keyboard/test-m37-imp2.scm")))
(check "m37/imp3/prior/imp1-present" #t
       (contains? imp1 "m37/imp1/keep/nr-minus-2-line-6640"))
(check "m37/imp3/prior/imp2-present" #t
       (contains? imp2 "m37/imp2/keep/gobble_input-6693"))
