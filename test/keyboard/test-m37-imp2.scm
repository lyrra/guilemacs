;;; test-m37-imp2.scm --- M37 imp-2: the kbd_buffer[] ring verdict.
;;;
;;; brief.org (M37 imp-2) does two jobs.  Job 1 records the Q1 verdict:
;;; the kbd_buffer[] ring STAYS C.  Job 2 reclaims the shims that imp-1
;;; orphans.  imp-1 orphaned none, so the reclaim set is empty.  This
;;; corpus proves both.
;;;
;;; The verdict rests on two proofs (brief.org §3.2):
;;;   - the C code moves the raw storage: x_delete_selection_requests
;;;     runs memmove (kbd_buffer + 1, kbd_buffer, ...) and rotates
;;;     kbd_buffer[0] (xterm.c:31848, :31856);
;;;   - the other consumers can not read a Scheme value: rows 1-3 are
;;;     raw X11 code, rows 4-6 are input-method conversion code, and
;;;     row 7 runs on the fatal_error_in_progress path and must not run
;;;     a Guile frame.
;;;
;;; Checks:
;;;    1. The repo root is bound by the wrapper (%m37-root).
;;;    2. The surface anchors are unchanged (imp-2 changes no C file):
;;;       keyboard.c 11,221 lines, 446 DEFUNs, 420 --=-shims;
;;;       keyboard-globals.c 490; combined 11,711; 162 scm_c_public_ref
;;;       sites (159 until M39, cr.org F1).  The budget is 11,960.
;;;    3. The ring verdict (§3.1): the seven consumer rows each hold
;;;       the named symbol at the named line (xterm.c:905, :31826,
;;;       :18660; textconv.c:591, :1607, :1716; emacs.c:2829).  The
;;;       memmove storage move at xterm.c:31848 and :31856 is present.
;;;    4. The kept C (§3.3): the ring cells (keyboard.c:302, :306,
;;;       :309), next_kbd_event (:380), the store site (:4776), and the
;;;       whole --kbd accessor family (from :1015 to :4752) stay C.
;;;    5. The kept remnants (§4.3): gobble_input (keyboard.c:6693) and
;;;       detect_input_pending_ignore_squeezables (:9218) stay C.
;;;    6. The reclaim proof (§4.2): each of the five imp-1 shims keeps
;;;       (a) a definition, (b) a src/keyboard.x registration, (c) a
;;;       live Scheme caller at the recorded line, and (d) no C code
;;;       caller in any live buildable src/*.c file.  A shim with a
;;;       caller is not dead, so it stays.
;;;    8. Registration: tool/run-tests.scm names
;;;       test/keyboard/test-m37-imp2.el in the keyboard group, after
;;;       the m37-imp1 row.
;;;    9. Drift guard: the sibling corpora (M34 imp-7, M36 imp-1) still
;;;       carry their anchors.
;;;
;;; (Item 7 used to check that docs/kb.org's ** M37 section carried the
;;; ring verdict.  docs/ is gitignored and not kept in sync with the
;;; git-tracked test/code work, so the check either skipped or failed on
;;; stale local docs unrelated to code correctness.  Removed; the
;;; verdict itself is still pinned by item 3 above.)
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

(define (contains-token-in-code? text token)
  "True when TOKEN occurs in TEXT outside a C comment, a string, or a
character literal.  Whole-token and comment-blind."
  (pair? (code-token-lines text token)))

(define (code-callers text token)
  "Return the 1-based line numbers of TEXT where TOKEN appears in code on
a line that does not define TOKEN (a definition starts the line)."
  (if (not (string? text))
      '()
      (let ((ls (split-lines text)))
        (filter (lambda (ln)
                  (not (string-prefix? token (list-ref ls (1- ln)))))
                (code-token-lines text token)))))

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

(define (live-code-callers token)
  "Names of the live buildable src/*.c files that call TOKEN in code.
The unbuilt pgtk*.c files and the headers are excluded.  A comment and
the definition line are not callers (cr.org F5)."
  (map basename
       (filter (lambda (f)
                 (let ((b (basename f)))
                   (and (string-suffix? ".c" b)
                        (not (pgtk-file? b))
                        (pair? (code-callers (slurp f) token)))))
               (src-code-files))))

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
    (begin (report "m37/imp2/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m37-root "."))
    (report "m37/imp2/root-bound" 'PASS))

(define kbd     (slurp (repo "src/keyboard.c")))
(define kg      (slurp (repo "src/keyboard-globals.c")))
(define kbd-x   (slurp (repo "src/keyboard.x")))
(define xterm-c (slurp (repo "src/xterm.c")))
(define textconv-c (slurp (repo "src/textconv.c")))
(define emacs-c (slurp (repo "src/emacs.c")))

;;; --- 1. The surface anchors (imp-2 changes no C file) --------------
(if (not kbd)
    (report "m37/imp2/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m37/imp2/count/keyboard.c-lines" 11221 (count-substr kbd "\n"))
      (check "m37/imp2/count/keyboard.c-defuns" 446 (count-prefix kbd "DEFUN (\""))
      (check "m37/imp2/count/keyboard.c-shims" 420 (count-prefix kbd "DEFUN (\"--"))))
(if (not kg)
    (report "m37/imp2/scan/keyboard-globals.c" (cons 'FAIL "missing"))
    (check "m37/imp2/count/keyboard-globals.c-lines" 490 (count-substr kg "\n")))
(define combined (+ (count-substr kbd "\n") (count-substr kg "\n")))
(check "m37/imp2/count/combined-lines" 11711 combined)
(check "m37/imp2/count/scm-c-public-ref-sites" 172 (src-site-count))

;;; --- 2. The budget ------------------------------------------------
(check "m37/imp2/budget/under-11960" #t (<= combined 11960))
(info "m37/imp2/budget/margin" (- 11960 combined))

;;; --- 3. The ring verdict: the seven consumer rows -----------------
;;; Each row pins the named symbol at the named line.  Rows 1-3 name
;;; the consumer function at its definition line; rows 4-7 name the
;;; raw-pointer comparison.
(define (line-holds-token? text line token)
  (and (string? text)
       (let ((l (line-n text line)))
         (and l (pair? (code-token-lines l token))))))

(check "m37/imp2/ring/1/x_defer_selection_requests-905" #t
       (line-holds-token? xterm-c 905 "x_defer_selection_requests"))
(check "m37/imp2/ring/2/x_delete_selection_requests-31826" #t
       (line-holds-token? xterm-c 31826 "x_delete_selection_requests"))
(check "m37/imp2/ring/3/x_find_monitors_changed_event-18660" #t
       (line-holds-token? xterm-c 18660 "x_find_monitors_changed_event"))
(check "m37/imp2/ring/4/textconv-591-kbd_fetch_ptr" #t
       (line-holds-token? textconv-c 591 "kbd_fetch_ptr"))
(check "m37/imp2/ring/5/textconv-1607-kbd_fetch_ptr" #t
       (line-holds-token? textconv-c 1607 "kbd_fetch_ptr"))
(check "m37/imp2/ring/6/textconv-1716-kbd_store_ptr" #t
       (line-holds-token? textconv-c 1716 "kbd_store_ptr"))
(check "m37/imp2/ring/7/emacs-2829-kbd_fetch_ptr" #t
       (line-holds-token? emacs-c 2829 "kbd_fetch_ptr"))

;;; The storage proof: the raw union move.  These two memmove calls are
;;; the reason the ring stays C (brief.org §3.2).
(check "m37/imp2/ring/memmove-31848" #t
       (contains? (line-n xterm-c 31848) "memmove (kbd_buffer + 1, kbd_buffer"))
(check "m37/imp2/ring/memmove-31856" #t
       (contains? (line-n xterm-c 31856) "memmove (kbd_fetch_ptr + 1, kbd_fetch_ptr"))

;;; --- 4. The kept C ring cells and accessors -----------------------
;;; The cells and next_kbd_event (brief.org §3.3).
(check "m37/imp2/keep/cell-kbd_buffer-302" #t
       (contains? (line-n kbd 302) "kbd_buffer[KBD_BUFFER_SIZE]"))
(check "m37/imp2/keep/cell-kbd_fetch_ptr-306" #t
       (contains? (line-n kbd 306) "*kbd_fetch_ptr;"))
(check "m37/imp2/keep/cell-kbd_store_ptr-309" #t
       (contains? (line-n kbd 309) "*kbd_store_ptr;"))
(check "m37/imp2/keep/next_kbd_event-380" #t
       (contains? (line-n kbd 380) "next_kbd_event (union buffered_input_event *ptr)"))
(check "m37/imp2/keep/store-site-4776" #t
       (contains? (line-n kbd 4776) "*kbd_store_ptr = ev;"))

;;; The accessor family stays C.  The raw union storage pins it (M27).
;;; Each row pins the DEFUN name at its definition line.
(define (defun-line-holds? text line name)
  (contains? (line-n text line) (string-append "DEFUN (\"" name "\"")))

(for-each
 (lambda (row)
   (let ((name (car row)) (line (cadr row)))
     (check (string-append "m37/imp2/keep/accessor/" name "/line-" (number->string line))
            #t (defun-line-holds? kbd line name))))
 '(("--kbd-fetch-ptr-index"            1015)
   ("--kbd-store-ptr-index"            1026)
   ("--kbd-buffer-nr-stored"           1035)
   ("--kbd-empty-p"                    1058)
   ("--kbd-event-kind"                 1130)
   ("--kbd-event-ie"                   1145)
   ("--kbd-advance-fetch-ptr"          1162)
   ("--kbd-set-fetch-ptr-index"        1195)
   ("--kbd-set-store-ptr-index"        1208)
   ("--kbd-handle-selection-event"     1222)
   ("--kbd-excise-selection-event-at!" 1274)
   ("--kbd-buffer-store-fake-event"    4752)))

;;; --- 5. The kept remnants (§4.3) ----------------------------------
(check "m37/imp2/keep/gobble_input-6693" #t
       (contains? (line-n kbd 6693) "gobble_input (void)"))
(check "m37/imp2/keep/detect_input_pending_ignore_squeezables-9218" #t
       (contains? (line-n kbd 9218) "detect_input_pending_ignore_squeezables (void)"))

;;; --- 6. The reclaim proof (§4.2) ----------------------------------
;;; Each imp-1 shim keeps a definition, a live Scheme caller at the
;;; recorded line, and a keyboard.x registration.  It also has no C
;;; caller in any live buildable src/*.c file.  So neither condition of
;;; the dead-shim rule (no Scheme caller AND no C caller) holds, and no
;;; shim is dead.  The checks are whole-token and comment-blind.
(define (shim-definition-present? name)
  (>= (count-prefix kbd (string-append "DEFUN (\"" name "\"")) 1))

(define (shim-registered? name)
  (contains? kbd-x (string-append "defsubr (\"" name "\"")))

(define (check-shim name module line)
  ;; The check name includes the module, because --pending-signals-p is a
  ;; live caller in two modules.  A duplicate ERT test name would make
  ;; the harness abort, so every name must be unique.
  (let ((label (string-append "m37/imp2/shim/"
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
    ;; live buildable src/*.c file calls the shim.
    (check (string-append label "/no-c-code-caller") '()
           (live-code-callers name))))

(for-each (lambda (row) (apply check-shim row))
          '(("--terminal-read-socket-hook-p" "gobble.scm" 202)
            ("--terminal-read-socket-hook!" "gobble.scm" 210)
            ("--frame-make-pointer-visible!" "gobble.scm" 221)
            ("--pending-signals-set!"       "gobble.scm" 229)
            ("--pending-signals-p"          "process-wait.scm" 97)
            ("--pending-signals-p"          "process-error.scm" 94)))

;;; --- 6b. Negative controls (cr.org F1) ----------------------------
;;; The /caller-line check must be able to fail.  A code line that does
;;; not hold the name, and a comment line, must both yield #f.  With
;;; the old trailing #t the check returned #t for any existing module,
;;; so the recorded line was not pinned.  These controls guard the fix:
;;; if the check can not fail, the corpus is a false guard.
(define gobble-scm (slurp (repo "mod/emacs/gobble.scm")))
(check "m37/imp2/shim/negative/wrong-code-line" #f
       (let ((l (line-n gobble-scm 200)))
         (and l (scheme-code-line? l)
              (pair? (code-token-lines l "--terminal-read-socket-hook-p")))))
(check "m37/imp2/shim/negative/comment-line" #f
       (scheme-code-line? ";; --pending-signals-p is used below"))
(check "m37/imp2/shim/negative/missing-module" #f
       (and (slurp (repo "mod/emacs/no-such-module.scm"))
            #t))

;;; --- 8. Static: registered in the keyboard group ------------------
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
       (imp1-idx (and rt-lines
                      (line-index-with rt-lines
                                       "\"test/keyboard/test-m37-imp1.el\"")))
       (reg-idx (and rt-lines
                     (line-index-with rt-lines
                                      "\"test/keyboard/test-m37-imp2.el\""))))
  (check "m37/imp2/run-tests.scm/registers-el" #t
         (and (string? run-tests)
              (and reg-idx
                   (contains? (list-ref rt-lines reg-idx)
                              "\"test/keyboard/test-m37-imp2.el\""))
              (and kg-end
                   (< kg-start reg-idx)
                   (< reg-idx kg-end))))
  (check "m37/imp2/run-tests.scm/after-imp1-row" #t
         (and imp1-idx reg-idx (< imp1-idx reg-idx))))

;;; --- 9. Drift guard: the sibling corpora carry the anchors -------
;;; The checks prove only that the sibling corpus FILES contain the
;;; anchor strings.  Live greenness is proven by the keyboard gate.
(define m36-imp1 (slurp (repo "test/keyboard/test-m36-imp1.scm")))
(define m34-imp7 (slurp (repo "test/keyboard/test-m34-imp7.scm")))
(check "m37/imp2/prior/m36-imp1-present" #t
       (contains? m36-imp1 "m36/imp1/def/swallow-events-gone"))
(check "m37/imp2/prior/m34-imp7-present" #t
       (contains? m34-imp7 "m34/imp7/kept/gen-help-event-retired"))
