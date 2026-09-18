;;; test-m36-imp5.scm --- M36 imp-5: the close-out audit corpus.
;;;
;;; brief.org (M36 imp-5) is the close-out.  It re-measures the combined
;;; C surface, runs the gate set, proves the seven retirements, records
;;; every unbuilt NS-only and PGTK-only caller, and marks M36 closed.
;;; imp-5 changes no C file and no Scheme module.  This corpus pins the
;;; close-out so the claims are checked automatically.
;;;
;;; Checks (brief.org 6):
;;;    1. The repo root is bound by the wrapper (%m36-root).
;;;    2. The brief.org 4 surface anchors hold: keyboard.c 11,221 lines,
;;;       keyboard-globals.c 490, combined 11,711, 446 DEFUNs, 420
;;;       --=-shims, 162 scm_c_public_ref sites (159 until M39,
;;;       cr.org F1), 70 in keyboard.c.
;;;    3. The budget: combined <= 11,960.  The margin is printed as INFO.
;;;    4. The seven retirements: swallow_events, timer_check, pop_kboard,
;;;       detect_input_pending, detect_input_pending_run_timers,
;;;       safe_run_hooks, gen_help_event.  Each has no definition in
;;;       keyboard.c, no extern in keyboard.h or lisp.h, and no live
;;;       buildable C caller.  A comment is not a caller.  pgtk*.c is
;;;       unbuilt, so it is not a live caller.
;;;    5. Criterion 4: gobble_input and kbd_buffer_store_event keep the
;;;       *final remnant* verdict and each keeps a live caller (checked
;;;       with the comment-blind whole-token scan); the whole-tree scan
;;;       finds no caller of detect_input_pending_ignore_squeezables, so
;;;       it keeps its keyboard.c:9218 definition and its lisp.h:4621
;;;       extern.
;;;    6. Criterion 3: no --=-shim that a retirement orphaned remains.
;;;    7. The unbuilt NS-only and PGTK-only callers.  HAVE_NS and
;;;       HAVE_PGTK are undefined in src/config.h.
;;;    8. tool/run-tests.scm registers test/keyboard/test-m36-imp5.el in
;;;       the keyboard group, after the m36-imp4 row.
;;;    9. Drift guard: the sibling corpora carry the retired-state
;;;       anchors.  The m36 and keyboard gates prove live greenness.
;;;   10. The two live comment anchors stay current: src/xdisp.c:582 and
;;;       src/keyboard.c:3896.
;;;   11. The accounting: docs/kb.org ** M36, docs/milestone-overview.org
;;;       §M36, and milestone.org.  docs/ is untracked, so an absent doc
;;;       prints an INFO line and skips the check, it does not fail it.
;;;
;;; All checks read files, so the corpus needs no C entry point and is
;;; batch-safe.
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

(define (code-token-lines text token)
  "Return the 1-based line numbers of TEXT where TOKEN occurs as a whole
token in code (outside a C comment, a string, or a character literal).
This is the whole-token scan with comment blindness: it matches `rg' on
the source lines that a compiler would see.  The line count survives
multi-line block comments and strings."
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
character literal.  This is the whole-token scan with comment blindness:
it matches `rg' on the source lines that a compiler would see."
  (pair? (code-token-lines text token)))

(define (code-callers text token)
  "Return the 1-based line numbers of TEXT where TOKEN appears in code on
a line that does not define TOKEN.  A C function definition starts the
line; a call site is indented.  So this returns the call sites only and
excludes the definition and every comment."
  (if (not (string? text))
      '()
      (let ((ls (split-lines text)))
        (filter (lambda (ln)
                  (not (string-prefix? token (list-ref ls (1- ln)))))
                (code-token-lines text token)))))

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

(define (count-lines-with text needle)
  "Number of lines of TEXT that contain NEEDLE."
  (if (not (string? text)) 0
      (count (lambda (l) (string-contains l needle)) (split-lines text))))

(define (line-n text n)
  "Return the 1-based Nth line of TEXT, or #f."
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
  "grep -rn 'scm_c_public_ref' src/*.c src/*.h | wc -l"
  (let loop ((fs (src-code-files)) (acc 0))
    (if (null? fs)
        acc
        (let ((t (slurp (car fs))))
          (loop (cdr fs)
                (+ acc (count (lambda (l) (string-contains l "scm_c_public_ref"))
                              (if t (split-lines t) '()))))))))

(define (pgtk-file? name)
  "True when NAME is an unbuilt PGTK source (pgtk*.c)."
  (string-prefix? "pgtk" name))

(define (live-code-callers token)
  "Names of the live buildable src/*.c files that call TOKEN in code.
The unbuilt pgtk*.c files and the headers are excluded.  A comment and
the definition line are not callers, so keyboard.c (the definition site)
is scanned too (cr.org F5): a lone definition does not count as a caller."
  (map basename
       (filter (lambda (f)
                 (let ((b (basename f)))
                   (and (string-suffix? ".c" b)
                        (not (pgtk-file? b))
                        (pair? (code-callers (slurp f) token)))))
               (src-code-files))))

(define (code-files-naming token)
  "Names of every src/*.c file that names TOKEN in code, comments blind."
  (map basename
       (filter (lambda (f) (contains-token-in-code? (slurp f) token))
               (src-code-files))))

(define (comma-format n)
  "Format integer N with thousands separators: 11711 -> \"11,711\"."
  (let* ((s (number->string n))
         (len (string-length s)))
    (let loop ((i len) (acc ""))
      (if (<= i 0)
          acc
          (let ((start (max 0 (- i 3))))
            (loop start
                  (string-append (substring s start i)
                                 (if (string=? acc "") "" ",")
                                 acc)))))))

;;; --- doc helpers (m35 imp-3 corpus) -------------------------------
(define (paragraphs text)
  "Split TEXT into paragraphs: each is a list of consecutive non-blank
lines.  A blank line separates paragraphs."
  (if (not (string? text))
      '()
      (let loop ((lines (split-lines text)) (cur '()) (acc '()))
        (cond ((null? lines)
               (reverse (if (null? cur) acc (cons (reverse cur) acc))))
              ((string-null? (string-trim (car lines)))
               (loop (cdr lines) '() (if (null? cur) acc (cons (reverse cur) acc))))
              (else (loop (cdr lines) (cons (car lines) cur) acc))))))

(define (paragraph-naming text token)
  "Return the first paragraph of TEXT that contains TOKEN, joined with
newlines, or #f.  A value must sit in the paragraph that names the
metric, not merely anywhere in the section."
  (let loop ((ps (paragraphs text)))
    (cond ((null? ps) #f)
          ((string-contains (string-join (car ps) "\n") token)
           (string-join (car ps) "\n"))
          (else (loop (cdr ps))))))

(define (doc-metric label section key name value)
  "Check that some paragraph of SECTION names NAME and also holds VALUE.
A value must sit in the paragraph that names the metric, so a value in
unrelated prose does not pass (cr.org F2).  All paragraphs are searched,
because a section may record a start state and a close-out state, and the
close-out value must appear in a paragraph that names the metric."
  (check (string-append label "/" key) #t
         (and (string? section)
              (any (lambda (p)
                     (let ((s (string-join p "\n")))
                       (and (string-contains s name)
                            (string-contains s value))))
                   (paragraphs section))
              #t)))

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
  "Return the org-mode section of TEXT introduced by the heading line
that starts with HEADING, up to the next heading at the same or a
shallower level.  Return #f when the heading is absent."
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

(define (tracks-milestone? text tag)
  "True when TEXT's first org heading starts with TAG."
  (and (string? text)
       (let ((ls (split-lines text)))
         (and (pair? ls) (string-prefix? tag (car ls))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m36-root))
    (begin (report "m36/imp5/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m36-root "."))
    (report "m36/imp5/root-bound" 'PASS))

(define kbd      (slurp (repo "src/keyboard.c")))
(define kg       (slurp (repo "src/keyboard-globals.c")))
(define kbd-h    (slurp (repo "src/keyboard.h")))
(define lisp-h   (slurp (repo "src/lisp.h")))
(define xdisp-c  (slurp (repo "src/xdisp.c")))
(define xterm-c  (slurp (repo "src/xterm.c")))
(define pgtk-c   (slurp (repo "src/pgtkterm.c")))
(define pgtkmenu (slurp (repo "src/pgtkmenu.c")))
(define nsterm   (slurp (repo "src/nsterm.m")))
(define nsmenu   (slurp (repo "src/nsmenu.m")))
(define dbusbind (slurp (repo "src/dbusbind.c")))
(define config-h (slurp (repo "src/config.h")))

;;; --- 1. The surface anchors (brief.org 4) -------------------------
(if (not kbd)
    (report "m36/imp5/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m36/imp5/count/keyboard.c-lines" 11221
             (count-substr kbd "\n"))
      (check "m36/imp5/count/keyboard.c-defuns" 446
             (count-prefix kbd "DEFUN (\""))
      (check "m36/imp5/count/keyboard.c-shims" 420
             (count-prefix kbd "DEFUN (\"--"))
      (check "m36/imp5/count/keyboard.c-sites" 70
             (count-lines-with kbd "scm_c_public_ref"))))
(if (not kg)
    (report "m36/imp5/scan/keyboard-globals.c" (cons 'FAIL "missing"))
    (check "m36/imp5/count/keyboard-globals.c-lines" 490
           (count-substr kg "\n")))
(check "m36/imp5/count/combined-lines" 11711
       (+ (count-substr kbd "\n") (count-substr kg "\n")))
(check "m36/imp5/count/scm-c-public-ref-sites" 162
       (src-site-count))

;;; --- 2. The budget ------------------------------------------------
(define combined (+ (count-substr kbd "\n") (count-substr kg "\n")))
(check "m36/imp5/budget/under-11960" #t
       (<= combined 11960))
(info "m36/imp5/budget/margin" (- 11960 combined))

;;; --- 3. The seven retirements -------------------------------------
;;; One check per stub.  No definition in keyboard.c, no extern in
;;; keyboard.h or lisp.h, and no live buildable C caller.  The scan is
;;; whole-token and comment-blind, so a comment mention is not a caller.
(define (retirement name)
  (check (string-append "m36/imp5/retired/" name "/no-definition") #f
         (contains-token-in-code? kbd name))
  (check (string-append "m36/imp5/retired/" name "/no-extern-keyboard.h") #f
         (contains-token-in-code? kbd-h name))
  (check (string-append "m36/imp5/retired/" name "/no-extern-lisp.h") #f
         (contains-token-in-code? lisp-h name))
  (check (string-append "m36/imp5/retired/" name "/no-live-caller") '()
         (live-code-callers name)))

(for-each retirement
          '("swallow_events" "timer_check" "pop_kboard"
            "detect_input_pending" "detect_input_pending_run_timers"
            "safe_run_hooks" "gen_help_event"))

;;; --- 4. Criterion 4: the final remnant stays C --------------------
;;; gobble_input and kbd_buffer_store_event keep the *final remnant*
;;; verdict: both remain in C and each keeps a live caller.
;;; The live-caller checks are comment-blind and whole-token (cr.org F4):
;;; a doc-comment mention is not a caller.  live-code-callers scans
;;; keyboard.c too, so a caller inside the definition file counts
;;; (cr.org F5).
(check "m36/imp5/remnant/gobble-input-definition" #t
       (contains-token-in-code? kbd "gobble_input"))
(check "m36/imp5/remnant/gobble-input-live-caller" #t
       (and (member "keyboard.c" (live-code-callers "gobble_input")) #t))
(check "m36/imp5/remnant/kbd-buffer-store-event-definition" #t
       (contains-token-in-code? kbd "kbd_buffer_store_event"))
(check "m36/imp5/remnant/kbd-buffer-store-event-live-caller" #t
       (pair? (code-callers dbusbind "kbd_buffer_store_event")))
;;; detect_input_pending_ignore_squeezables does not retire.  It keeps
;;; its definition (keyboard.c:9218) and its extern (lisp.h:4621).  This
;;; is a whole-tree scan: live-code-callers now reads keyboard.c as well
;;; as every other live buildable src/*.c file (cr.org F5).  It finds no
;;; caller.
(check "m36/imp5/remnant/detect-ignore-definition-keyboard.c:9218" #t
       (contains? (line-n kbd 9218)
                  "detect_input_pending_ignore_squeezables (void)"))
(check "m36/imp5/remnant/detect-ignore-extern-lisp.h:4621" #t
       (contains? (line-n lisp-h 4621)
                  "extern bool detect_input_pending_ignore_squeezables (void);"))
(check "m36/imp5/remnant/detect-ignore-no-caller" '()
       (live-code-callers "detect_input_pending_ignore_squeezables"))

;;; --- 5. Criterion 3: no orphaned --=-shim remains -----------------
;;; A retirement may orphan a --=-shim (a shim with no caller left).
;;; imp-2 moved the three detect shim bodies to the Scheme readers;
;;; imp-3 and imp-4 orphaned none.  Assert that no shim named after a
;;; retired stub family remains in keyboard.c.
(define (shim-names text)
  (filter (lambda (l) (string-prefix? "DEFUN (\"--" l)) (split-lines text)))
(define orphan-keys
  '("swallow-events" "timer-check" "pop-kboard"
    "detect-input-pending" "safe-run-hooks" "gen-help-event"))
(define all-shims (if kbd (shim-names kbd) '()))
(define orphan-shims
  (filter (lambda (shim)
            (any (lambda (key) (string-contains shim key)) orphan-keys))
          all-shims))
(info "m36/imp5/shims/total" (length all-shims))
(check "m36/imp5/shims/no-orphan" '() orphan-shims)

;;; --- 6. The unbuilt NS-only and PGTK-only callers -----------------
(check "m36/imp5/unbuilt/have-ns-undefined" #t
       (contains? config-h "/* #undef HAVE_NS */"))
(check "m36/imp5/unbuilt/have-pgtk-undefined" #t
       (contains? config-h "/* #undef HAVE_PGTK */"))
;; timer_check -> nsmenu.m:1972
(check "m36/imp5/unbuilt/timer-check/nsmenu.m:1972" #t
       (contains? (line-n nsmenu 1972) "timer_check ()"))
;; safe_run_hooks -> nsmenu.m:204, :208; pgtkmenu.c:288, :292
(check "m36/imp5/unbuilt/safe-run-hooks/nsmenu.m:204" #t
       (contains? (line-n nsmenu 204) "safe_run_hooks (Qactivate_menubar_hook)"))
(check "m36/imp5/unbuilt/safe-run-hooks/nsmenu.m:208" #t
       (contains? (line-n nsmenu 208) "safe_run_hooks (Qmenu_bar_update_hook)"))
(check "m36/imp5/unbuilt/safe-run-hooks/pgtkmenu.c:288" #t
       (contains? (line-n pgtkmenu 288) "safe_run_hooks (Qactivate_menubar_hook)"))
(check "m36/imp5/unbuilt/safe-run-hooks/pgtkmenu.c:292" #t
       (contains? (line-n pgtkmenu 292) "safe_run_hooks (Qmenu_bar_update_hook)"))
;; gen_help_event -> nsterm.m:7710, :8007; pgtkterm.c:5520, :5801, :6037
(check "m36/imp5/unbuilt/gen-help-event/nsterm.m:7710" #t
       (contains? (line-n nsterm 7710) "gen_help_event (help_echo_string, frame,"))
(check "m36/imp5/unbuilt/gen-help-event/nsterm.m:8007" #t
       (contains? (line-n nsterm 8007) "gen_help_event (Qnil, frame, Qnil, Qnil, 0)"))
(check "m36/imp5/unbuilt/gen-help-event/pgtkterm.c:5520" #t
       (contains? (line-n pgtk-c 5520) "gen_help_event (Qnil, frame, Qnil, Qnil, 0)"))
(check "m36/imp5/unbuilt/gen-help-event/pgtkterm.c:5801" #t
       (contains? (line-n pgtk-c 5801) "gen_help_event (Qnil, frame_obj, Qnil, Qnil, 0)"))
(check "m36/imp5/unbuilt/gen-help-event/pgtkterm.c:6037" #t
       (contains? (line-n pgtk-c 6037) "gen_help_event (help_echo_string, frame,"))
;; No src/*.m file names the other four stubs.
(check "m36/imp5/unbuilt/ns-names-only-three-stubs" #t
       (equal? (sort (map basename
                          (filter (lambda (f)
                                    (any (lambda (n)
                                           (contains-token-in-code? (slurp f) n))
                                         '("swallow_events" "timer_check" "pop_kboard"
                                           "detect_input_pending"
                                           "detect_input_pending_run_timers"
                                           "safe_run_hooks" "gen_help_event")))
                                  (map (lambda (n) (string-append (repo "src") "/" n))
                                       (files-with-ext (repo "src") ".m"))))
                    string<?)
              '("nsmenu.m" "nsterm.m")))
(check "m36/imp5/unbuilt/pgtk-c-names-only-two-stubs" #t
       (equal? (sort (map basename
                          (filter (lambda (f)
                                    (any (lambda (n)
                                           (contains-token-in-code? (slurp f) n))
                                         '("swallow_events" "timer_check" "pop_kboard"
                                           "detect_input_pending"
                                           "detect_input_pending_run_timers"
                                           "safe_run_hooks" "gen_help_event")))
                                  (map (lambda (n) (string-append (repo "src") "/" n))
                                       (filter (lambda (n) (string-prefix? "pgtk" n))
                                               (files-with-ext (repo "src") ".c")))))
                    string<?)
              '("pgtkmenu.c" "pgtkterm.c")))

;;; --- 7. Static: the corpus is registered in the keyboard group ----
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
       (imp4-idx (and rt-lines
                      (line-index-with rt-lines
                                       "\"test/keyboard/test-m36-imp4.el\"")))
       (reg-idx (and rt-lines
                     (line-index-with rt-lines
                                      "\"test/keyboard/test-m36-imp5.el\""))))
  (check "m36/imp5/run-tests.scm/registers-el" #t
         (and (string? run-tests)
              (and reg-idx
                   (contains? (list-ref rt-lines reg-idx)
                              "\"test/keyboard/test-m36-imp5.el\""))
              (and kg-end
                   (< kg-start reg-idx)
                   (< reg-idx kg-end))))
  (check "m36/imp5/run-tests.scm/after-imp4-row" #t
         (and imp4-idx reg-idx (< imp4-idx reg-idx))))

;;; --- 8. Drift guard: the sibling corpora carry the anchors --------
;;; These checks prove only that the sibling corpus FILES contain the
;;; assertion-name strings.  They do not run the siblings.  Live
;;; greenness is proven by the m36 and keyboard gates instead (cr.org
;;; F6).  The checks stay as a drift guard: a sibling that drops its
;;; retired-state anchor is caught here.
(define m36-imp1 (slurp (repo "test/keyboard/test-m36-imp1.scm")))
(define m36-imp2 (slurp (repo "test/keyboard/test-m36-imp2.scm")))
(define m36-imp3 (slurp (repo "test/keyboard/test-m36-imp3.scm")))
(define m36-imp4 (slurp (repo "test/keyboard/test-m36-imp4.scm")))
(define m35-imp3 (slurp (repo "test/keyboard/test-m35-imp3.scm")))
(define m34-imp7 (slurp (repo "test/keyboard/test-m34-imp7.scm")))
(check "m36/imp5/prior/m36-imp1-swallow-retired" #t
       (contains? m36-imp1 "m36/imp1/def/swallow-events-gone"))
(check "m36/imp5/prior/m36-imp2-pop-retired" #t
       (contains? m36-imp2 "m36/imp2/cr/G2/m34-imp6-pop-retired"))
(check "m36/imp5/prior/m36-imp3-safe-run-hooks-retired" #t
       (contains? m36-imp3 "m36/imp3/prior/m35-imp2-def-retired"))
(check "m36/imp5/prior/m36-imp4-gen-help-event-retired" #t
       (contains? m36-imp4 "m36/imp4/code/gen-help-event-def-gone"))
(check "m36/imp5/prior/m35-imp3-gen-help-event-retired" #t
       (contains? m35-imp3 "m35/imp3/keep/gen-help-event/retired"))
(check "m36/imp5/prior/m34-imp7-gen-help-event-retired" #t
       (contains? m34-imp7 "m34/imp7/kept/gen-help-event-retired"))

;;; --- 9. The guard anchors stay current ----------------------------
;;; The two live cross-reference comment anchors.  Check the live line,
;;; not a prose phrase.
(check "m36/imp5/guard/xdisp.c:582" #t
       (contains? (line-n xdisp-c 582) "(src/xdisp.c:27788, :28574)"))
(check "m36/imp5/guard/keyboard.c:3896" #t
       (contains? (line-n kbd 3896) "(term.c:3595)"))

;;; --- 10. The accounting --------------------------------------------
;;; docs/ is untracked, so a fresh clone has no kb.org and no
;;; milestone-overview.org.  When a doc file is absent, print an INFO
;;; line; do not fail.
(define (doc-records-close-out label section)
  (doc-metric label section "keyboard.c-lines" "keyboard.c" "11,221")
  (doc-metric label section "keyboard-globals.c-lines" "keyboard-globals.c" "490")
  (doc-metric label section "combined-lines" "keyboard-globals.c" "11,711")
  (doc-metric label section "scm-c-public-ref-sites" "scm_c_public_ref" "159"))

;; cr.org F1: docs/kb.org is now the reduced ontology knowledge base (the
;; kb2 reduction).  It holds no per-milestone historical detail, only the
;; reduction's self-links.  Treat the reduced record like an absent doc
;; file: skip the historical pins, do not fail them.
(define kb (let ((f (slurp (repo "docs/kb.org"))))
             (if (and f (string-contains f "Historical detail: [[file:kb.org::"))
                 #f f)))
(if (not kb)
    (info "m36/imp5/kb.org/skipped" "docs/kb.org absent or reduced (cr.org F1)")
    (let ((kb-m36 (org-section kb "** M36")))
      (if (not kb-m36)
          (report "m36/imp5/kb.org/status-closed"
                  (cons 'FAIL "no ** M36 section in docs/kb.org"))
          (begin
            (check "m36/imp5/kb.org/status-closed" #t
                   (contains? kb-m36 "status :: closed"))
            (check "m36/imp5/kb.org/imp5-landing" #t
                   (contains? kb-m36 "imp-5 landing"))
            (doc-records-close-out "m36/imp5/kb.org/count" kb-m36)))))

(define overview (slurp (repo "docs/milestone-overview-closed.org")))
(if (not overview)
    (info "m36/imp5/overview/skipped"
          "docs/milestone-overview-closed.org absent (untracked)")
    (let ((ov-m36 (org-section overview "*** M36")))
      (if (not ov-m36)
          (report "m36/imp5/overview/m36-closed"
                  (cons 'FAIL "no *** M36 section in the overview"))
          (begin
            (check "m36/imp5/overview/m36-closed" #t
                   (contains? ov-m36 "CLOSED"))
            (doc-records-close-out "m36/imp5/overview/count" ov-m36)))))

(define milestone (slurp (repo "milestone.org")))
(cond
 ((not milestone)
  (info "m36/imp5/milestone.org/skipped" "milestone.org absent (untracked)"))
 ((not (tracks-milestone? milestone "* M36"))
  (info "m36/imp5/milestone.org/skipped"
        "milestone.org no longer tracks M36 (live tracker)"))
 (else
  (let ((ms-status (org-section milestone "** Status"))
        (ms-imps (org-section milestone "** Imps")))
    (check "m36/imp5/milestone.org/status-closed" #t
           (and (contains? ms-status "closed")
                (contains? ms-status "imp-5")))
    (check "m36/imp5/milestone.org/imp5-done" #t
           (and (contains? ms-imps "imp-5")
                (contains? ms-imps "DONE")))
    ;; cr.org F2: the out-of-scope note must cite keyboard.c:9218 and
    ;; must not claim a live C caller.
    (check "m36/imp5/milestone.org/detect-ignore-9218" #t
           (contains? milestone "keyboard.c:9218"))
    (check "m36/imp5/milestone.org/detect-ignore-no-c-caller-claim" #f
           (contains? milestone "keyboard.c:9257")))))
