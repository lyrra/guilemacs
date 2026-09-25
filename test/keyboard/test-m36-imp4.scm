;;; test-m36-imp4.scm --- M36 imp-4: retire gen_help_event.
;;;
;;; brief.org (M36 imp-4) retires the C stub gen_help_event.  It loses
;;; its definition, its extern, and its last live buildable C caller.
;;; The last live caller, the src/xterm.c help block in
;;; handle_one_xevent, moves its raw call into a local static dispatcher
;;; x_gen_help_event, which targets (emacs help-echo) gen-help-event.
;;; The decision already lives in (emacs xterm) x-help-event-action
;;; (M33).  The unbuilt NS and PGTK callers stay (HAVE_NS and HAVE_PGTK
;;; are undefined).
;;;
;;; This corpus pins the retirement so the claims are checked
;;; automatically and not only by hand.
;;;
;;; Checks (brief.org 8):
;;;    1. keyboard.c holds no definition of gen_help_event.
;;;    2. keyboard.h holds no extern for gen_help_event.
;;;    3. xterm.c defines the static dispatcher x_gen_help_event, keeps
;;;       the two call sites on the dispatcher, and holds exactly one
;;;       scm_c_public_ref ("emacs help-echo", "gen-help-event").
;;;    4. A whole-token, comment-blind scan of src/*.c finds no live
;;;       bare gen_help_event call outside the unbuilt pgtkterm.c.
;;;    5. The unbuilt NS and PGTK callers keep the name; HAVE_NS and
;;;       HAVE_PGTK are undefined.
;;;    6. (emacs help-echo) still exports and defines gen-help-event.
;;;    7. The brief.org 9 surface anchors hold.
;;;    8. tool/run-tests.scm registers test/keyboard/test-m36-imp4.el.
;;;    9. The prior corpora pin the new retired state.
;;;   10. cr1.org F8: a table-driven guard checks that every sibling
;;;       corpus anchor tracks the live surface.
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

(define (contains-token-in-code? text token)
  "True when TOKEN occurs in TEXT outside a C comment, a string, or a
character literal.  This is the whole-token scan with comment blindness:
it matches `rg' on source lines that a compiler would see."
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

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m36-root))
    (begin (report "m36/imp4/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m36-root "."))
    (report "m36/imp4/root-bound" 'PASS))

(define kbd    (slurp (repo "src/keyboard.c")))
(define kbd-h  (slurp (repo "src/keyboard.h")))
(define xterm-c (slurp (repo "src/xterm.c")))
(define pgtk-c (slurp (repo "src/pgtkterm.c")))
(define nsterm (slurp (repo "src/nsterm.m")))
(define config-h (slurp (repo "src/config.h")))
(define kg (slurp (repo "src/keyboard-globals.c")))
(define help-echo (slurp (repo "mod/emacs/help-echo.scm")))

;;; --- 1. No definition remains in keyboard.c -----------------------
(if (not kbd)
    (report "m36/imp4/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m36/imp4/code/gen-help-event-def-gone" #f
             (contains? kbd "gen_help_event (Lisp_Object help"))
      (check "m36/imp4/code/retirement-comment" #t
             (contains? kbd "gen_help_event retired"))))

;;; --- 2. No extern remains in the header ---------------------------
(if (not kbd-h)
    (report "m36/imp4/scan/keyboard.h" (cons 'FAIL "src/keyboard.h missing"))
    (check "m36/imp4/extern/gen-help-event-gone" #f
           (contains? kbd-h "extern void gen_help_event (")))

;;; --- 3. xterm.c holds the dispatcher and the raw call ------------
(if (not xterm-c)
    (report "m36/imp4/scan/xterm.c" (cons 'FAIL "src/xterm.c missing"))
    (begin
      (check "m36/imp4/xterm.c/dispatcher-defined" #t
             (contains? xterm-c "x_gen_help_event (Lisp_Object help, Lisp_Object frame,"))
      (check "m36/imp4/xterm.c/show-site-uses-dispatcher" #t
             (contains? xterm-c "x_gen_help_event (help_echo_string, frame,"))
      (check "m36/imp4/xterm.c/clear-site-uses-dispatcher" #t
             (contains? xterm-c "x_gen_help_event (Qnil, frame, Qnil, Qnil, 0)"))
      (check "m36/imp4/xterm.c/one-raw-ref" 1
             (count-substr xterm-c
                           "scm_c_public_ref (\"emacs help-echo\", \"gen-help-event\")"))
      (check "m36/imp4/xterm.c/bare-call-gone" #f
             (contains-token-in-code? xterm-c "gen_help_event"))))

;;; --- 4. No live buildable call outside the unbuilt pgtkterm.c -----
(define live-files
  (map basename
       (filter (lambda (fs) (contains-token-in-code? (slurp fs) "gen_help_event"))
               (src-code-files))))
(info "m36/imp4/caller/gen-help-event/code-files" live-files)
(check "m36/imp4/caller/only-unbuilt-pgtkterm" '("pgtkterm.c") live-files)

;;; --- 5. The unbuilt NS and PGTK callers keep the name -------------
(check "m36/imp4/caller/pgtkterm-sites" 3
       (+ (if (contains? pgtk-c "gen_help_event (Qnil, frame, Qnil, Qnil, 0)") 1 0)
          (if (contains? pgtk-c "gen_help_event (Qnil, frame_obj, Qnil, Qnil, 0)") 1 0)
          (if (contains? pgtk-c "gen_help_event (help_echo_string, frame,") 1 0)))
(check "m36/imp4/caller/nsterm-sites" #t
       (and (contains? nsterm "gen_help_event (help_echo_string, frame,")
            (contains? nsterm "gen_help_event (Qnil, frame, Qnil, Qnil, 0)")))
(check "m36/imp4/caller/ns-unbuilt" #t
       (contains? config-h "/* #undef HAVE_NS */"))
(check "m36/imp4/caller/pgtk-unbuilt" #t
       (contains? config-h "/* #undef HAVE_PGTK */"))

;;; --- 6. (emacs help-echo) still exports and defines gen-help-event --
(if (not help-echo)
    (report "m36/imp4/scan/help-echo.scm" (cons 'FAIL "module missing"))
    (begin
      (check "m36/imp4/module/defines-gen-help-event" #t
             (contains? help-echo "(define (gen-help-event help frame window object pos)"))
      (check "m36/imp4/module/exports-gen-help-event" #t
             (contains? help-echo "gen-help-event"))))

;;; --- 7. The brief.org 9 surface anchors hold ----------------------
(if (not kbd)
    (report "m36/imp4/scan/keyboard.c-counts" (cons 'FAIL "missing"))
    (begin
      (check "m36/imp4/count/keyboard.c-lines" 11221
             (count-substr kbd "\n"))
      (check "m36/imp4/count/keyboard.c-defuns" 446
             (count-prefix kbd "DEFUN (\""))
      (check "m36/imp4/count/keyboard.c-shims" 420
             (count-prefix kbd "DEFUN (\"--"))))
(info "m36/imp4/count/keyboard-globals.c-lines" (count-substr kg "\n"))
(check "m36/imp4/count/combined-lines" 11711
       (+ (count-substr kbd "\n") (count-substr kg "\n")))
(check "m36/imp4/count/under-budget" #t
       (<= (+ (count-substr kbd "\n") (count-substr kg "\n")) 11960))
(check "m36/imp4/count/scm-c-public-ref-sites" 174
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
                                      "\"test/keyboard/test-m36-imp4.el\""))))
  (check "m36/imp4/run-tests.scm/registers-el" #t
         (and (string? run-tests)
              (and reg-idx
                   (contains? (list-ref rt-lines reg-idx)
                              "\"test/keyboard/test-m36-imp4.el\""))
              (and kg-end
                   (< kg-start reg-idx)
                   (< reg-idx kg-end)))))

;;; --- 9. The prior corpora pin the new retired state ---------------
(define m33-imp3 (slurp (repo "test/keyboard/test-m33-imp3.scm")))
(define m34-imp7 (slurp (repo "test/keyboard/test-m34-imp7.scm")))
(define m35-imp2 (slurp (repo "test/keyboard/test-m35-imp2.scm")))
(define m35-imp3 (slurp (repo "test/keyboard/test-m35-imp3.scm")))
(check "m36/imp4/prior/m33-imp3-retired" #t
       (contains? m33-imp3 "m33/imp3/keyboard.c/gen-help-event-retired"))
(check "m36/imp4/prior/m34-imp7-retired" #t
       (contains? m34-imp7 "m34/imp7/kept/gen-help-event-retired"))
(check "m36/imp4/prior/m35-imp2-def-retired" #t
       (contains? m35-imp2 "m35/imp2/def/gen-help-event-retired"))
(check "m36/imp4/prior/m35-imp2-keep-retired" #t
       (contains? m35-imp2 "m35/imp2/keep/gen-help-event/retired"))
(check "m36/imp4/prior/m35-imp3-keep-retired" #t
       (contains? m35-imp3 "m35/imp3/keep/gen-help-event/retired"))

;;; --- 10. cr1.org F8: the sibling anchors track the live surface ----
;;; The milestone re-pins the surface at each imp, and that step was
;;; missed twice (cr1.org F1, and the older cr/G1 note).  This guard
;;; reads the live-count anchor out of each sibling corpus and compares
;;; it with the live tree, so a later surface move cannot leave a corpus
;;; behind.  It covers the three anchors that the milestone re-pins:
;;; keyboard.c lines, combined lines, and scm_c_public_ref sites.  The
;;; M35 doc-record anchors (comma-format) are history and are not read.
(define (first-int text)
  "The first run of digits in TEXT as a number, or #f."
  (let loop ((chars (string->list text)))
    (cond ((null? chars) #f)
          ((char-numeric? (car chars))
           (let scan ((cs chars) (acc '()))
             (if (and (pair? cs) (char-numeric? (car cs)))
                 (scan (cdr cs) (cons (car cs) acc))
                 (string->number (list->string (reverse acc))))))
          (else (loop (cdr chars))))))

(define (anchor-int text token)
  "The integer pinned by the first (check ... TOKEN) line of TEXT, or #f.
A line must hold both \"(check\" and TOKEN, so a doc-record or a
doc-metric line does not match."
  (if (not (string? text))
      #f
      (let loop ((lines (split-lines text)))
        (cond ((null? lines) #f)
              ((and (string-contains (car lines) "(check")
                    (string-contains (car lines) token))
               (let ((i (string-contains (car lines) token)))
                 (first-int (substring (car lines)
                                       (+ i (string-length token))
                                       (string-length (car lines))))))
              (else (loop (cdr lines)))))))

(define live-kbd-lines (count-substr kbd "\n"))
(define live-combined (+ (count-substr kbd "\n") (count-substr kg "\n")))
(define live-sites (src-site-count))

(define (guard-sibling label path)
  (let ((text (slurp path)))
    (check (string-append "m36/imp4/guard/" label "/keyboard.c-lines")
           live-kbd-lines (anchor-int text "count/keyboard.c-lines"))
    (check (string-append "m36/imp4/guard/" label "/combined-lines")
           live-combined (anchor-int text "count/combined-lines"))
    (check (string-append "m36/imp4/guard/" label "/scm-c-public-ref-sites")
           live-sites (anchor-int text "count/scm-c-public-ref-sites"))))

(guard-sibling "m36-imp1" (repo "test/keyboard/test-m36-imp1.scm"))
(guard-sibling "m36-imp2" (repo "test/keyboard/test-m36-imp2.scm"))
(guard-sibling "m36-imp3" (repo "test/keyboard/test-m36-imp3.scm"))
(guard-sibling "m35-imp3" (repo "test/keyboard/test-m35-imp3.scm"))
