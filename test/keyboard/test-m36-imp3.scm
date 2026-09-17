;;; test-m36-imp3.scm --- M36 imp-3: retire safe_run_hooks.
;;;
;;; brief.org (M36 imp-3) retires the C stub safe_run_hooks.  It loses
;;; its definition, its extern, and its live buildable C caller.  The
;;; decision moves into (emacs command-loop); the C keeps the mechanism
;;; and a static dispatcher local to each caller file.  The unbuilt NS
;;; and PGTK callers stay (HAVE_NS / HAVE_PGTK are undefined).
;;;
;;; This corpus pins the retirement so the claims are checked
;;; automatically and not only by hand.
;;;
;;; Checks (brief.org 8):
;;;    1. keyboard.c holds no definition of safe_run_hooks.
;;;    2. lisp.h holds no extern for safe_run_hooks.
;;;    3. A whole-token, comment-blind scan of src/*.c and src/*.h
;;;       finds no live call outside the unbuilt pgtkmenu.c.
;;;    4. (emacs command-loop) exports and defines the two new
;;;       procedures; no Scheme #f remains in the bodies.
;;;    5. Each caller file keeps its static dispatcher and calls the
;;;       module proc; the live .c call is gone.
;;;    6. The stale comment at keyboard.c:11197 is repaired.
;;;    7. gobble_input, kbd_buffer_store_event, and
;;;       detect_input_pending_ignore_squeezables are untouched.
;;;    8. The brief.org 9 surface anchors hold.
;;;    9. tool/run-tests.scm registers test/keyboard/test-m36-imp3.el.
;;;   10. The prior corpora pin the new retired state.
;;;   11. cr.org F2: the pgtk.scm note no longer names the dead
;;;       --detect-input-pending shim.
;;;   12. cr1.org F1: the sibling count anchors track the live
;;;       scm_c_public_ref site count.
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
    (begin (report "m36/imp3/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m36-root "."))
    (report "m36/imp3/root-bound" 'PASS))

(define kbd   (slurp (repo "src/keyboard.c")))
(define lisp-h (slurp (repo "src/lisp.h")))
(define emacs-c (slurp (repo "src/emacs.c")))
(define xmenu-c (slurp (repo "src/xmenu.c")))
(define pgtkmenu-c (slurp (repo "src/pgtkmenu.c")))
(define config-h (slurp (repo "src/config.h")))
(define kg (slurp (repo "src/keyboard-globals.c")))
(define cl-scm (slurp (repo "mod/emacs/command-loop.scm")))
(define pgtk-scm (slurp (repo "mod/emacs/pgtk.scm")))

;;; --- 1. No definition remains in keyboard.c -----------------------
(if (not kbd)
    (report "m36/imp3/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m36/imp3/code/safe-run-hooks-gone" #f
             (contains? kbd "safe_run_hooks (Lisp_Object hook)"))
      ;; The shared echo-area dispatcher is present, not a bare token.
      (check "m36/imp3/code/echo-dispatcher-defined" #t
             (contains? kbd "kbd_run_echo_area_clear_hook (void)"))))

;;; --- 2. No extern remains in the header ---------------------------
(if (not lisp-h)
    (report "m36/imp3/scan/lisp.h" (cons 'FAIL "src/lisp.h missing"))
    (check "m36/imp3/extern/safe-run-hooks-gone" #f
           (contains? lisp-h "extern void safe_run_hooks (Lisp_Object)")))

;;; --- 3. No live buildable C caller remains ------------------------
;;; The unbuilt pgtkmenu.c keeps a live call.  nsmenu.m is NS (.m).
(define (code-token-files token)
  (filter (lambda (fs) (contains-token-in-code? (slurp fs) token))
          (src-code-files)))
(define live-files (map basename (code-token-files "safe_run_hooks")))
(info "m36/imp3/caller/safe-run-hooks/code-files" live-files)
(check "m36/imp3/caller/only-unbuilt-pgtkmenu" '("pgtkmenu.c") live-files)
(check "m36/imp3/caller/pgtk-unbuilt" #t
       (contains? config-h "/* #undef HAVE_PGTK */"))

;;; --- 4. (emacs command-loop) exports and defines the new procs -----
(if (not cl-scm)
    (report "m36/imp3/scan/command-loop.scm" (cons 'FAIL "module missing"))
    (begin
      (check "m36/imp3/module/exports-echo" #t
             (contains? cl-scm "run-echo-area-clear-hook!"))
      (check "m36/imp3/module/exports-kill" #t
             (contains? cl-scm "run-kill-emacs-hook!"))
      (check "m36/imp3/module/defines-echo" #t
             (contains? cl-scm "(define (run-echo-area-clear-hook!)"))
      (check "m36/imp3/module/defines-kill" #t
             (contains? cl-scm "(define (run-kill-emacs-hook! noninteractive)"))
      ;; The module owns the hook names and calls safe-run-hooks!.
      (check "m36/imp3/module/owns-echo-hook" #t
             (contains? cl-scm "(safe-run-hooks! 'echo-area-clear-hook)"))
      (check "m36/imp3/module/owns-kill-hook" #t
             (contains? cl-scm "(safe-run-hooks! 'kill-emacs-hook)"))
      (check "m36/imp3/module/kill-else-query-error" #t
             (contains? cl-scm "run-hook-query-error-with-timeout"))))

;; No Scheme #f in the new bodies (elisp #f reads as true).
(let* ((echo (def-region cl-scm "(define (run-echo-area-clear-hook!)"))
       (kill (def-region cl-scm "(define (run-kill-emacs-hook! noninteractive)"))
       (echo-c (strip-scheme-strings (or echo "")))
       (kill-c (strip-scheme-strings (or kill ""))))
  (check "m36/imp3/module/echo-no-scheme-false" #f (contains? echo-c "#f"))
  (check "m36/imp3/module/kill-no-scheme-false" #f (contains? kill-c "#f"))
  (check "m36/imp3/module/kill-uses-nilp" #t (contains? kill-c "%nilp")))

;;; --- 5. Each caller file keeps its static dispatcher ---------------
(if (not emacs-c)
    (report "m36/imp3/scan/emacs.c" (cons 'FAIL "src/emacs.c missing"))
    (begin
      (check "m36/imp3/emacs.c/dispatcher-defined" #t
             (contains? emacs-c "emacs_run_kill_emacs_hook (bool noninteractive)"))
      (check "m36/imp3/emacs.c/dispatcher-call" #t
             (contains? emacs-c "emacs_run_kill_emacs_hook (noninteractive)"))
      (check "m36/imp3/emacs.c/refs-command-loop" #t
             (contains? emacs-c "scm_c_public_ref (\"emacs command-loop\", \"run-kill-emacs-hook!\")"))
      (check "m36/imp3/emacs.c/live-call-gone" #f
             (contains? emacs-c "safe_run_hooks (Qkill_emacs_hook)"))))
(if (not xmenu-c)
    (report "m36/imp3/scan/xmenu.c" (cons 'FAIL "src/xmenu.c missing"))
    (begin
      (check "m36/imp3/xmenu.c/activate-dispatcher" #t
             (contains? xmenu-c "xmenu_run_activate_menubar_hook (void)"))
      (check "m36/imp3/xmenu.c/menu-bar-dispatcher" #t
             (contains? xmenu-c "xmenu_run_menu_bar_update_hook (void)"))
      (check "m36/imp3/xmenu.c/activate-dispatch-call" #t
             (contains? xmenu-c "xmenu_run_activate_menubar_hook ();"))
      (check "m36/imp3/xmenu.c/menu-bar-dispatch-call" #t
             (contains? xmenu-c "xmenu_run_menu_bar_update_hook ();"))
      (check "m36/imp3/xmenu.c/reuses-xdisp-activate" #t
             (contains? xmenu-c "\"xdisp-run-activate-menubar-hook!\""))
      (check "m36/imp3/xmenu.c/reuses-xdisp-menu-bar" #t
             (contains? xmenu-c "\"xdisp-run-menu-bar-update-hook!\""))
      (check "m36/imp3/xmenu.c/live-call-gone" #f
             (contains? xmenu-c "safe_run_hooks (Qactivate_menubar_hook)"))))

;;; --- 6. The stale comment at keyboard.c:11197 is repaired ---------
(if (not kbd)
    (report "m36/imp3/scan/comment" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m36/imp3/comment/old-claim-gone" #f
             (contains? kbd "still consumed from C (safe_run_hooks"))
      (check "m36/imp3/comment/repaired" #t
             (contains? kbd "M36 imp-3 moved the last"))))

;;; --- 7. The untouched mechanisms -------------------------------
(if (not kbd)
    (report "m36/imp3/scan/keep" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m36/imp3/keep/gobble-input" #t
             (contains? kbd "gobble_input (void)"))
      (check "m36/imp3/keep/kbd-buffer-store-event" #t
             (contains? kbd "kbd_buffer_store_event (register struct input_event"))
      (check "m36/imp3/keep/detect-input-pending-ignore-squeezables" #t
             (contains? kbd "detect_input_pending_ignore_squeezables (void)"))))

;;; --- 8. The brief.org 9 surface anchors hold ----------------------
(if (not kbd)
    (report "m36/imp3/scan/keyboard.c-counts" (cons 'FAIL "missing"))
    (begin
      (check "m36/imp3/count/keyboard.c-lines" 11221
             (count-substr kbd "\n"))
      (check "m36/imp3/count/keyboard.c-defuns" 446
             (count-prefix kbd "DEFUN (\""))
      (check "m36/imp3/count/keyboard.c-shims" 420
             (count-prefix kbd "DEFUN (\"--"))))
(info "m36/imp3/count/keyboard-globals.c-lines" (count-substr kg "\n"))
(check "m36/imp3/count/combined-lines" 11711
       (+ (count-substr kbd "\n") (count-substr kg "\n")))
(check "m36/imp3/count/under-budget" #t
       (<= (+ (count-substr kbd "\n") (count-substr kg "\n")) 11960))
(check "m36/imp3/count/scm-c-public-ref-sites" 162
       (src-site-count))

;;; --- 9. Static: the corpus is registered in the keyboard group ----
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
                                      "\"test/keyboard/test-m36-imp3.el\""))))
  (check "m36/imp3/run-tests.scm/registers-el" #t
         (and (string? run-tests)
              (and reg-idx
                   (contains? (list-ref rt-lines reg-idx)
                              "\"test/keyboard/test-m36-imp3.el\""))
              (and kg-end
                   (< kg-start reg-idx)
                   (< reg-idx kg-end)))))

;;; --- 10. The prior corpora pin the new retired state --------------
(define m35-imp2 (slurp (repo "test/keyboard/test-m35-imp2.scm")))
(define m35-imp3 (slurp (repo "test/keyboard/test-m35-imp3.scm")))
(define m34-imp3 (slurp (repo "test/keyboard/test-m34-imp3.scm")))
(define m34-imp4 (slurp (repo "test/keyboard/test-m34-imp4.scm")))
(define m34-imp7 (slurp (repo "test/keyboard/test-m34-imp7.scm")))
(check "m36/imp3/prior/m35-imp2-def-retired" #t
       (contains? m35-imp2 "m35/imp2/def/safe-run-hooks-retired"))
(check "m36/imp3/prior/m35-imp2-keep-retired" #t
       (contains? m35-imp2 "m35/imp2/keep/safe-run-hooks/emacs.c-retired"))
(check "m36/imp3/prior/m35-imp3-keep-retired" #t
       (contains? m35-imp3 "m35/imp3/keep/safe-run-hooks/emacs.c-retired"))
(check "m36/imp3/prior/m34-imp3-retired" #t
       (contains? m34-imp3 "m34/imp3/keyboard.c/safe-run-hooks-retired"))
(check "m36/imp3/prior/m34-imp4-retired" #t
       (contains? m34-imp4 "m34/imp4/keyboard.c/safe-run-hooks-retired"))
(check "m36/imp3/prior/m34-imp7-retired" #t
       (contains? m34-imp7 "m34/imp7/kept/safe-run-hooks/definition-retired"))

;;; --- 11. cr.org F2: the pgtk.scm note is repaired -----------------
(if (not pgtk-scm)
    (report "m36/imp3/scan/pgtk.scm" (cons 'FAIL "module missing"))
    (begin
      (check "m36/imp3/cr/F2/pgtk-no-dead-shim" #f
             (contains? pgtk-scm "--detect-input-pending"))
      (check "m36/imp3/cr/F2/pgtk-repaired" #t
             (contains? pgtk-scm "It needs no such"))))

;;; --- 12. cr1.org F1: the sibling count anchors track the source ----
;;; The review found that the imp-3 commit moved the scm_c_public_ref
;;; site count from 156 to 159 but left three older corpora anchored at
;;; 156 (test-m36-imp1, test-m36-imp2, test-m35-imp3), so each of those
;;; checks failed "expected 156 got 159".  The anchors are now re-pinned
;;; and this section keeps them honest: it reads the anchor out of each
;;; sibling corpus and compares it with the live count, so a later
;;; surface move cannot leave a corpus behind.  cr1.org F1, F5.
;;; M39 re-measured: the process ports added three scm_c_public_ref sites
;;; (src/process.c 8 -> 11), so the live count is now 162 and every
;;; sibling anchor is re-pinned to 162.  cr.org F1.
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

(define (anchor-site-count text)
  "The integer pinned by the first (check ... scm-c-public-ref-sites)
line of TEXT, or #f."
  (if (not (string? text))
      #f
      (let loop ((lines (split-lines text)))
        (cond ((null? lines) #f)
              ((and (string-contains (car lines) "(check")
                    (string-contains (car lines) "scm-c-public-ref-sites"))
               (let ((i (string-contains (car lines) "scm-c-public-ref-sites")))
                 (first-int (substring (car lines)
                                       (+ i (string-length
                                             "scm-c-public-ref-sites"))
                                       (string-length (car lines))))))
              (else (loop (cdr lines)))))))

(define measured-sites (src-site-count))
(check "m36/imp3/anchor/m36-imp1" measured-sites
       (anchor-site-count (slurp (repo "test/keyboard/test-m36-imp1.scm"))))
(check "m36/imp3/anchor/m36-imp2" measured-sites
       (anchor-site-count (slurp (repo "test/keyboard/test-m36-imp2.scm"))))
(check "m36/imp3/anchor/m35-imp3" measured-sites
       (anchor-site-count m35-imp3))
