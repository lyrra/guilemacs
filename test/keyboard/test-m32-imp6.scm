;;; test-m32-imp6.scm --- M32 imp-6: the close-out audit corpus.
;;;
;;; brief.org (M32 imp-6) is the docs-only close-out.  It runs no port
;;; work.  It re-measures the surface (Job 1) and proves the two stub
;;; retirements (Job 2).  This corpus pins the Job 2 proof and the Job 1
;;; anchored counts so the close-out claims are checked automatically
;;; instead of only by hand.
;;;
;;; Two kinds of check:
;;;
;;;   - a static retirement proof: cmd_error_internal has no definition,
;;;     extern, or caller left; stuff_buffered_input keeps only the
;;;     allowed hits (comment lines, the file-local static body, the
;;;     file-local static dispatcher) and no header extern; and the 6
;;;     migrated names have no C storage in the generated globals.h.
;;;   - a static count check: the anchored Job 1 numbers (the
;;;     keyboard.c DEFUN count and the keyboard-globals.c site split)
;;;     match the brief table.
;;;
;;; All checks read files, so the corpus needs no C entry point and is
;;; batch-safe.
;;;
;;; The repo root is bound by the .el wrapper as %m32-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m32-imp6.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (info name value)
  (report name (cons 'INFO value)))

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
  ;; string-contains returns the match index or #f; normalize to a boolean
  ;; so `check' can compare against #t/#f.
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (count-prefix text prefix)
  "Count the lines of TEXT that start with PREFIX.  This is the anchored
count -- a loose substring match would also count a comment line."
  (if (not (string? text))
      0
      (call-with-input-string text
        (lambda (port)
          (let loop ((n 0))
            (let ((line (read-line port)))
              (cond ((eof-object? line) n)
                    ((string-prefix? prefix line) (loop (1+ n)))
                    (else (loop n)))))))))

(define (repo path) (string-append %m32-root "/" path))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m32-root))
    (begin (report "m32/imp6/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m32-root "."))
    (report "m32/imp6/root-bound" 'PASS))

;;; --- 1. Static: cmd_error_internal is fully retired -----------------
;;; imp-2 retired the stub.  No definition, no extern, no caller may
;;; stay in the three files the brief names.
(for-each
 (lambda (path)
   (let ((text (slurp (repo path))))
     (if (not text)
         (report (string-append "m32/imp6/scan/" path)
                 (cons 'FAIL "file missing"))
         (check (string-append "m32/imp6/no-cmd-error-internal/" path) #f
                (contains? text "cmd_error_internal")))))
 '("src/keyboard.c" "src/process.c" "src/lisp.h"))

;;; --- 2. Static: stuff_buffered_input leaves only allowed hits -------
;;; imp-3 retired the extern stub.  No header extern may stay, and the
;;; keyboard.c references must be comments only (no call, no definition).
(define lisp-h (slurp (repo "src/lisp.h")))
(if (not lisp-h)
    (report "m32/imp6/scan/lisp.h" (cons 'FAIL "src/lisp.h missing"))
    (check "m32/imp6/lisp.h/no-stuff-buffered-input" #f
           (contains? lisp-h "stuff_buffered_input")))
(define keyboard-h (slurp (repo "src/keyboard.h")))
(if (not keyboard-h)
    (report "m32/imp6/scan/keyboard.h" (cons 'FAIL "src/keyboard.h missing"))
    (check "m32/imp6/keyboard.h/no-stuff-buffered-input" #f
           (contains? keyboard-h "stuff_buffered_input")))

(define kbd (slurp (repo "src/keyboard.c")))
(if (not kbd)
    (report "m32/imp6/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      ;; No call site (a comment mention has no " (").
      (check "m32/imp6/keyboard.c/no-call" #f
             (contains? kbd "stuff_buffered_input ("))
      ;; No extern declaration or definition.
      (check "m32/imp6/keyboard.c/no-extern" #f
             (contains? kbd "extern void stuff_buffered_input"))
      (check "m32/imp6/keyboard.c/no-definition" #f
             (contains? kbd "stuff_buffered_input (Lisp_Object"))
      ;; The comment references stay (they record the retirement).
      (check "m32/imp6/keyboard.c/keeps-comment" #t
             (contains? kbd "the stuff_buffered_input stub"))))

;;; --- 3. Static: the emacs.c fatal-safe body stays -------------------
;;; The C body and the dispatcher are file-local statics; the external
;;; entry point calls the dispatcher.  This is the port shape imp-3 left.
(define em (slurp (repo "src/emacs.c")))
(if (not em)
    (report "m32/imp6/scan/emacs.c" (cons 'FAIL "src/emacs.c missing"))
    (begin
      (check "m32/imp6/emacs.c/static-body" #t
             (contains? em "stuff_buffered_input_c (Lisp_Object"))
      (check "m32/imp6/emacs.c/static-dispatch" #t
             (contains? em "stuff_buffered_input_dispatch (Lisp_Object"))
      (check "m32/imp6/emacs.c/entry-calls-dispatch" #t
             (contains? em "stuff_buffered_input_dispatch (stuff);"))))

;;; --- 4. Static: the 6 migrated names have no C storage --------------
;;; A DEFVAR_* value cell would make the name C-owned again.  The check
;;; reads the generated globals.h, which is what a fresh build produces.
(define gh (slurp (repo "src/globals.h")))
(if (not gh)
    (report "m32/imp6/scan/globals.h" (cons 'FAIL "src/globals.h missing"))
    (for-each
     (lambda (cell)
       (check (string-append "m32/imp6/no-cell/" cell) #f
              (contains? gh cell)))
     '("f_Vtop_level" "f_Vthrow_on_input"
       "f_Vnum_nonmacro_input_events" "f_Vtty_erase_char")))

;;; --- 5. Static: keyboard-globals.c keeps only the DEFSYM handles ----
;;; The three retired names keep a DEFSYM (the Qsym #define and the
;;; defsym_name[] entry) but no DEFVAR_* site.  The other three names
;;; (top-level, attempt-orderly-shutdown-on-fatal-signal,
;;; attempt-stack-overflow-recovery) keep no handle in this file.
(define kg (slurp (repo "src/keyboard-globals.c")))
(if (not kg)
    (report "m32/imp6/scan/keyboard-globals.c" (cons 'FAIL "missing"))
    (begin
      (check "m32/imp6/kg/defsym-num-nonmacro-input-events" #t
             (contains? kg "DEFSYM (Qnum_nonmacro_input_events, \"num-nonmacro-input-events\")"))
      (check "m32/imp6/kg/defsym-throw-on-input" #t
             (contains? kg "DEFSYM (Qthrow_on_input, \"throw-on-input\")"))
      (check "m32/imp6/kg/defsym-tty-erase-char" #t
             (contains? kg "DEFSYM (Qtty_erase_char, \"tty-erase-char\")"))))

;;; --- 6. Static: the anchored Job 1 counts ---------------------------
;;; The brief warns twice about loose patterns.  Use the anchored forms
;;; only: "^DEFUN (\"" for the DEFUN count and "^  DEFVAR_*/DEFSYM (" for
;;; the site counts.  M33 imp-1 added two keyboard.c primitives
;;; (--menu-items, --clear-input-pending!), and M34 imp-1 added one more
;;; (--detect-input-pending-run-timers), so the count is 449.
;;; M33 imp-6 moved extra-keyboard-modifiers (INT) and
;;; mwheel-coalesce-scroll-events (BOOL) to Scheme, so the DEFVAR_INT
;;; and DEFVAR_BOOL site counts drop by one each (2 -> 1).
(if (not kbd)
    (report "m32/imp6/scan/keyboard.c-count" (cons 'FAIL "missing"))
    (check "m32/imp6/count/keyboard.c-defuns" 449
           (count-prefix kbd "DEFUN (\"")))

(if (not kg)
    (report "m32/imp6/scan/keyboard-globals.c-count" (cons 'FAIL "missing"))
    (begin
      (check "m32/imp6/count/defvar-lisp" 32 (count-prefix kg "  DEFVAR_LISP ("))
      (check "m32/imp6/count/defvar-int" 1 (count-prefix kg "  DEFVAR_INT ("))
      (check "m32/imp6/count/defvar-bool" 1 (count-prefix kg "  DEFVAR_BOOL ("))
      (check "m32/imp6/count/defvar-kboard" 8 (count-prefix kg "  DEFVAR_KBOARD ("))
      (check "m32/imp6/count/defsym" 34 (count-prefix kg "  DEFSYM ("))))

;;; --- 7. Static: the corpus is registered ---------------------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m32/imp6/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m32-imp6.el"))
