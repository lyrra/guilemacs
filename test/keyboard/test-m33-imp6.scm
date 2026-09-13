;;; test-m33-imp6.scm --- M33 imp-6: the 2 DEFVAR_* names move to Scheme.
;;;
;;; brief.org (M33 imp-6) moves two names out of C:
;;;
;;;   - extra-keyboard-modifiers      (DEFVAR_INT,  default 0)
;;;   - mwheel-coalesce-scroll-events (DEFVAR_BOOL, default true)
;;;
;;; The DEFVAR_* sites and their default assignments are deleted from
;;; src/keyboard-globals.c.  The two rows are added to the M23
;;; declaration table in mod/emacs/command-loop.scm.  No compiled C
;;; file reads either cell: src/xterm.c reads through (emacs xterm)
;;; (x-extra-keyboard-modifiers / x-mwheel-coalesce-scroll-events?),
;;; src/pgtkterm.c reads through (emacs pgtk) (the pgtk- pair), and
;;; src/main-queue via (mod/emacs/main-queue.scm) reads with
;;; symbol-value.  The C keeps the mechanism: x_emacs_to_x_modifiers,
;;; scm_to_intmax in the dispatcher, and the fabs tests.
;;;
;;; This corpus pins the port end state.  Six kinds of check:
;;;
;;;   - deletion: keyboard-globals.c holds neither DEFVAR_* site;
;;;     the generated globals.h holds neither storage member.
;;;   - declaration: command-loop.scm holds both names; the module
;;;     boot-loads once.
;;;   - runtime: both names are special and bound; each cell is live
;;;     through every reader, not a constant.
;;;   - mechanism: xterm.c keeps the conversion and the fabs tests.
;;;   - no C reader: no compiled C file reads a bare cell.
;;;
;;; The repo root is bound by the .el wrapper as %m33-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m33-imp6.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))
(use-modules (emacs-elisp runtime))

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
  ;; string-contains returns the match index or #f; normalize to a boolean
  ;; so `check' can compare against #t/#f.
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (count-occurrences text needle)
  "Return the number of non-overlapping occurrences of NEEDLE in TEXT."
  (if (or (not (string? text)) (string-null? needle))
      0
      (let loop ((start 0) (n 0))
        (let ((i (string-contains text needle start)))
          (if i (loop (+ i (string-length needle)) (1+ n)) n)))))

(define (repo path) (string-append %m33-root "/" path))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m33-root))
    (begin (report "m33-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m33-root "."))
    (report "m33-root-bound" 'PASS))

;;; --- 1. Deletion: keyboard-globals.c holds neither site ------------
(define kbd-g (slurp (repo "src/keyboard-globals.c")))
(if (not kbd-g)
    (report "m33/imp6/scan/keyboard-globals.c"
            (cons 'FAIL "src/keyboard-globals.c missing"))
    (begin
      (check "m33/imp6/keyboard-globals.c/no-defvar-extra-keyboard" #f
             (contains? kbd-g "DEFVAR_INT (\"extra-keyboard-modifiers\""))
      (check "m33/imp6/keyboard-globals.c/no-defvar-mwheel" #f
             (contains? kbd-g "DEFVAR_BOOL (\"mwheel-coalesce-scroll-events\""))
      ;; The two default assignments go with the sites.
      (check "m33/imp6/keyboard-globals.c/no-default-extra-keyboard" #f
             (contains? kbd-g "extra_keyboard_modifiers = 0;"))
      (check "m33/imp6/keyboard-globals.c/no-default-mwheel" #f
             (contains? kbd-g "mwheel_coalesce_scroll_events = true;"))
      ;; The stay-C names are untouched (brief.org 7).
      (check "m33/imp6/keyboard-globals.c/keeps-deactivate-mark" #t
             (contains? kbd-g "DEFVAR_LISP (\"deactivate-mark\""))
      (check "m33/imp6/keyboard-globals.c/keeps-overriding-menu-flag" #t
             (contains? kbd-g "DEFVAR_LISP (\"overriding-local-map-menu-flag\""))
      (check "m33/imp6/keyboard-globals.c/keeps-track-mouse" #t
             (contains? kbd-g "DEFVAR_LISP (\"track-mouse\""))))

;;; --- 2. Deletion: globals.h holds neither storage member -----------
;;; The build regenerates src/globals.h.  A surviving member would keep
;;; the bare-name macro alive, and a C reader would link or compile.
(define globals-h (slurp (repo "src/globals.h")))
(if (not globals-h)
    (report "m33/imp6/scan/globals.h"
            (cons 'FAIL "src/globals.h missing (build it first)"))
    (begin
      (check "m33/imp6/globals.h/no-member-extra-keyboard" #f
             (contains? globals-h "f_extra_keyboard_modifiers"))
      (check "m33/imp6/globals.h/no-member-mwheel" #f
             (contains? globals-h "f_mwheel_coalesce_scroll_events"))))

;;; --- 3. Declaration: command-loop.scm holds both names -------------
(define cmd-loop (slurp (repo "mod/emacs/command-loop.scm")))
(if (not cmd-loop)
    (report "m33/imp6/scan/command-loop.scm"
            (cons 'FAIL "mod/emacs/command-loop.scm missing"))
    (begin
      (check "m33/imp6/command-loop.scm/holds-extra-keyboard" #t
             (contains? cmd-loop "(extra-keyboard-modifiers"))
      (check "m33/imp6/command-loop.scm/holds-mwheel" #t
             (contains? cmd-loop "(mwheel-coalesce-scroll-events"))))

;;; The module boot-loads once.
(define load-scm (slurp (repo "prelude/load.scm")))
(if (not load-scm)
    (report "m33/imp6/scan/load.scm" (cons 'FAIL "prelude/load.scm missing"))
    (begin
      (check "m33/imp6/load.scm/registers-module" #t
             (contains? load-scm "(emacs command-loop)"))
      (check "m33/imp6/load.scm/registers-module-once" 1
             (count-occurrences load-scm "(use-modules (emacs command-loop))"))))

;;; --- 4. Runtime: both names are special and bound ------------------
;;; The declaration table calls proclaim-special! then, when unbound,
;;; set-symbol-default-value!.  So both must be special and bound.
(check "m33/imp6/runtime/extra-keyboard-special" #t
       (special? 'extra-keyboard-modifiers))
(check "m33/imp6/runtime/mwheel-special" #t
       (special? 'mwheel-coalesce-scroll-events))
(check "m33/imp6/runtime/extra-keyboard-bound" #t
       (symbol-default-bound? 'extra-keyboard-modifiers))
(check "m33/imp6/runtime/mwheel-bound" #t
       (symbol-default-bound? 'mwheel-coalesce-scroll-events))

;;; The xterm pair reads the live cell (brief.org 4).
(use-modules (emacs xterm))
(check "m33/imp6/runtime/x-extra-keyboard-default" 0
       (x-extra-keyboard-modifiers))
(check "m33/imp6/runtime/x-mwheel-default" #t
       (x-mwheel-coalesce-scroll-events?))

;;; The pgtk pair reads the same live cell (brief.org 4, imp-5 readers).
(use-modules (emacs pgtk))
(check "m33/imp6/runtime/pgtk-extra-keyboard-default" 0
       (pgtk-extra-keyboard-modifiers))
(check "m33/imp6/runtime/pgtk-mwheel-default" #t
       (pgtk-mwheel-coalesce-scroll-events?))

;;; Prove each read is live, not a constant: write the cell, read it
;;; back through every reader, then restore the default.
(set-symbol-value! 'extra-keyboard-modifiers 3)
(check "m33/imp6/runtime/x-extra-keyboard-live" 3
       (x-extra-keyboard-modifiers))
(check "m33/imp6/runtime/pgtk-extra-keyboard-live" 3
       (pgtk-extra-keyboard-modifiers))
(set-symbol-value! 'extra-keyboard-modifiers 0)
(check "m33/imp6/runtime/x-extra-keyboard-restored" 0
       (x-extra-keyboard-modifiers))

(set-symbol-value! 'mwheel-coalesce-scroll-events #nil)
(check "m33/imp6/runtime/x-mwheel-live" #f
       (x-mwheel-coalesce-scroll-events?))
(check "m33/imp6/runtime/pgtk-mwheel-live" #f
       (pgtk-mwheel-coalesce-scroll-events?))
(set-symbol-value! 'mwheel-coalesce-scroll-events #t)
(check "m33/imp6/runtime/x-mwheel-restored" #t
       (x-mwheel-coalesce-scroll-events?))

;;; --- 5. Mechanism: src/xterm.c keeps the C mechanism ---------------
(define xt (slurp (repo "src/xterm.c")))
(if (not xt)
    (report "m33/imp6/scan/xterm.c" (cons 'FAIL "src/xterm.c missing"))
    (begin
      (check "m33/imp6/xterm.c/keeps-emacs-to-x-modifiers" #t
             (contains? xt "x_emacs_to_x_modifiers"))
      ;; The 2 fabs tests of the coalesce decision (brief.org 4).
      (check "m33/imp6/xterm.c/keeps-fabs-emacs-value" #t
             (contains? xt "(fabs (val->emacs_value) < 1)"))
      (check "m33/imp6/xterm.c/keeps-fabs-delta" #t
             (contains? xt "(fabs (delta) > 0)"))
      (check "m33/imp6/xterm.c/keeps-fabs-total" #t
             (contains? xt "(fabs (total_x) > 0 || fabs (total_y) > 0)"))))

;;; --- 6. No C reader: no compiled C file reads a bare cell ----------
;;; The build compiles keyboard.c and xterm.c.  A bare read of a cell
;;; is a defect.  Assert the call-site forms, not the bare names (a
;;; comment may keep the name; x_* embeds it).
(define kbd-c (slurp (repo "src/keyboard.c")))
(if (not kbd-c)
    (report "m33/imp6/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m33/imp6/keyboard.c/no-bare-extra-keyboard" #f
             (contains? kbd-c "extra_keyboard_modifiers"))
      (check "m33/imp6/keyboard.c/no-bare-mwheel" #f
             (contains? kbd-c "mwheel_coalesce_scroll_events"))))

(if (not xt)
    (report "m33/imp6/scan/xterm.c-readers"
            (cons 'FAIL "src/xterm.c missing"))
    (begin
      ;; The old bare read forms are gone.
      (check "m33/imp6/xterm.c/no-old-extra-keyboard-read" #f
             (contains? xt ", extra_keyboard_modifiers)"))
      (check "m33/imp6/xterm.c/no-old-mwheel-read" #f
             (contains? xt "if (mwheel_coalesce_scroll_events"))
      ;; The reads go through the (emacs xterm) dispatchers.
      (check "m33/imp6/xterm.c/reads-via-dispatcher" #t
             (contains? xt "x_extra_keyboard_modifiers ()"))
      (check "m33/imp6/xterm.c/reads-mwheel-via-dispatcher" #t
             (contains? xt "x_mwheel_coalesce_scroll_events_p ()"))))

;;; --- 7. Static: the corpus is registered ---------------------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(if (not run-tests)
    (report "m33/imp6/scan/run-tests.scm"
            (cons 'FAIL "tool/run-tests.scm missing"))
    (check "m33/imp6/run-tests.scm/registers-el" #t
           (contains? run-tests "test-m33-imp6.el")))
