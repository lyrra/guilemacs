;;; test-m33-imp4.scm --- M33 imp-4: the xterm.c input test and the 2
;;;                       name readers.
;;;
;;; brief.org (M33 imp-4) moves 3 things out of src/xterm.c and into the
;;; module (emacs xterm):
;;;
;;;   - the XTflash input-pending test -> x-input-pending?
;;;   - the extra-keyboard-modifiers read -> x-extra-keyboard-modifiers
;;;   - the mwheel-coalesce-scroll-events read
;;;     -> x-mwheel-coalesce-scroll-events?
;;;
;;; The C mechanism stays C: the pselect / fd-set / timeout arithmetic,
;;; the x_emacs_to_x_modifiers conversion, and the 2 fabs tests.
;;;
;;; This corpus pins the port end state.  Three kinds of check:
;;;
;;;   - a load / export check: the module loads and exports the 3 new
;;;     procedures.
;;;   - a runtime check: the 2 name readers read the live cell.  The
;;;     reads use the running binary.  The input-pending value is not
;;;     pinned, because it depends on the input state.
;;;   - a static wiring check: src/xterm.c holds the 3 dispatchers and
;;;     the 3 module references; the 3 old C reads are gone; the
;;;     DEFVAR_* sites stayed C at imp-4 and moved to Scheme at imp-6;
;;;     the module boot-loads once.
;;;
;;; The repo root is bound by the .el wrapper as %m33-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m33-imp4.el.

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

;;; --- 1. The module loads and exports the 3 new procedures ----------
(use-modules (emacs xterm))

(define (exported? name)
  (let ((p (module-ref (resolve-module '(emacs xterm)) name)))
    (procedure? p)))

(check "m33/imp4/export/x-input-pending?" #t
       (exported? 'x-input-pending?))
(check "m33/imp4/export/x-extra-keyboard-modifiers" #t
       (exported? 'x-extra-keyboard-modifiers))
(check "m33/imp4/export/x-mwheel-coalesce-scroll-events?" #t
       (exported? 'x-mwheel-coalesce-scroll-events?))

;;; --- 2. Runtime: the 2 name readers read the live cell -------------
;;; Both names keep their DEFVAR_* defaults at imp-4.
(check "m33/imp4/runtime/extra-keyboard-modifiers-default" 0
       (x-extra-keyboard-modifiers))
(check "m33/imp4/runtime/mwheel-coalesce-scroll-events-default" #t
       (x-mwheel-coalesce-scroll-events?))

;; The input test returns a boolean; the value depends on the input
;; state, so do not pin it.
(check "m33/imp4/runtime/input-pending-is-boolean" #t
       (boolean? (x-input-pending?)))

;; Prove the read is live, not a constant: write the cell, read again.
(set-symbol-value! 'extra-keyboard-modifiers 3)
(check "m33/imp4/runtime/extra-keyboard-modifiers-live" 3
       (x-extra-keyboard-modifiers))
(set-symbol-value! 'extra-keyboard-modifiers 0)
(check "m33/imp4/runtime/extra-keyboard-modifiers-restored" 0
       (x-extra-keyboard-modifiers))

(set-symbol-value! 'mwheel-coalesce-scroll-events #nil)
(check "m33/imp4/runtime/mwheel-coalesce-scroll-events-live" #f
       (x-mwheel-coalesce-scroll-events?))
(set-symbol-value! 'mwheel-coalesce-scroll-events #t)
(check "m33/imp4/runtime/mwheel-coalesce-scroll-events-restored" #t
       (x-mwheel-coalesce-scroll-events?))

;;; --- 3. Static: src/xterm.c holds the 3 dispatchers ----------------
(define xterm-c (slurp (repo "src/xterm.c")))
(if (not xterm-c)
    (report "m33/imp4/scan/xterm.c" (cons 'FAIL "src/xterm.c missing"))
    (begin
      (check "m33/imp4/xterm.c/defines-input-pending" #t
             (contains? xterm-c "x_input_pending (void)"))
      (check "m33/imp4/xterm.c/defines-extra-keyboard-modifiers" #t
             (contains? xterm-c "x_extra_keyboard_modifiers (void)"))
      (check "m33/imp4/xterm.c/defines-mwheel-coalesce" #t
             (contains? xterm-c "x_mwheel_coalesce_scroll_events_p (void)"))
      ;; The 3 module references.
      (check "m33/imp4/xterm.c/refs-input-pending" #t
             (contains? xterm-c "\"emacs xterm\", \"x-input-pending?\""))
      (check "m33/imp4/xterm.c/refs-extra-keyboard-modifiers" #t
             (contains? xterm-c "\"emacs xterm\", \"x-extra-keyboard-modifiers\""))
      (check "m33/imp4/xterm.c/refs-mwheel-coalesce" #t
             (contains? xterm-c "\"x-mwheel-coalesce-scroll-events?\""))
      ;; The 3 old C reads are gone.  Assert the call-site forms, not the
      ;; bare names: a comment may keep the name.
      (check "m33/imp4/xterm.c/no-old-detect-call" #f
             (contains? xterm-c "while (! detect_input_pending ())"))
      (check "m33/imp4/xterm.c/no-old-extra-keyboard-read" #f
             (contains? xterm-c "extra_keyboard_modifiers);"))
      (check "m33/imp4/xterm.c/no-old-mwheel-read" #f
             (contains? xterm-c "if (mwheel_coalesce_scroll_events"))
      ;; The mechanism stays C.
      (check "m33/imp4/xterm.c/keeps-x-emacs-to-x-modifiers" #t
             (contains? xterm-c "x_emacs_to_x_modifiers"))
      (check "m33/imp4/xterm.c/keeps-fabs-tests" #t
             (contains? xterm-c "(fabs (delta) > 0)"))))

;;; --- 4. Static: the 2 DEFVAR_* sites no longer stay -----------------
;;; imp-4 moved the readers but kept the DEFVAR_* sites in C.  M33 imp-6
;;; moved the two sites to Scheme, so assert they are gone.  A surviving
;;; site would make the name C-owned again.
(define kbd-g (slurp (repo "src/keyboard-globals.c")))
(if (not kbd-g)
    (report "m33/imp4/scan/keyboard-globals.c"
            (cons 'FAIL "src/keyboard-globals.c missing"))
    (begin
      (check "m33/imp4/keyboard-globals.c/no-defvars-extra-keyboard" #f
             (contains? kbd-g "DEFVAR_INT (\"extra-keyboard-modifiers\""))
      (check "m33/imp4/keyboard-globals.c/no-defvars-mwheel" #f
             (contains? kbd-g "DEFVAR_BOOL (\"mwheel-coalesce-scroll-events\""))))

;;; --- 5. Static: src/keyboard.c keeps the primitive -----------------
(define kbd-c (slurp (repo "src/keyboard.c")))
(if (not kbd-c)
    (report "m33/imp4/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m33/imp4/keyboard.c/still-defines-detect-input-pending" #t
             (contains? kbd-c "detect_input_pending (void)"))
      (check "m33/imp4/keyboard.c/still-defines-primitive" #t
             (contains? kbd-c "--detect-input-pending"))))

;;; --- 6. Static: the module source ----------------------------------
(define xterm-mod (slurp (repo "mod/emacs/xterm.scm")))
(if (not xterm-mod)
    (report "m33/imp4/scan/module" (cons 'FAIL "mod/emacs/xterm.scm missing"))
    (begin
      (check "m33/imp4/module/declarative" #t
             (contains? xterm-mod "#:declarative? #t"))
      (check "m33/imp4/module/exports-input-pending" #t
             (contains? xterm-mod "x-input-pending?"))
      (check "m33/imp4/module/exports-extra-keyboard-modifiers" #t
             (contains? xterm-mod "x-extra-keyboard-modifiers"))
      (check "m33/imp4/module/exports-mwheel-coalesce" #t
             (contains? xterm-mod "x-mwheel-coalesce-scroll-events?"))
      (check "m33/imp4/module/reads-with-symbol-value" #t
             (contains? xterm-mod "%symbol-value"))))

;;; --- 7. Static: boot load runs the module once ---------------------
(define load-scm (slurp (repo "prelude/load.scm")))
(if (not load-scm)
    (report "m33/imp4/scan/load.scm" (cons 'FAIL "prelude/load.scm missing"))
    (begin
      (check "m33/imp4/load.scm/registers-module" #t
             (contains? load-scm "(emacs xterm)"))
      (check "m33/imp4/load.scm/registers-module-once" 1
             (count-occurrences load-scm "(use-modules (emacs xterm))"))))

;;; --- 8. Static: the corpus is registered ---------------------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m33/imp4/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m33-imp4.el"))
