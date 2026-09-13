;;; test-m33-imp1.scm --- M33 imp-1: the term.c TTY help/mouse consumers.
;;;
;;; brief.org (M33 imp-1) ports the decision logic of the TTY menu
;;; help/mouse paths in src/term.c into the new module (emacs terminal),
;;; and the discard_mouse_events stub retires.  See docs/m33-plan.org A4.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - a runtime check: the module loads and exports the three
;;;     procedures.  The sandbox cannot relink src/emacs, so the two new
;;;     C primitives (--menu-items, --clear-input-pending!) are absent
;;;     from the running binary; every runtime call that would touch
;;;     them is guarded and reported as INFO, not asserted.
;;;   - a static wiring check: src/term.c holds the static dispatchers
;;;     and no longer calls discard_mouse_events; src/keyboard.c defines
;;;     the two primitives and no longer defines discard_mouse_events;
;;;     src/lisp.h no longer declares it; the module is boot-loaded.
;;;
;;; The repo root is bound by the .el wrapper as %m33-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m33-imp1.el.

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
  ;; string-contains returns the match index or #f; normalize to a boolean
  ;; so `check' can compare against #t/#f.
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (repo path) (string-append %m33-root "/" path))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m33-root))
    (begin (report "m33-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m33-root "."))
    (report "m33-root-bound" 'PASS))

;;; --- 1. The module loads and exports the three procedures ----------
(use-modules (emacs terminal))

(define (exported? name)
  (let ((p (module-ref (resolve-module '(emacs terminal)) name)))
    (procedure? p)))

(check "m33/imp1/export/tty-menu-clear-help!" #t
       (exported? 'tty-menu-clear-help!))
(check "m33/imp1/export/tty-menu-help-callback" #t
       (exported? 'tty-menu-help-callback))
(check "m33/imp1/export/tty-menu-discard-mouse-events!" #t
       (exported? 'tty-menu-discard-mouse-events!))

;;; --- 2. Runtime: the clear-help arm (no new primitive) -------------
;;; The MI_QUIT_MENU arm calls show-help-echo with four nils.  It does
;;; not touch a new primitive, so assert the return value.
(define (safe thunk)
  (catch #t
    (lambda () (cons 'ok (thunk)))
    (lambda (key . args) (cons 'error (cons key args)))))

(let ((r (safe (lambda () (tty-menu-clear-help!)))))
  (report "m33/imp1/runtime/clear-help" (list 'INFO r))
  (check "m33/imp1/runtime/clear-help-returns-nil" '(ok . #nil) r))

;;; --- 3. Runtime: calls that touch a new primitive ------------------
;;; tty-menu-discard-mouse-events! calls --clear-input-pending! when no
;;; real event waits; tty-menu-help-callback reads --menu-items.  The
;;; running binary lacks both, so print an INFO report and do not assert.
(let ((r (safe (lambda () (tty-menu-discard-mouse-events!)))))
  (report "m33/imp1/runtime/discard-mouse-events" (list 'INFO r)))
(let ((r (safe (lambda () (tty-menu-help-callback "" 1 2)))))
  (report "m33/imp1/runtime/help-callback" (list 'INFO r)))

;;; --- 4. Static: the module source shapes the three decision arms ---
(define term-mod (slurp (repo "mod/emacs/terminal.scm")))
(if (not term-mod)
    (report "m33/imp1/scan/module" (cons 'FAIL "mod/emacs/terminal.scm missing"))
    (begin
      (check "m33/imp1/module/export-names" #t
             (and (contains? term-mod "tty-menu-clear-help!")
                  (contains? term-mod "tty-menu-help-callback")
                  (contains? term-mod "tty-menu-discard-mouse-events!")))
      (check "m33/imp1/module/menu-items-primitive" #t
             (contains? term-mod "%--menu-items"))
      (check "m33/imp1/module/clear-input-pending-primitive" #t
             (contains? term-mod "%--clear-input-pending!"))
      (check "m33/imp1/module/aref" #t (contains? term-mod "%aref"))
      (check "m33/imp1/module/vectorp" #t (contains? term-mod "%vectorp"))
      (check "m33/imp1/module/show-help-echo" #t
             (contains? term-mod "show-help-echo"))
      (check "m33/imp1/module/pane-name-const" #t
             (contains? term-mod "%menu-items-pane-name"))
      (check "m33/imp1/module/item-name-const" #t
             (contains? term-mod "%menu-items-item-name"))))

;;; --- 5. Static: src/term.c calls the dispatchers, old code is gone --
(define term-c (slurp (repo "src/term.c")))
(if (not term-c)
    (report "m33/imp1/scan/term.c" (cons 'FAIL "src/term.c missing"))
    (begin
      (check "m33/imp1/term.c/includes-guile.h" #t
             (contains? term-c "#include \"guile.h\""))
      ;; The three static dispatchers exist.
      (check "m33/imp1/term.c/defines-clear-help" #t
             (contains? term-c "tty_menu_clear_help (void)"))
      (check "m33/imp1/term.c/defines-discard-mouse-events" #t
             (contains? term-c "tty_menu_discard_mouse_events (void)"))
      ;; The three call sites leave C.
      (check "m33/imp1/term.c/calls-clear-help" #t
             (contains? term-c "tty_menu_clear_help ();"))
      (check "m33/imp1/term.c/calls-discard-mouse-events" #t
             (contains? term-c "tty_menu_discard_mouse_events ();"))
      (check "m33/imp1/term.c/help-callback-dispatches" #t
             (contains? term-c "tty-menu-help-callback"))
      ;; The old C bodies are gone.
      (check "m33/imp1/term.c/no-old-discard-call" #f
             (contains? term-c "  discard_mouse_events ();"))
      (check "m33/imp1/term.c/no-old-help-body-list3" #f
             (contains? term-c "list3 (Qmenu_item"))
      (check "m33/imp1/term.c/no-old-help-body-check-type" #f
             (contains? term-c "CHECK_TYPE (PLAIN_VECTORP (menu_vec)"))))

;;; --- 6. Static: src/keyboard.c holds the two primitives ------------
;;; The discard_mouse_events stub retired.
(define kbd-c (slurp (repo "src/keyboard.c")))
(if (not kbd-c)
    (report "m33/imp1/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m33/imp1/keyboard.c/primitive-menu-items" #t
             (contains? kbd-c "\"--menu-items\""))
      (check "m33/imp1/keyboard.c/primitive-clear-input-pending" #t
             (contains? kbd-c "\"--clear-input-pending!\""))
      (check "m33/imp1/keyboard.c/retired-discard-mouse-events" #f
             (contains? kbd-c "discard_mouse_events (void)"))))

;;; --- 7. Static: lisp.h no longer declares the stub -----------------
(define lisp-h (slurp (repo "src/lisp.h")))
(if (not lisp-h)
    (report "m33/imp1/scan/lisp.h" (cons 'FAIL "src/lisp.h missing"))
    (check "m33/imp1/lisp.h/no-discard-mouse-events" #f
           (contains? lisp-h "discard_mouse_events")))

;;; --- 8. Static: boot load ------------------------------------------
(define load-scm (slurp (repo "prelude/load.scm")))
(check "m33/imp1/load.scm/registers-module" #t
       (contains? load-scm "(emacs terminal)"))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m33/imp1/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m33-imp1.el"))

;;; --- 9. Static: the review resolutions are recorded -----------------
;;; cr.org F1 (the frame help path reading), F2 (vectorp vs
;;; PLAIN_VECTORP) and F3 ("" vs empty_unibyte_string) are low-risk.
;;; The module records each one, so a future reader sees it.  These
;;; checks pin the record only; they assert no runtime behavior.
(check "m33/imp1/record/F1-frame-help-path" #t
       (and (contains? term-mod "fn-pointer wiring")
            (contains? term-mod "no fourth dispatcher")))
(check "m33/imp1/record/F2-vectorp-divergence" #t
       (and (contains? term-mod "F2")
            (contains? term-mod "PLAIN_VECTORP")))
(check "m33/imp1/record/F3-empty-unibyte" #t
       (and (contains? term-mod "F3")
            (contains? term-mod "empty_unibyte_string")))
