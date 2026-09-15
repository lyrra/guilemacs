;;; test-m33-imp2.scm --- M33 imp-2: the xmenu.c/gtkutil.c menu/help
;;; consumers.
;;;
;;; brief.org (M33 imp-2) ports the decision logic of the X/GTK menu help
;;; and timer paths in src/xmenu.c and src/gtkutil.c into the new module
;;; (emacs menu), and the show_help_echo stub retires.  See
;;; docs/m33-plan.org A5 ... A7.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - a runtime check: the module loads and exports the four
;;;     procedures.  The sandbox may not relink src/emacs, so a runtime
;;;     call that touches a newly built helper is guarded and reported
;;;     as INFO, not asserted.
;;;   - a static wiring check: src/xmenu.c holds the three dispatchers
;;;     and no longer calls show_help_echo or timer_check; src/gtkutil.c
;;;     holds the dispatch and no longer calls timer_check;
;;;     src/keyboard.c no longer defines show_help_echo but still
;;;     defines timer_check; src/keyboard.h no longer declares
;;;     show_help_echo; the module is boot-loaded.
;;;
;;; The repo root is bound by the .el wrapper as %m33-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m33-imp2.el.

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

;;; --- 1. The module loads and exports the four procedures -----------
(use-modules (emacs menu))

(define (exported? name)
  (let ((p (module-ref (resolve-module '(emacs menu)) name)))
    (procedure? p)))

(check "m33/imp2/export/menu-show-help-event" #t
       (exported? 'menu-show-help-event))
(check "m33/imp2/export/menu-help-callback" #t
       (exported? 'menu-help-callback))
(check "m33/imp2/export/x-menu-timer-wait" #t
       (exported? 'x-menu-timer-wait))
(check "m33/imp2/export/xg-maybe-add-timer-delay" #t
       (exported? 'xg-maybe-add-timer-delay))

;;; --- 2. Runtime: the no-frame help path (no new primitive) ---------
;;; With a #nil frame, menu-show-help-event calls show-help-echo, which
;;; is already a Scheme procedure.  Assert its return value.
(define (safe thunk)
  (catch #t
    (lambda () (cons 'ok (thunk)))
    (lambda (key . args) (cons 'error (cons key args)))))

(let ((r (safe (lambda () (menu-show-help-event #nil "text")))))
  (report "m33/imp2/runtime/show-help-event" (list 'INFO r))
  (check "m33/imp2/runtime/show-help-event-returns-nil" '(ok . #nil) r))

;;; --- 3. Runtime: calls that may need a rebuilt binary --------------
;;; menu-help-callback delegates to (emacs terminal) and reads the
;;; --menu-items primitive; x-menu-timer-wait / xg-maybe-add-timer-delay
;;; read the timers module.  The running binary may lack a freshly
;;; built helper, so print an INFO report and do not assert.
(let ((r (safe (lambda () (menu-help-callback "" 1 2)))))
  (report "m33/imp2/runtime/help-callback" (list 'INFO r)))
(let ((r (safe (lambda () (x-menu-timer-wait)))))
  (report "m33/imp2/runtime/x-menu-timer-wait" (list 'INFO r)))
(let ((r (safe (lambda () (xg-maybe-add-timer-delay)))))
  (report "m33/imp2/runtime/xg-maybe-add-timer-delay" (list 'INFO r)))

;;; --- 4. Static: the module source shapes the decision arms ---------
(define menu-mod (slurp (repo "mod/emacs/menu.scm")))
(if (not menu-mod)
    (report "m33/imp2/scan/module" (cons 'FAIL "mod/emacs/menu.scm missing"))
    (begin
      (check "m33/imp2/module/export-names" #t
             (and (contains? menu-mod "menu-show-help-event")
                  (contains? menu-mod "menu-help-callback")
                  (contains? menu-mod "x-menu-timer-wait")
                  (contains? menu-mod "xg-maybe-add-timer-delay")))
      (check "m33/imp2/module/lazy-help-echo" #t
             (and (contains? menu-mod "show-help-echo")
                  (contains? menu-mod "store-help-event")))
      (check "m33/imp2/module/lazy-timer-check" #t
             (contains? menu-mod "timer-check"))
      (check "m33/imp2/module/delegates-help-callback" #t
             (contains? menu-mod "tty-menu-help-callback"))
      (check "m33/imp2/module/declarative" #t
             (contains? menu-mod "#:declarative? #t"))
      ;; The gtkutil re-arm folds the whole delay into one millisecond
      ;; count: SEC * 1000 + ceiling (NSEC / 1e6).  Pin the ceiling
      ;; division so a wrong divisor or truncation is caught (brief.org
      ;; 3.5, review N2).
      (check "m33/imp2/module/gtkutil-ms-fold" #t
             (contains? menu-mod "(quotient (+ nsec 999999) 1000000)"))))

;;; --- 5. Static: src/xmenu.c calls the dispatchers, old code is gone -
(define xmenu-c (slurp (repo "src/xmenu.c")))
(if (not xmenu-c)
    (report "m33/imp2/scan/xmenu.c" (cons 'FAIL "src/xmenu.c missing"))
    (begin
      (check "m33/imp2/xmenu.c/includes-guile.h" #t
             (contains? xmenu-c "#include \"guile.h\""))
      ;; The three dispatchers exist.
      (check "m33/imp2/xmenu.c/defines-timer-dispatch" #t
             (contains? xmenu-c "x_menu_timer_wait (void)"))
      (check "m33/imp2/xmenu.c/help-event-dispatches" #t
             (contains? xmenu-c "\"emacs menu\", \"menu-show-help-event\""))
      (check "m33/imp2/xmenu.c/help-callback-dispatches" #t
             (contains? xmenu-c "\"emacs menu\", \"menu-help-callback\""))
      ;; The three call sites leave C.
      (check "m33/imp2/xmenu.c/calls-timer-dispatch" #t
             (contains? xmenu-c "x_menu_timer_wait (), *ntp"))
      ;; The timer dispatcher keeps the C-side conversion and copies the
      ;; exact conversion shape of timer_check (keyboard.c).  Pin it so
      ;; the (SEC . NSEC) -> struct timespec fold cannot drift.
      (check "m33/imp2/xmenu.c/timer-dispatch-converts-pair" #t
             (contains? xmenu-c
                       "make_timespec (XFIXNUM (XCAR (result)), XFIXNUM (XCDR (result)))"))
      ;; The old C bodies are gone.
      (check "m33/imp2/xmenu.c/no-old-show-help-echo-call" #f
             (contains? xmenu-c "show_help_echo ("))
      (check "m33/imp2/xmenu.c/no-old-timer-check-call" #f
             (contains? xmenu-c "timer_check ()"))))

;;; --- 6. Static: src/gtkutil.c dispatches, no timer_check -----------
(define gtkutil-c (slurp (repo "src/gtkutil.c")))
(if (not gtkutil-c)
    (report "m33/imp2/scan/gtkutil.c" (cons 'FAIL "src/gtkutil.c missing"))
    (begin
      (check "m33/imp2/gtkutil.c/includes-guile.h" #t
             (contains? gtkutil-c "#include \"guile.h\""))
      (check "m33/imp2/gtkutil.c/timer-delay-dispatches" #t
             (contains? gtkutil-c
                       "\"emacs menu\", \"xg-maybe-add-timer-delay\""))
      (check "m33/imp2/gtkutil.c/no-timer-check" #f
             (contains? gtkutil-c "timer_check"))
      ;; The C keeps the guint range check before it arms g_timeout_add
      ;; (brief.org 4.3, review N2).
      (check "m33/imp2/gtkutil.c/arms-with-guint-bound" #t
             (contains? gtkutil-c "ms <= (long long) (guint) -1"))))

;;; --- 7. Static: src/keyboard.c retires show_help_echo --------------
(define kbd-c (slurp (repo "src/keyboard.c")))
(if (not kbd-c)
    (report "m33/imp2/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m33/imp2/keyboard.c/no-show-help-echo-def" #f
             (contains? kbd-c "show_help_echo (Lisp_Object"))
      ;; M36 imp-1 retired the stub.
      (check "m33/imp2/keyboard.c/timer-check-retired" #f
             (contains? kbd-c "timer_check (void)"))))

;;; --- 8. Static: src/keyboard.h no longer declares the stub ---------
(define kbd-h (slurp (repo "src/keyboard.h")))
(if (not kbd-h)
    (report "m33/imp2/scan/keyboard.h" (cons 'FAIL "src/keyboard.h missing"))
    (check "m33/imp2/keyboard.h/no-show-help-echo" #f
           (contains? kbd-h "show_help_echo")))

;;; --- 9. Static: boot load ------------------------------------------
(define load-scm (slurp (repo "prelude/load.scm")))
(if (not load-scm)
    (report "m33/imp2/scan/load.scm" (cons 'FAIL "prelude/load.scm missing"))
    (check "m33/imp2/load.scm/registers-module" #t
           (contains? load-scm "(emacs menu)")))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m33/imp2/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m33-imp2.el"))
