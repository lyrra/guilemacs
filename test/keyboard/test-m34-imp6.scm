;;; test-m34-imp6.scm --- M34 imp-6: the xdisp.c part-2 kboard + name
;;;                       readers.
;;;
;;; brief.org (M34 imp-6) ports the decision logic of the five live
;;; src/xdisp.c part-2 call sites into the module (emacs xdisp): the two
;;; push_kboard callers (S1 display_mode_line, S3 Fformat_mode_line),
;;; the two pop_kboard callers (S2, S4), and the three
;;; Voverriding_local_map_menu_flag readers (S5 update_menu_bar,
;;; update_tab_bar, update_tool_bar).  src/xdisp.c now calls three new
;;; static dispatchers; push_kboard and pop_kboard keep their C
;;; definitions at this imp (they are the (emacs single-kboard)
;;; dispatchers); imp-7 later retired the push side.  The
;;; overriding-local-map-menu-flag DEFVAR_LISP stays C; no stub retires
;;; at this imp and no keyboard.c line changes.  See docs/kb.org ** M34.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - runtime checks: the module loads and exports its six
;;;     procedures.  push/pop runs on the live current kboard smob
;;;     without error and restores the (emacs single-kboard) state
;;;     (push then pop is net zero).  The S5 reader returns #nil for a
;;;     #nil cell and a non-nil value for a non-nil cell; every binding
;;;     is saved and a previously-void cell is restored with makunbound,
;;;     so no state leaks (kb shared-harness-cross-corpus-state-leak).
;;;   - static checks: mod/emacs/xdisp.scm shapes the decisions with
;;;     lazy cross-module refs and no eager (emacs single-kboard)
;;;     import; src/xdisp.c includes guile.h, holds the three new
;;;     dispatcher names, has exactly six scm_c_public_ref ("emacs
;;;     xdisp" sites, and holds no old site text; src/keyboard.c holds
;;;     no push_kboard and no pop_kboard (imp-7 retired push_kboard,
;;;     M36 imp-2 retired pop_kboard) and 446 DEFUNs;
;;;     prelude/load.scm and tool/run-tests.scm register the port.
;;;
;;; The repo root is bound by the .el wrapper as %m34-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m34-imp6.el.

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

(define (count-substring text needle)
  (let loop ((start 0) (n 0))
    (let ((i (string-contains text needle start)))
      (if i (loop (+ i 1) (+ n 1)) n))))

(define (count-prefix text prefix)
  "Count the lines of TEXT that start with PREFIX.  This is the anchored
count -- a loose substring match would also count a comment line
(kb defun-count-anchor)."
  (if (not (string? text))
      0
      (call-with-input-string text
        (lambda (port)
          (let loop ((n 0))
            (let ((line (read-line port)))
              (cond ((eof-object? line) n)
                    ((string-prefix? prefix line) (loop (1+ n)))
                    (else (loop n)))))))))

(define (repo path) (string-append %m34-root "/" path))

(define (safe thunk)
  (catch #t
    (lambda () (cons 'ok (thunk)))
    (lambda (key . args) (cons 'error (cons key args)))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m34-root))
    (begin (report "m34-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m34-root "."))
    (report "m34-root-bound" 'PASS))

;;; --- 1. The module loads and exports its procedures ----------------
(use-modules (emacs xdisp))

(define xdisp-mod (resolve-module '(emacs xdisp)))

(define (exported? mod name)
  (let ((p (module-ref mod name)))
    (and (procedure? p) #t)))

;; The six procedures: three imp-5 names plus three imp-6 names.
(for-each
 (lambda (name)
   (check (string-append "m34/imp6/export/" (symbol->string name)) #t
          (exported? xdisp-mod name)))
 '(xdisp-run-activate-menubar-hook!
   xdisp-run-menu-bar-update-hook!
   xdisp-run-window-scroll-functions!
   xdisp-push-kboard!
   xdisp-pop-kboard!
   xdisp-overriding-local-map-menu-flag-p))

;;; --- 2. Runtime: the push/pop pair --------------------------------
;;; Bind a kboard smob from the live C state.  current-kboard returns a
;;; KBOARD smob (M2).  push then pop is net zero on the
;;; (emacs single-kboard) kboard-stack, so no state leaks.
(define (%c name) (symbol-function name))
(define %void (list 'void))

(define (cell-read name)
  (if ((%c 'boundp) name) (symbol-value name) %void))

(define (current-kboard-smob)
  ((%c 'current-kboard)))

(let ((r (safe current-kboard-smob)))
  (if (and (pair? r) (eq? (car r) 'ok))
      (let ((kb (cdr r)))
        (check "m34/imp6/runtime/push-no-error" 'ok
               (car (safe (lambda () (xdisp-push-kboard! kb)))))
        ;; Restore the stack in every case: if push consed and then
        ;; failed, pop still removes the one entry it added.
        (check "m34/imp6/runtime/pop-no-error" 'ok
               (car (safe (lambda () (xdisp-pop-kboard!))))))
      (report "m34/imp6/runtime/current-kboard"
              (cons 'FAIL (format "current-kboard failed: %S" r)))))

;;; --- 3. Runtime: the S5 cell reader --------------------------------
;;; Read the cell with boundp, and restore a previously-void cell with
;;; makunbound (the imp-5 F4 fix), so no cell state leaks.
(let ((old (cell-read 'overriding-local-map-menu-flag)))
  ;; nil arm: an elisp nil cell.
  (set-symbol-value! 'overriding-local-map-menu-flag #nil)
  (check "m34/imp6/runtime/s5-nil" #nil
         (xdisp-overriding-local-map-menu-flag-p))
  ;; non-nil arm: a non-nil cell yields elisp t.  In guilemacs Qt is
  ;; SCM_BOOL_T, i.e. the Scheme #t (src/lread.c:2878), so the reader
  ;; must return #t exactly -- not merely some non-#nil value (cr.org
  ;; F3).  This pins the brief.org 5.4 Qt/Qnil contract.
  (set-symbol-value! 'overriding-local-map-menu-flag #t)
  (check "m34/imp6/runtime/s5-t" #t
         (xdisp-overriding-local-map-menu-flag-p))
  ;; Any other non-nil value is normalized to elisp t (brief.org 5.5).
  (set-symbol-value! 'overriding-local-map-menu-flag 'some-symbol)
  (check "m34/imp6/runtime/s5-non-nil-normalized" #t
         (xdisp-overriding-local-map-menu-flag-p))
  ;; Restore: a previously-void cell returns to void, not to elisp nil.
  (if (eq? old %void)
      ((%c 'makunbound) 'overriding-local-map-menu-flag)
      (set-symbol-value! 'overriding-local-map-menu-flag old))
  (check "m34/imp6/runtime/s5-restored" old
         (cell-read 'overriding-local-map-menu-flag)))

;;; --- 4. Static: the module source shapes the decisions -------------
(define xdisp-scm (slurp (repo "mod/emacs/xdisp.scm")))
(if (not xdisp-scm)
    (report "m34/imp6/scan/module" (cons 'FAIL "mod/emacs/xdisp.scm missing"))
    (begin
      (check "m34/imp6/module/lazy-single-kboard" #t
             (contains? xdisp-scm "'push-kboard!"))
      (check "m34/imp6/module/lazy-pop-kboard" #t
             (contains? xdisp-scm "'pop-kboard!"))
      (check "m34/imp6/module/no-eager-import" #f
             (contains? xdisp-scm "#:use-module (emacs single-kboard)"))
      (check "m34/imp6/module/s5-symbol" #t
             (contains? xdisp-scm "'overriding-local-map-menu-flag"))
      (check "m34/imp6/module/symbol-value-ref" #t
             (contains? xdisp-scm "(defelisp %symbol-value symbol-value)"))
      (check "m34/imp6/module/keeps-imp5-safe-run-hooks" #t
             (contains? xdisp-scm "'safe-run-hooks!"))))

;;; --- 5. Static: src/xdisp.c calls the module, old sites are gone ---
(define xdisp-c (slurp (repo "src/xdisp.c")))
(if (not xdisp-c)
    (report "m34/imp6/scan/xdisp.c" (cons 'FAIL "src/xdisp.c missing"))
    (begin
      (check "m34/imp6/xdisp.c/includes-guile.h" #t
             (contains? xdisp-c "#include \"guile.h\""))
      ;; The three new dispatchers exist.
      (for-each
       (lambda (name)
         (check (string-append "m34/imp6/xdisp.c/dispatcher/" name) #t
                (contains? xdisp-c name)))
       '("xdisp_push_kboard"
         "xdisp_pop_kboard"
         "xdisp_overriding_local_map_menu_flag_p"))
      ;; Exactly six scm_c_public_ref ("emacs xdisp" sites: 3 from imp-5,
      ;; 3 from imp-6.
      (check "m34/imp6/xdisp.c/refs-emacs-xdisp" 6
             (count-substring xdisp-c "scm_c_public_ref (\"emacs xdisp\""))
      ;; The old S1/S3 and S2/S4 site text is gone (anchored with the
      ;; two leading spaces, so the new xdisp_ dispatcher names do not
      ;; match).
      (check "m34/imp6/xdisp.c/no-old-push" #f
             (contains? xdisp-c "\n  push_kboard (FRAME_KBOARD"))
      (check "m34/imp6/xdisp.c/no-old-pop" #f
             (contains? xdisp-c "\n  pop_kboard ();"))
      ;; The old S5 test is gone.
      (check "m34/imp6/xdisp.c/no-old-s5" #f
             (contains? xdisp-c "NILP (Voverriding_local_map_menu_flag)"))))

;;; --- 6. Static: src/keyboard.c keeps the stubs and its DEFUNs ------
(define kbd (slurp (repo "src/keyboard.c")))
(if (not kbd)
    (report "m34/imp6/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      ;; M34 imp-7 retired push_kboard (its last caller, xdisp.c, left C
      ;; at this imp); M36 imp-2 retired pop_kboard.  The anchored form
      ;; starts the match at a line start, so the static kbd_pop_kboard
      ;; dispatcher is not a bare pop_kboard token (cr.org G2).
      (check "m34/imp6/keyboard.c/push-retired" #f
             (contains? kbd "push_kboard (struct kboard *k)"))
      (check "m34/imp6/keyboard.c/pop-retired" #f
             (contains? kbd "\npop_kboard (void)"))
      (check "m34/imp6/keyboard.c/defun-count" 446
             (count-prefix kbd "DEFUN (\""))))

;;; --- 7. Static: boot load and test registration --------------------
(define load-scm (slurp (repo "prelude/load.scm")))
(check "m34/imp6/load.scm/registers-xdisp" #t
       (contains? load-scm "(emacs xdisp)"))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m34/imp6/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m34-imp6.el"))
