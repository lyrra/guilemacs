;;; test-m34-imp5.scm --- M34 imp-5: the xdisp.c part-1 hook callers.
;;;
;;; brief.org (M34 imp-5) ports the decision logic of the three live
;;; src/xdisp.c hook call sites into the new module (emacs xdisp): the
;;; Lucid activate-menubar-hook run (S1), the menu-bar-update-hook run
;;; (S2), and the window-scroll-functions run (S3).  src/xdisp.c now
;;; calls three static dispatchers; site S4 (the tool-bar event store)
;;; stays C (Option B).  No stub retires at this imp and no DEFVAR_*
;;; site leaves C; imp-7 later retired safe_run_hooks_2.  See
;;; docs/kb.org ** M34.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - runtime checks: the module loads and exports its three
;;;     procedures.  Each of the three hook ports runs its hook on a
;;;     flag-setting lambda, and a #nil hook is a no-op.  Every binding
;;;     is saved and restored explicitly, so no state leaks (kb
;;;     shared-harness-cross-corpus-state-leak).
;;;   - static checks: src/xdisp.c includes guile.h, holds the three
;;;     dispatcher names, has exactly three scm_c_public_ref sites for
;;;     (emacs xdisp), and holds no live safe_run_hooks text for S1/S2;
;;;     src/keyboard.c keeps its 449 DEFUNs; prelude/load.scm and
;;;     tool/run-tests.scm register the port.
;;;
;;; The repo root is bound by the .el wrapper as %m34-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m34-imp5.el.

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

(for-each
 (lambda (name)
   (check (string-append "m34/imp5/export/" (symbol->string name)) #t
          (exported? xdisp-mod name)))
 '(xdisp-run-activate-menubar-hook!
   xdisp-run-menu-bar-update-hook!
   xdisp-run-window-scroll-functions!))

;;; --- 2. Runtime: S1, the activate-menubar-hook run ----------------
;;; Helpers for the hook cells.  activate-menubar-hook has no C DEFVAR
;;; (only a DEFSYM in src/keyboard-globals.c), so it is void in the
;;; minimal test runtime; a plain symbol-value read signals
;;; void-variable.  Read with boundp, and restore a previously-void cell
;;; to *void* with makunbound, not to elisp nil, so no cell state leaks
;;; (kb shared-harness-cross-corpus-state-leak; cr.org F4).  The two
;;; states behave the same in run-hook-with-args-1, but keeping the cell
;;; void is the exact pre-test state.
;;; menu-bar-update-hook and window-scroll-functions are C DEFVAR_LISPs
;;; and stay bound.
(define (%c name) (symbol-function name))
(define %void (list 'void))
(define (hook-read name)
  (if ((%c 'boundp) name) (symbol-value name) %void))
(define (hook-write! name v)
  (set-symbol-value! name v))
(define (hook-restore! name old)
  (if (eq? old %void)
      ((%c 'makunbound) name)
      (hook-write! name old)))

;; Bind activate-menubar-hook to a flag-setting lambda, then call the
;; port.  safe-run-hooks! runs the hook; the lambda only sets a local
;; flag, so no state leaks.  Save and restore the old hook value.
(let ((old (hook-read 'activate-menubar-hook))
      (was-void (eq? (hook-read 'activate-menubar-hook) %void))
      (ran #f))
  (hook-write! 'activate-menubar-hook (lambda () (set! ran #t)))
  (check "m34/imp5/runtime/activate-no-error" 'ok
         (car (safe (lambda () (xdisp-run-activate-menubar-hook!)))))
  (check "m34/imp5/runtime/activate-runs" #t ran)
  (hook-restore! 'activate-menubar-hook old)
  ;; cr.org F4: the cell was void before the block.  The restore must
  ;; return it to void, not leave it bound to elisp nil.  No caller reads
  ;; the difference, but the cell state must not leak.
  (check "m34/imp5/runtime/activate-void-restored" was-void
         (eq? (hook-read 'activate-menubar-hook) %void)))

;; A #nil hook is a no-op.
(let ((old (hook-read 'activate-menubar-hook)))
  (hook-write! 'activate-menubar-hook #nil)
  (check "m34/imp5/runtime/activate-nil-no-error" 'ok
         (car (safe (lambda () (xdisp-run-activate-menubar-hook!)))))
  (hook-restore! 'activate-menubar-hook old))

;;; --- 2b. Runtime: S2, the menu-bar-update-hook run ----------------
(let ((old (hook-read 'menu-bar-update-hook))
      (ran #f))
  (hook-write! 'menu-bar-update-hook (lambda () (set! ran #t)))
  (check "m34/imp5/runtime/menu-bar-no-error" 'ok
         (car (safe (lambda () (xdisp-run-menu-bar-update-hook!)))))
  (check "m34/imp5/runtime/menu-bar-runs" #t ran)
  (hook-restore! 'menu-bar-update-hook old))

(let ((old (hook-read 'menu-bar-update-hook)))
  (hook-write! 'menu-bar-update-hook #nil)
  (check "m34/imp5/runtime/menu-bar-nil-no-error" 'ok
         (car (safe (lambda () (xdisp-run-menu-bar-update-hook!)))))
  (hook-restore! 'menu-bar-update-hook old))

;;; --- 2c. Runtime: S3, the window-scroll-functions run -------------
;;; safe-run-hooks-2! calls the hook with two arguments: the window and
;;; the start fixnum.  The port passes both through to the hook.
(let ((old (hook-read 'window-scroll-functions))
      (got-w #f)
      (got-s #f))
  (hook-write! 'window-scroll-functions
               (lambda (w s) (set! got-w w) (set! got-s s)))
  (check "m34/imp5/runtime/scroll-no-error" 'ok
         (car (safe (lambda ()
                      (xdisp-run-window-scroll-functions! 'W 'S)))))
  (check "m34/imp5/runtime/scroll-passes-window" 'W got-w)
  (check "m34/imp5/runtime/scroll-passes-start" 'S got-s)
  (hook-restore! 'window-scroll-functions old))

(let ((old (hook-read 'window-scroll-functions)))
  (hook-write! 'window-scroll-functions #nil)
  (check "m34/imp5/runtime/scroll-nil-no-error" 'ok
         (car (safe (lambda ()
                      (xdisp-run-window-scroll-functions! #nil #nil)))))
  (hook-restore! 'window-scroll-functions old))

;;; --- 3. Static: the module source shapes the decisions -------------
(define xdisp-scm (slurp (repo "mod/emacs/xdisp.scm")))
(if (not xdisp-scm)
    (report "m34/imp5/scan/module" (cons 'FAIL "mod/emacs/xdisp.scm missing"))
    (begin
      (check "m34/imp5/module/lazy-command-loop" #t
             (contains? xdisp-scm "(emacs command-loop)"))
      (check "m34/imp5/module/no-eager-import" #f
             (contains? xdisp-scm "#:use-module (emacs command-loop)"))
      (check "m34/imp5/module/lazy-safe-run-hooks-2" #t
             (contains? xdisp-scm "'safe-run-hooks-2!"))
      (check "m34/imp5/module/no-dead-helper" #f
             (contains? xdisp-scm "(define (truthy? x)"))
      (check "m34/imp5/module/activate-symbol" #t
             (contains? xdisp-scm "'activate-menubar-hook"))
      (check "m34/imp5/module/menu-bar-symbol" #t
             (contains? xdisp-scm "'menu-bar-update-hook"))
      (check "m34/imp5/module/scroll-symbol" #t
             (contains? xdisp-scm "'window-scroll-functions"))))

;;; --- 4. Static: src/xdisp.c calls the module, old sites are gone ---
(define xdisp-c (slurp (repo "src/xdisp.c")))
(if (not xdisp-c)
    (report "m34/imp5/scan/xdisp.c" (cons 'FAIL "src/xdisp.c missing"))
    (begin
      (check "m34/imp5/xdisp.c/includes-guile.h" #t
             (contains? xdisp-c "#include \"guile.h\""))
      ;; The three dispatchers exist.
      (for-each
       (lambda (name)
         (check (string-append "m34/imp5/xdisp.c/dispatcher/" name) #t
                (contains? xdisp-c name)))
       '("xdisp_run_activate_menubar_hook"
         "xdisp_run_menu_bar_update_hook"
         "xdisp_run_window_scroll_functions"))
      ;; Each dispatcher resolves the same-named module procedure.  Count
      ;; the three imp-5 refs by their module-procedure names, so the
      ;; three imp-6 refs (test-m34-imp6.scm) do not disturb this check.
      (check "m34/imp5/xdisp.c/refs-emacs-xdisp" 3
             (count-substring xdisp-c "\"xdisp-run-"))
      ;; The old S1/S2 site text is gone.
      (check "m34/imp5/xdisp.c/no-old-activate" #f
             (contains? xdisp-c "safe_run_hooks (Qactivate_menubar_hook)"))
      (check "m34/imp5/xdisp.c/no-old-menu-bar" #f
             (contains? xdisp-c "safe_run_hooks (Qmenu_bar_update_hook)"))
      ;; No safe_run_hooks text at all remains in xdisp.c.
      (check "m34/imp5/xdisp.c/no-safe-run-hooks" #f
             (contains? xdisp-c "safe_run_hooks"))))

;;; --- 5. Static: src/keyboard.c retired the stub, keeps its DEFUNs --
(define kbd (slurp (repo "src/keyboard.c")))
(if (not kbd)
    (report "m34/imp5/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      ;; M34 imp-7 retired safe_run_hooks_2 (its last caller, xdisp.c
      ;; S3, left C at this imp).  The definition is gone.
      (check "m34/imp5/keyboard.c/safe-run-hooks-2-retired" #f
             (contains? kbd "safe_run_hooks_2 (Lisp_Object hook, Lisp_Object arg1"))
      (check "m34/imp5/keyboard.c/defun-count" 449
             (count-prefix kbd "DEFUN (\""))))

;;; --- 6. Static: boot load and test registration --------------------
(define load-scm (slurp (repo "prelude/load.scm")))
(check "m34/imp5/load.scm/registers-xdisp" #t
       (contains? load-scm "(emacs xdisp)"))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m34/imp5/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m34-imp5.el"))
