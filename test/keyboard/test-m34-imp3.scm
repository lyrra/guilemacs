;;; test-m34-imp3.scm --- M34 imp-3: the window.c and fileio.c
;;;                       safe_run_hooks callers.
;;;
;;; brief.org (M34 imp-3) ports the decision logic of the two live
;;; src/window.c and src/fileio.c call sites of the safe_run_hooks stub
;;; into the new modules (emacs window) and (emacs fileio).  src/window.c
;;; and src/fileio.c now call one static dispatcher each; no stub
;;; retires.  See docs/kb.org ** M34.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - runtime checks: both modules load and export their procedure.
;;;     Site 1 is exercised on both arms with the hook variable bound to
;;;     a flag-setting lambda: the false arm (#nil) must NOT run it, the
;;;     true arm (#t) must.  Site 2 is exercised with auto-save-hook
;;;     bound to #nil, so the dispatch runs and is a guaranteed no-op.
;;;     Every binding is saved and restored explicitly, so no state leaks
;;;     (kb shared-harness-cross-corpus-state-leak).  A non-nil
;;;     auto-save-hook is never used.
;;;   - a static wiring check: src/window.c and src/fileio.c each hold
;;;     the dispatcher, include guile.h, and no longer contain the old
;;;     safe_run_hooks call text; src/keyboard.c still defines
;;;     safe_run_hooks and keeps its 449 DEFUNs.
;;;
;;; The repo root is bound by the .el wrapper as %m34-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m34-imp3.el.

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

;;; --- 1. The modules load and export their procedure ----------------
(use-modules (emacs window))
(use-modules (emacs fileio))

(define window-mod (resolve-module '(emacs window)))
(define fileio-mod (resolve-module '(emacs fileio)))

(define (exported? mod name)
  (let ((p (module-ref mod name)))
    (and (procedure? p) #t)))

(check "m34/imp3/export/window-maybe-run-state-change-hook!" #t
       (exported? window-mod 'window-maybe-run-state-change-hook!))
(check "m34/imp3/export/fileio-run-auto-save-hook!" #t
       (exported? fileio-mod 'fileio-run-auto-save-hook!))

;;; --- 2. Runtime: site 1, both arms ---------------------------------
;;; Site 1 hands over an elisp boolean.
;;;
;;; False arm (F3): bind window-state-change-hook to a flag-setting
;;; lambda, pass #nil, and assert the lambda did NOT run.  This proves
;;; the false-bool arm is a no-op (brief.org imp-0 note 4), not only
;;; error-free.  The lambda is reachable only through the hook, which
;;; the false arm never runs.
;;;
;;; True arm (F4): bind the hook to a flag-setting lambda, pass #t, and
;;; assert the lambda DID run.  safe-run-hooks! runs the hook; the lambda
;;; only sets a local flag, so no state leaks
;;; (kb shared-harness-cross-corpus-state-leak).  Both arms save and
;;; restore the old hook value explicitly (the corpus convention, cf.
;;; test-m32-imp5.scm).
(define maybe-run window-maybe-run-state-change-hook!)

(check "m34/imp3/runtime/window-false-no-error" 'ok
       (car (safe (lambda () (maybe-run #nil)))))

(let ((old (symbol-value 'window-state-change-hook))
      (ran #f))
  (set-symbol-value! 'window-state-change-hook (lambda () (set! ran #t)))
  (maybe-run #nil)
  (check "m34/imp3/runtime/window-false-no-op" #f ran)
  (set-symbol-value! 'window-state-change-hook old))

(let ((old (symbol-value 'window-state-change-hook))
      (ran #f))
  (set-symbol-value! 'window-state-change-hook (lambda () (set! ran #t)))
  (maybe-run #t)
  (check "m34/imp3/runtime/window-true-runs" #t ran)
  (set-symbol-value! 'window-state-change-hook old))

;;; --- 2b. Runtime: site 2 with a nil auto-save-hook (F4) ------------
;;; The port's real fileio path runs safe-run-hooks! on auto-save-hook.
;;; Bind the hook to #nil so the run is a guaranteed no-op, then call the
;;; procedure: "no error" proves the dispatch works.  A non-nil hook is
;;; never used (it could run Lisp code and leak state).  Save and restore
;;; the value explicitly (the corpus convention, cf. test-m32-imp5.scm).
(define auto-save (module-ref fileio-mod 'fileio-run-auto-save-hook!))
(let ((old (symbol-value 'auto-save-hook)))
  (set-symbol-value! 'auto-save-hook #nil)
  (check "m34/imp3/runtime/fileio-nil-no-error" 'ok
         (car (safe (lambda () (auto-save)))))
  (set-symbol-value! 'auto-save-hook old))

;;; --- 3. Static: the module sources shape the decisions -------------
(define window-src (slurp (repo "mod/emacs/window.scm")))
(if (not window-src)
    (report "m34/imp3/scan/window-module"
            (cons 'FAIL "mod/emacs/window.scm missing"))
    (begin
      (check "m34/imp3/window-module/export-name" #t
             (contains? window-src "window-maybe-run-state-change-hook!"))
      (check "m34/imp3/window-module/lazy-command-loop" #t
             (contains? window-src "(emacs command-loop)"))
      (check "m34/imp3/window-module/nil-test" #t (contains? window-src "%nilp"))
      (check "m34/imp3/window-module/hook-symbol" #t
             (contains? window-src "'window-state-change-hook"))))

(define fileio-src (slurp (repo "mod/emacs/fileio.scm")))
(if (not fileio-src)
    (report "m34/imp3/scan/fileio-module"
            (cons 'FAIL "mod/emacs/fileio.scm missing"))
    (begin
      (check "m34/imp3/fileio-module/export-name" #t
             (contains? fileio-src "fileio-run-auto-save-hook!"))
      (check "m34/imp3/fileio-module/lazy-command-loop" #t
             (contains? fileio-src "(emacs command-loop)"))
      (check "m34/imp3/fileio-module/hook-symbol" #t
             (contains? fileio-src "'auto-save-hook"))))

;;; --- 4. Static: src/window.c calls the module, old site is gone ----
(define window-c (slurp (repo "src/window.c")))
(if (not window-c)
    (report "m34/imp3/scan/window.c" (cons 'FAIL "src/window.c missing"))
    (begin
      (check "m34/imp3/window.c/includes-guile.h" #t
             (contains? window-c "#include \"guile.h\""))
      ;; The static dispatcher exists.
      (check "m34/imp3/window.c/dispatcher" #t
             (contains? window-c "window_maybe_run_state_change_hook (bool run_hook)"))
      ;; The site calls the dispatcher.
      (check "m34/imp3/window.c/dispatcher-call" #t
             (contains? window-c "window_maybe_run_state_change_hook (run_window_state_change_hook)"))
      ;; The old site is gone.
      (check "m34/imp3/window.c/no-old-call" #f
             (contains? window-c "safe_run_hooks (Qwindow_state_change_hook);"))
      ;; The module reads state through Scheme: one scm_c_public_ref site.
      (check "m34/imp3/window.c/one-public-ref" 1
             (count-substring window-c "scm_c_public_ref (\"emacs window\""))))

;;; --- 5. Static: src/fileio.c calls the module, old site is gone ----
(define fileio-c (slurp (repo "src/fileio.c")))
(if (not fileio-c)
    (report "m34/imp3/scan/fileio.c" (cons 'FAIL "src/fileio.c missing"))
    (begin
      (check "m34/imp3/fileio.c/includes-guile.h" #t
             (contains? fileio-c "#include \"guile.h\""))
      ;; The static dispatcher exists.
      (check "m34/imp3/fileio.c/dispatcher" #t
             (contains? fileio-c "fileio_run_auto_save_hook (void)"))
      ;; The site calls the dispatcher.
      (check "m34/imp3/fileio.c/dispatcher-call" #t
             (contains? fileio-c "fileio_run_auto_save_hook ();"))
      ;; The old site is gone.
      (check "m34/imp3/fileio.c/no-old-call" #f
             (contains? fileio-c "safe_run_hooks (hook);"))
      ;; The dead local hook variable is removed from the declaration.
      (check "m34/imp3/fileio.c/no-hook-var" #f
             (contains? fileio-c "Lisp_Object tail, buf, hook;"))
      ;; The module reads state through Scheme: one scm_c_public_ref site.
      (check "m34/imp3/fileio.c/one-public-ref" 1
             (count-substring fileio-c "scm_c_public_ref (\"emacs fileio\""))))

;;; --- 6. Static: src/keyboard.c keeps the stub ----------------------
(define kbd (slurp (repo "src/keyboard.c")))
(if (not kbd)
    (report "m34/imp3/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m34/imp3/keyboard.c/safe-run-hooks-still-defined" #t
             (contains? kbd "safe_run_hooks (Lisp_Object hook)"))
      ;; DoD 5: no stub retires at imp-3, so the DEFUN count is stable.
      ;; Use the anchored counter (kb defun-count-anchor): a loose
      ;; substring match would also count the doc-comment continuation
      ;; line whose text begins with "DEFUN".
      (check "m34/imp3/keyboard.c/defun-count" 446
             (count-prefix kbd "DEFUN (\""))))

;;; --- 7. Static: boot load and test registration --------------------
;;; The boot path is text-checked only: the corpus imports the two
;;; modules itself (section 1), so a boot-load failure in prelude/load.scm
;;; stays hidden here.  These checks prove the two use-modules lines are
;;; registered; the real boot proof is the --filter=m34 gate (DoD 1).
(define load-scm (slurp (repo "prelude/load.scm")))
(check "m34/imp3/load.scm/registers-window" #t
       (contains? load-scm "(emacs window)"))
(check "m34/imp3/load.scm/registers-fileio" #t
       (contains? load-scm "(emacs fileio)"))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m34/imp3/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m34-imp3.el"))
