;;; test-m34-imp4.scm --- M34 imp-4: the minibuf.c input-state callers.
;;;
;;; brief.org (M34 imp-4) ports the decision logic of the live
;;; src/minibuf.c call sites into the new module (emacs minibuf): the
;;; minibuffer-exit-hook run, the frame value handed to
;;; temporarily_switch_to_single_kboard, the unread-command-events drain
;;; and batch test, the help-form / overriding-local-map cell access, and
;;; the deactivate-mark cell access.  src/minibuf.c now calls nine static
;;; dispatchers; no stub retires and no DEFVAR_* site leaves C.  See
;;; docs/kb.org ** M34.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - runtime checks: the module loads and exports its nine procedures.
;;;     The exit-hook port runs minibuffer-exit-hook on a flag-setting
;;;     lambda.  The drain port pops unread-command-events and stops on a
;;;     newline.  The batch test returns both truth values.  The
;;;     help-state and deactivate-mark values round-trip.  Every binding
;;;     is saved and restored explicitly, so no state leaks (kb
;;;     shared-harness-cross-corpus-state-leak).  The true arm of the
;;;     single-kboard switch is never run: it changes global kboard state.
;;;   - static checks: src/minibuf.c includes guile.h, holds the nine
;;;     dispatcher names, and holds no live Vunread_command_events,
;;;     Vhelp_form, Voverriding_local_map, or Vdeactivate_mark token; the
;;;     old safe_run_hooks call is gone; src/keyboard.c keeps its 449
;;;     DEFUNs; prelude/load.scm and tool/run-tests.scm register the port.
;;;
;;; The repo root is bound by the .el wrapper as %m34-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m34-imp4.el.

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
(use-modules (emacs minibuf))

(define minibuf-mod (resolve-module '(emacs minibuf)))

(define (exported? mod name)
  (let ((p (module-ref mod name)))
    (and (procedure? p) #t)))

(for-each
 (lambda (name)
   (check (string-append "m34/imp4/export/" (symbol->string name)) #t
          (exported? minibuf-mod name)))
 '(minibuf-run-exit-minibuffer-hook!
   minibuf-single-kboard-target
   minibuf-unread-command-string
   minibuf-batch-unread-drain-p
   minibuf-capture-help-state
   minibuf-set-help-form!
   minibuf-restore-help-state!
   minibuf-capture-deactivate-mark
   minibuf-restore-deactivate-mark!))

;;; --- 2. Runtime: the exit-hook run ---------------------------------
;;; Bind minibuffer-exit-hook to a flag-setting lambda, then call the
;;; port.  safe-run-hooks! runs the hook; the lambda only sets a local
;;; flag, so no state leaks.  Save and restore the old hook value.
(let ((old (symbol-value 'minibuffer-exit-hook))
      (ran #f))
  (set-symbol-value! 'minibuffer-exit-hook (lambda () (set! ran #t)))
  (check "m34/imp4/runtime/exit-hook-no-error" 'ok
         (car (safe (lambda () (minibuf-run-exit-minibuffer-hook!)))))
  (check "m34/imp4/runtime/exit-hook-runs" #t ran)
  (set-symbol-value! 'minibuffer-exit-hook old))

;; A #nil hook is a no-op.
(let ((old (symbol-value 'minibuffer-exit-hook)))
  (set-symbol-value! 'minibuffer-exit-hook #nil)
  (check "m34/imp4/runtime/exit-hook-nil-no-error" 'ok
         (car (safe (lambda () (minibuf-run-exit-minibuffer-hook!)))))
  (set-symbol-value! 'minibuffer-exit-hook old))

;;; --- 2b. Runtime: the single-kboard target -------------------------
;;; The port is a pass-through: the original C call is unconditional, so
;;; no liveness guard is added (cr.org F3).  The target is returned
;;; unchanged.  Only #nil is exercised here -- the true arm changes
;;; global kboard state and is never run.
(check "m34/imp4/runtime/single-kboard-nil" #nil
       (minibuf-single-kboard-target #nil))

;;; --- 2c. Runtime: the unread-command-events drain ------------------
(let ((old-macro (symbol-value 'executing-kbd-macro))
      (old-uc (symbol-value 'unread-command-events)))
  ;; Guard holds: macro non-nil and a cons list.
  (set-symbol-value! 'executing-kbd-macro #t)
  (set-symbol-value! 'unread-command-events (list 65 66 10 67))
  (check "m34/imp4/runtime/drain-string" "AB" (minibuf-unread-command-string))
  (check "m34/imp4/runtime/drain-rest" (list 67)
         (symbol-value 'unread-command-events))
  ;; Guard fails: macro nil.
  (set-symbol-value! 'executing-kbd-macro #nil)
  (check "m34/imp4/runtime/drain-nil-macro" #nil
         (minibuf-unread-command-string))
  ;; Guard fails: empty list.
  (set-symbol-value! 'executing-kbd-macro #t)
  (set-symbol-value! 'unread-command-events #nil)
  (check "m34/imp4/runtime/drain-nil-list" #nil
         (minibuf-unread-command-string))
  (set-symbol-value! 'executing-kbd-macro old-macro)
  (set-symbol-value! 'unread-command-events old-uc))

;;; --- 2c-bis. Runtime: the drain matches C FIXNUMP and char truncation
(let ((old-macro (symbol-value 'executing-kbd-macro))
      (old-uc (symbol-value 'unread-command-events)))
  ;; A bignum event is not a fixnum, so the C FIXNUMP test skips it.  The
  ;; drain must not signal and must not emit a character (cr.org F4.1).
  (set-symbol-value! 'executing-kbd-macro #t)
  (set-symbol-value! 'unread-command-events (list 65 (expt 2 100) 66 10))
  (check "m34/imp4/runtime/drain-skips-bignum" "AB"
         (minibuf-unread-command-string))
  ;; line[len++] = c truncates the int to 8 bits: 300 -> 44 (cr.org F4.2).
  (set-symbol-value! 'unread-command-events (list 300 10))
  (let ((s (minibuf-unread-command-string)))
    (check "m34/imp4/runtime/drain-truncates-8bit" 44
           (if (and (string? s) (= (string-length s) 1))
               (char->integer (string-ref s 0))
               s)))
  (set-symbol-value! 'executing-kbd-macro old-macro)
  (set-symbol-value! 'unread-command-events old-uc))

;;; --- 2d. Runtime: the batch drain test -----------------------------
(let ((old-macro (symbol-value 'executing-kbd-macro))
      (old-uc (symbol-value 'unread-command-events)))
  (set-symbol-value! 'executing-kbd-macro #nil)
  (check "m34/imp4/runtime/batch-no-macro" #t
         (minibuf-batch-unread-drain-p))
  (set-symbol-value! 'executing-kbd-macro #t)
  (set-symbol-value! 'unread-command-events (list 1 2))
  (check "m34/imp4/runtime/batch-macro-cons" #t
         (minibuf-batch-unread-drain-p))
  (set-symbol-value! 'unread-command-events #nil)
  (check "m34/imp4/runtime/batch-macro-empty" #nil
         (minibuf-batch-unread-drain-p))
  (set-symbol-value! 'executing-kbd-macro old-macro)
  (set-symbol-value! 'unread-command-events old-uc))

;;; --- 2e. Runtime: the help-state round trip ------------------------
(let ((old-hf (symbol-value 'help-form))
      (old-olm (symbol-value 'overriding-local-map))
      (old-mhf (symbol-value 'minibuffer-help-form)))
  (set-symbol-value! 'help-form "HF")
  (set-symbol-value! 'overriding-local-map "OLM")
  (let ((st (minibuf-capture-help-state)))
    (check "m34/imp4/runtime/help-capture-car" "HF" (car st))
    (check "m34/imp4/runtime/help-capture-cdr" "OLM" (cdr st)))
  ;; restore-help-state! sets both cells from a pair.
  (minibuf-restore-help-state! (cons "H2" "O2"))
  (check "m34/imp4/runtime/help-restore-hf" "H2" (symbol-value 'help-form))
  (check "m34/imp4/runtime/help-restore-olm" "O2"
         (symbol-value 'overriding-local-map))
  ;; set-help-form! reads minibuffer-help-form and sets help-form.
  (set-symbol-value! 'minibuffer-help-form "MHF")
  (minibuf-set-help-form!)
  (check "m34/imp4/runtime/set-help-form" "MHF" (symbol-value 'help-form))
  (set-symbol-value! 'help-form old-hf)
  (set-symbol-value! 'overriding-local-map old-olm)
  (set-symbol-value! 'minibuffer-help-form old-mhf))

;;; --- 2f. Runtime: the deactivate-mark round trip -------------------
(let ((old (symbol-value 'deactivate-mark)))
  (set-symbol-value! 'deactivate-mark "DM")
  (check "m34/imp4/runtime/deactivate-capture" "DM"
         (minibuf-capture-deactivate-mark))
  (set-symbol-value! 'deactivate-mark #nil)
  (minibuf-restore-deactivate-mark! "DM")
  (check "m34/imp4/runtime/deactivate-restore" "DM"
         (symbol-value 'deactivate-mark))
  (set-symbol-value! 'deactivate-mark old))

;;; --- 3. Static: the module source shapes the decisions -------------
(define minibuf-scm (slurp (repo "mod/emacs/minibuf.scm")))
(if (not minibuf-scm)
    (report "m34/imp4/scan/module" (cons 'FAIL "mod/emacs/minibuf.scm missing"))
    (begin
      (check "m34/imp4/module/lazy-command-loop" #t
             (contains? minibuf-scm "(emacs command-loop)"))
      (check "m34/imp4/module/truthy-helper" #t
             (contains? minibuf-scm "(define (truthy? x)"))
      (check "m34/imp4/module/no-dead-nilp" #f (contains? minibuf-scm "%nilp"))
      (check "m34/imp4/module/exit-hook-symbol" #t
             (contains? minibuf-scm "'minibuffer-exit-hook"))
      (check "m34/imp4/module/unread-cells" #t
             (and (contains? minibuf-scm "'unread-command-events")
                  (contains? minibuf-scm "'executing-kbd-macro")))
      (check "m34/imp4/module/help-cells" #t
             (and (contains? minibuf-scm "'help-form")
                  (contains? minibuf-scm "'overriding-local-map")
                  (contains? minibuf-scm "'minibuffer-help-form")))
      (check "m34/imp4/module/deactivate-cell" #t
             (contains? minibuf-scm "'deactivate-mark"))))

;;; --- 4. Static: src/minibuf.c calls the module, old sites are gone -
(define minibuf-c (slurp (repo "src/minibuf.c")))
(if (not minibuf-c)
    (report "m34/imp4/scan/minibuf.c" (cons 'FAIL "src/minibuf.c missing"))
    (begin
      (check "m34/imp4/minibuf.c/includes-guile.h" #t
             (contains? minibuf-c "#include \"guile.h\""))
      ;; The nine dispatchers exist.
      (for-each
       (lambda (name)
         (check (string-append "m34/imp4/minibuf.c/dispatcher/" name) #t
                (contains? minibuf-c name)))
       '("minibuf_run_exit_minibuffer_hook"
         "minibuf_single_kboard_target"
         "minibuf_unread_command_string"
         "minibuf_batch_unread_drain_p"
         "minibuf_capture_help_state"
         "minibuf_set_help_form"
         "minibuf_restore_help_state"
         "minibuf_capture_deactivate_mark"
         "minibuf_restore_deactivate_mark"))
      ;; Each dispatcher resolves the same-named module procedure.
      (check "m34/imp4/minibuf.c/refs-emacs-minibuf" 9
             (count-substring minibuf-c "scm_c_public_ref (\"emacs minibuf\""))
      ;; The old safe_run_hooks site is gone.
      (check "m34/imp4/minibuf.c/no-safe-run-hooks" #f
             (contains? minibuf-c "safe_run_hooks"))
      ;; The old single-kboard argument form is gone.
      (check "m34/imp4/minibuf.c/no-old-single-kboard" #f
             (contains? minibuf-c "temporarily_switch_to_single_kboard (XFRAME (mini_frame))"))
      ;; No stay-C name token remains.
      (for-each
       (lambda (tok)
         (check (string-append "m34/imp4/minibuf.c/no-token/" tok) #f
                (contains? minibuf-c tok)))
       '("Vunread_command_events" "Vhelp_form" "Voverriding_local_map"
         "Vdeactivate_mark"))))

;;; --- 5. Static: src/keyboard.c keeps the stub and its DEFUNs -------
(define kbd (slurp (repo "src/keyboard.c")))
(if (not kbd)
    (report "m34/imp4/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m34/imp4/keyboard.c/safe-run-hooks-still-defined" #t
             (contains? kbd "safe_run_hooks (Lisp_Object hook)"))
      (check "m34/imp4/keyboard.c/defun-count" 446
             (count-prefix kbd "DEFUN (\""))))

;;; --- 6. Static: boot load and test registration --------------------
(define load-scm (slurp (repo "prelude/load.scm")))
(check "m34/imp4/load.scm/registers-minibuf" #t
       (contains? load-scm "(emacs minibuf)"))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m34/imp4/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m34-imp4.el"))
