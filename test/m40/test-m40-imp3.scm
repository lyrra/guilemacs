;;; test-m40-imp3.scm --- M40 imp-3: the residual Group A accessors.
;;;
;;; brief.org (M40 imp-3) moves the *decision* of two residual
;;; src/process.c Group A accessors into the module
;;; (emacs process-accessors):
;;;
;;;   process-tty-name                   -- a multi-slot read of
;;;                                         tty_name / stderrproc /
;;;                                         pty_in / pty_out plus the
;;;                                         stdin / stdout / stderr
;;;                                         stream test.
;;;   process-inherit-coding-system-flag -- a plain read of the
;;;                                         inherit_coding_system_flag
;;;                                         slot.
;;;
;;; The struct slots stay C: each body reads them through the
;;; table-driven C bridge --process-ref (the imp-3 read rows tty_name,
;;; stderrproc, pty_in, pty_out).  The elisp names are kept.  The other
;;; 10 residual Group A names stay C.
;;;
;;; Two kinds of check: the runtime value of each accessor against the C
;;; rule (the C rule is expressed here by reading the slots through the
;;; same bridge), and a static scan of the module, src/process.c, and the
;;; harness registration.
;;;
;;; The repo root is bound by the .el wrapper as %m40-root.  The .el
;;; wrapper creates the live processes the runtime checks use (a pty
;;; process and a pipe process) and looks them up by name; when no
;;; command is available the runtime checks are INFO-skipped.  The .el
;;; wrapper turns each (NAME PASS|FAIL) pair into an ERT test; see
;;; test/m40/test-m40-imp3.el.

(use-modules (srfi srfi-13))
(use-modules (ice-9 popen))

(use-modules (emacs-elisp runtime))
(use-modules (emacs process-accessors))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (info name text)
  (report name (list 'INFO text)))

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

(define (repo path) (string-append %m40-root "/" path))

(define (contains? text needle)
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (export-region text)
  "Return the text of the module's #:export form, or #f when TEXT is
absent or holds no #:export form.  The export check uses this so the
needle does not pin the indentation or the line layout of the export
list."
  (if (not (string? text))
      #f
      (let ((start (string-contains text "#:export (")))
        (if (not start)
            #f
            (let ((end (string-contains text ")" start)))
              (and end (substring text start end)))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m40-root))
    (begin (report "m40-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m40-root "."))
    (report "m40-root-bound" 'PASS))

;;; --- 1. The module loads and exports the new procedures ------------
(define tty-name
  (module-ref (resolve-module '(emacs process-accessors))
              'elisp-process-tty-name))
(define inherit-flag
  (module-ref (resolve-module '(emacs process-accessors))
              'elisp-process-inherit-coding-system-flag))

(check "m40/imp3/export/process-tty-name" #t
       (and (defined? 'tty-name) (procedure? tty-name)))
(check "m40/imp3/export/process-inherit-coding-system-flag" #t
       (and (defined? 'inherit-flag) (procedure? inherit-flag)))

;;; --- 2. The elisp names exist and resolve to the module procedures --
(define (elisp-fn name) (symbol-function name))
(define (ptn proc . args) (apply tty-name proc args))
(define (icf proc) (inherit-flag proc))

(check "m40/imp3/elisp/process-tty-name-installed" #t
       (eq? (elisp-fn 'process-tty-name) tty-name))
(check "m40/imp3/elisp/process-inherit-coding-system-flag-installed" #t
       (eq? (elisp-fn 'process-inherit-coding-system-flag) inherit-flag))

;;; --- 3. Runtime: the accessors match the C rule on live processes ----
;;;
;;; The C rule is reproduced here by reading the slots through the same
;;; bridge the module uses, so the check is independent of the module
;;; body's branch spelling.  The .el wrapper created the two processes;
;;; get-process is a kept C DEFUN.
(define (get-process name) ((symbol-function 'get-process) name))
(define (ref proc name) ((symbol-function '--process-ref) proc name))

(define pty (get-process "m40-imp3-pty"))
(define pipe (get-process "m40-imp3-pipe"))
(define have-pty (not (eq? pty #nil)))
(define have-pipe (not (eq? pipe #nil)))

(define (expected-tty proc stream)
  "The C branch rule of process-tty-name, expressed through the bridge."
  (let ((tty (ref proc 'tty_name)))
    (cond
      ((eq? stream #nil) tty)
      ((eq? stream 'stdin) (if (eq? (ref proc 'pty_in) #nil) #nil tty))
      ((eq? stream 'stdout) (if (eq? (ref proc 'pty_out) #nil) #nil tty))
      ((eq? stream 'stderr)
       (if (and (not (eq? (ref proc 'pty_out) #nil))
                (eq? (ref proc 'stderrproc) #nil))
           tty #nil))
      (else #nil))))

(define (signals? thunk)
  "True when THUNK raises any error."
  (catch #t (lambda () (thunk) #f) (lambda args #t)))

(if (not have-pty)
    (info "m40/imp3/runtime/pty" "no pty process (no command available)")
    (begin
      ;; A pty process has a real tty name; some batch builds allocate no
      ;; pty, so the name may also be nil.  Either way the nil-stream
      ;; branch returns the slot value unchanged (checked below).
      (check "m40/imp3/runtime/pty/nil-stream-is-string" #t
             (or (eq? (ptn pty) #nil) (string? (ptn pty))))
      (check "m40/imp3/runtime/pty/nil-stream" (expected-tty pty #nil)
             (ptn pty))
      (check "m40/imp3/runtime/pty/stdin" (expected-tty pty 'stdin)
             (ptn pty 'stdin))
      (check "m40/imp3/runtime/pty/stdout" (expected-tty pty 'stdout)
             (ptn pty 'stdout))
      (check "m40/imp3/runtime/pty/stderr" (expected-tty pty 'stderr)
             (ptn pty 'stderr))
      (check "m40/imp3/runtime/pty/matches-c-rule" #t
             (and (equal? (ptn pty) (expected-tty pty #nil))
                  (equal? (ptn pty 'stdin) (expected-tty pty 'stdin))
                  (equal? (ptn pty 'stdout) (expected-tty pty 'stdout))
                  (equal? (ptn pty 'stderr) (expected-tty pty 'stderr))))
      ;; The unknown-stream branch signals an error (the C rule did
      ;; signal_error).
      (check "m40/imp3/runtime/pty/unknown-stream-signals" #t
             (signals? (lambda () (ptn pty 'bogus))))))

(if (not have-pipe)
    (info "m40/imp3/runtime/pipe" "no pipe process (no command available)")
    (begin
      ;; A pipe process has no tty, so every stream returns nil.
      (check "m40/imp3/runtime/pipe/no-tty" #nil (ref pipe 'tty_name))
      (check "m40/imp3/runtime/pipe/nil-stream" #nil (ptn pipe))
      (check "m40/imp3/runtime/pipe/stdin" #nil (ptn pipe 'stdin))
      (check "m40/imp3/runtime/pipe/stdout" #nil (ptn pipe 'stdout))
      (check "m40/imp3/runtime/pipe/stderr" #nil (ptn pipe 'stderr))))

;;; --- 4. Runtime: process-inherit-coding-system-flag ------------------
(if (not have-pipe)
    (info "m40/imp3/runtime/inherit" "no process (no command available)")
    (begin
      ;; set-process-inherit-coding-system-flag is the M39 imp-3 writer;
      ;; the new reader must mirror the slot value it sets.
      ((symbol-function 'set-process-inherit-coding-system-flag) pipe #t)
      (check "m40/imp3/runtime/inherit/set-t" #t (icf pipe))
      (check "m40/imp3/runtime/inherit/t-matches-slot" #t
             (eq? (icf pipe) (ref pipe 'inherit_coding_system_flag)))
      ((symbol-function 'set-process-inherit-coding-system-flag) pipe #nil)
      (check "m40/imp3/runtime/inherit/set-nil" #nil (icf pipe))
      (check "m40/imp3/runtime/inherit/nil-matches-slot" #t
             (eq? (icf pipe) (ref pipe 'inherit_coding_system_flag)))))

;;; --- 5. Static: the module defines and exports the procedures -------
(define pa (slurp (repo "mod/emacs/process-accessors.scm")))
(check "m40/imp3/static/module-src-exists" #t (string? pa))
(check "m40/imp3/static/defines-tty-name" #t
       (contains? pa "(define-elisp-inline (process-tty-name process . rest)"))
(check "m40/imp3/static/defines-inherit-flag" #t
       (contains? pa "(define-elisp-inline (process-inherit-coding-system-flag process)"))
(define pa-exports (export-region pa))
(check "m40/imp3/static/exports-tty-name" #t
       (contains? pa-exports "elisp-process-tty-name"))
(check "m40/imp3/static/exports-inherit-flag" #t
       (contains? pa-exports "elisp-process-inherit-coding-system-flag"))
;; The body reaches the bridge through the imported symbol-function.
(check "m40/imp3/static/uses-symbol-function-ref" #t
       (contains? pa "(symbol-function '--process-ref)"))
;; F2: the unknown-stream error keeps the stream datum.  The C ran
;; signal_error ("Unknown stream", stream); the module must reach the
;; `signal' subr and pass the two-element list, because `error' would
;; format the message and drop STREAM.
(check "m40/imp3/static/error-uses-signal" #t
       (contains? pa "(symbol-function 'signal) 'error"))
(check "m40/imp3/static/error-keeps-stream" #t
       (contains? pa "(list \"Unknown stream\" stream)"))
;; The stdin / stdout / stderr branch order is spelled in the module.
(check "m40/imp3/static/branch-stdin" #t (contains? pa "(eq? stream 'stdin)"))
(check "m40/imp3/static/branch-stdout" #t (contains? pa "(eq? stream 'stdout)"))
(check "m40/imp3/static/branch-stderr" #t (contains? pa "(eq? stream 'stderr)"))
;; The module header records the move (M40 imp-3).
(check "m40/imp3/static/header-records-move" #t
       (contains? pa "M40 imp-3 adds two more"))
;; The module header keeps the reason for each of the 10 names that stay
;; C.  Each needle is the name as the header lists it.
(for-each
 (lambda (name)
   (check (string-append "m40/imp3/static/header-keeps/" name) #t
          (contains? pa name)))
 '("get-process" "process-status" "process-exit-status" "process-name"
   "process-type" "waiting-for-user-input-p" "set-process-buffer"
   "set-process-filter" "set-process-sentinel" "set-process-thread"))
;; Hygiene: no source comment cites the transient review file.
(define transient-review-needle (string-append "cr" ".org"))
(check "m40/imp3/static/no-transient-cr-citation" #f
       (contains? pa transient-review-needle))
(check "m40/imp3/static/cites-kb-m40" #t
       (contains? pa "docs/kb.org ** M40"))
(define imp3-corpus-src (slurp (repo "test/m40/test-m40-imp3.scm")))
(check "m40/imp3/static/corpus-no-transient-citation" #f
       (contains? imp3-corpus-src transient-review-needle))

;;; --- 6. Static: src/process.c table rows and removed DEFUNs ---------
(define proc-c (slurp (repo "src/process.c")))
(if (not proc-c)
    (report "m40/imp3/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      ;; The four new read rows exist.
      (check "m40/imp3/process.c/row-tty-name" #t
             (contains? proc-c "\"tty_name\", offsetof (struct Lisp_Process, tty_name)"))
      (check "m40/imp3/process.c/row-stderrproc" #t
             (contains? proc-c "\"stderrproc\", offsetof (struct Lisp_Process, stderrproc)"))
      (check "m40/imp3/process.c/row-pty-in" #t
             (contains? proc-c "\"pty_in\", 0, PROC_BOOL_PTY_IN"))
      (check "m40/imp3/process.c/row-pty-out" #t
             (contains? proc-c "\"pty_out\", 0, PROC_BOOL_PTY_OUT"))
      ;; The two bit-field kinds exist and the reader handles them.
      (check "m40/imp3/process.c/kind-pty-in" #t
             (contains? proc-c "PROC_BOOL_PTY_IN,"))
      (check "m40/imp3/process.c/kind-pty-out" #t
             (contains? proc-c "PROC_BOOL_PTY_OUT"))
      (check "m40/imp3/process.c/ref-reads-pty-in" #t
             (contains? proc-c "return p->pty_in ? Qt : Qnil;"))
      (check "m40/imp3/process.c/ref-reads-pty-out" #t
             (contains? proc-c "return p->pty_out ? Qt : Qnil;"))
      ;; The two C DEFUNs are gone.
      (check "m40/imp3/process.c/no-defun-tty-name" #f
             (contains? proc-c "DEFUN (\"process-tty-name\""))
      (check "m40/imp3/process.c/no-defun-inherit-flag" #f
             (contains? proc-c "DEFUN (\"process-inherit-coding-system-flag\""))
      ;; The writer pair that stays C is untouched.
      (check "m40/imp3/process.c/keeps-process-name" #t
             (contains? proc-c "DEFUN (\"process-name\""))))

;;; --- 7. Static: the harness registers the M40 group -----------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m40/imp3/run-tests/registers-el" #t
       (contains? run-tests "test/m40/test-m40-imp3.el"))

;;; --- 8. Static: imp-3 adds no C dispatcher --------------------------
;;;
;;; imp-3 adds no scm_c_public_ref site (the module reaches an existing
;;; bridge), so the tree-wide count over src/*.c and src/*.h stays 163 at
;;; imp-3 and rises to 167 at imp-4a (four new dispatchers in
;;; src/process.c) and to 172 at imp-4b (five more dispatchers).
(define (count-substr text sub)
  (if (not (string? text))
      0
      (let ((sl (string-length sub)))
        (let loop ((i 0) (n 0))
          (if (>= i (string-length text))
              n
              (let ((hit (string-contains text sub i)))
                (if hit (loop (+ hit sl) (1+ n)) n)))))))

(define (src-c-h-files)
  (let ((d (opendir (repo "src"))))
    (let loop ((names '()))
      (let ((n (readdir d)))
        (if (eof-object? n)
            (begin (closedir d) names)
            (loop (if (or (string-suffix? ".c" n) (string-suffix? ".h" n))
                      (cons n names)
                      names)))))))

(define tree-ref-sites
  (let loop ((fs (src-c-h-files)) (acc 0))
    (if (null? fs)
        acc
        (loop (cdr fs)
              (+ acc (count-substr (slurp (repo (string-append "src/" (car fs))))
                                   "scm_c_public_ref"))))))

(check "m40/imp3/static/tree-ref-sites-258" 258 tree-ref-sites)
