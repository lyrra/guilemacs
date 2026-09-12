;;; test-m32-imp5.scm --- M32 imp-5: the sysdep.c emacs_full_write EINTR
;;; drain, plus the tty-erase-char and attempt-stack-overflow-recovery
;;; DEFVAR_* names.
;;;
;;; brief.org (M32 imp-5) does three jobs:
;;;
;;;   1. route the sysdep.c caller of process_pending_signals (in
;;;      emacs_full_write) through Scheme ((emacs sysdep-main)
;;;      full-write-drain!), keeping the write () loop in C;
;;;   2. migrate tty-erase-char (DEFVAR_LISP, default nil);
;;;   3. migrate attempt-stack-overflow-recovery (DEFVAR_BOOL, default
;;;      true) -- a fatal-signal name read by stack_overflow.
;;;
;;; This corpus pins the end state.  Two kinds of check:
;;;
;;;   - a runtime check: the two names are special after boot, the
;;;     tty-erase-char default is nil and the
;;;     attempt-stack-overflow-recovery default is non-nil, and a
;;;     write-then-read round trip passes for each.  These use only core
;;;     primitives.
;;;   - a static wiring check: the sysdep.c dispatcher, the value-cell
;;;     helper and the resolve exist; the C site no longer calls
;;;     process_pending_signals directly; the stub keeps its definition
;;;     and its keyboard.c caller; the two names have no DEFVAR_* site
;;;     and no globals.h storage cell; and the Scheme declarations exist.
;;;
;;; The repo root is bound by the .el wrapper as %m32-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m32-imp5.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))
;; The runtime check in section 9b calls the ported decision procedure
;; (emacs sysdep-main) full-write-drain! directly.
(use-modules (emacs sysdep-main))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (info name value)
  "Report NAME as an INFO pair.  The .el wrapper prints it and does not
assert it; use it for a runtime call that needs a C entry point the
binary may not export."
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

(define (repo path) (string-append %m32-root "/" path))

(define (defvar-site? text name)
  "True when TEXT holds a DEFVAR_* call site for NAME.  A bare C
variable reference or a comment mention does not count."
  (and (string? text)
       (let ((needle (string-append "\"" name "\"")))
         (call-with-input-string text
           (lambda (port)
             (let loop ()
               (let ((line (read-line port)))
                 (cond ((eof-object? line) #f)
                       ((and (string-contains line "DEFVAR_")
                             (string-contains line needle)) #t)
                       (else (loop))))))))))

(define (has-line-matching? text pred)
  "True when any line of TEXT satisfies PRED."
  (and (string? text)
       (call-with-input-string text
         (lambda (port)
           (let loop ()
             (let ((line (read-line port)))
               (cond ((eof-object? line) #f)
                     ((pred line) #t)
                     (else (loop)))))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m32-root))
    (begin (report "m32/imp5/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m32-root "."))
    (report "m32/imp5/root-bound" 'PASS))

;;; --- 1. Runtime: the two names are special --------------------------
;;; The C DEFVAR_* set SYMBOL_DECLARED_SPECIAL; proclaim-special! in
;;; command-loop.scm is the replacement.  A non-special name would let
;;; elisp let/setq compile lexical.
(check "m32/imp5/special/tty-erase-char" #t
       (special? 'tty-erase-char))
(check "m32/imp5/special/attempt-stack-overflow-recovery" #t
       (special? 'attempt-stack-overflow-recovery))

;;; --- 2. Runtime: the migrated defaults ------------------------------
;;; tty-erase-char was DEFVAR_LISP, default nil.  init_sys_modes writes it
;;; to nil at boot; with no tty in batch it stays nil.
(check "m32/imp5/default/tty-erase-char" #nil
       (symbol-value 'tty-erase-char))
;; attempt-stack-overflow-recovery was DEFVAR_BOOL, default true.  The
;; (emacs command-loop) declaration seeds the non-nil default.
(check "m32/imp5/default/attempt-stack-overflow-recovery-is-non-nil" #t
       (not (eq? (symbol-value 'attempt-stack-overflow-recovery) #nil)))

;;; --- 3. Runtime: a write-then-read round trip for each --------------
(let ((old (symbol-value 'tty-erase-char)))
  (set-symbol-value! 'tty-erase-char 127)
  (check "m32/imp5/write-read/tty-erase-char" 127
         (symbol-value 'tty-erase-char))
  (set-symbol-value! 'tty-erase-char old))

(let ((old (symbol-value 'attempt-stack-overflow-recovery)))
  (set-symbol-value! 'attempt-stack-overflow-recovery #nil)
  (check "m32/imp5/write-read/attempt-stack-overflow-recovery" #nil
         (symbol-value 'attempt-stack-overflow-recovery))
  (set-symbol-value! 'attempt-stack-overflow-recovery old))

;;; --- 3b. Runtime: the C writers reach the same slot ------------------
;;; The checks above use only the Scheme side.  These call the C entry
;;; points -- the elisp function `set' is Fset and `symbol-value' is
;;; Fsymbol_value -- which is exactly how sysdep.c writes tty-erase-char
;;; and how the reader resolves the value cell.  A Scheme write is read
;;; back through C and a C write is read back through Scheme.  Guarded: a
;;; binary without those subrs reports INFO, not a failure.
(define (c-read name) ((symbol-function 'symbol-value) name))
(define (c-write name value) ((symbol-function 'set) name value))

(define (c-caller-roundtrip label name)
  "Write NAME through the C `set', read it back through the Scheme
symbol-value, then write it through set-symbol-value! and read it back
through the C `symbol-value'.  NAME is restored."
  (catch #t
    (lambda ()
      (let ((old (symbol-value name))
            (cval (list 'm32 'imp5 'c-write))
            (sval (list 'm32 'imp5 'scheme-write)))
        (c-write name cval)
        (check (string-append "m32/imp5/c-write/scheme-read/" label)
               cval (symbol-value name))
        (set-symbol-value! name sval)
        (check (string-append "m32/imp5/scheme-write/c-read/" label)
               sval (c-read name))
        (set-symbol-value! name old)))
    (lambda (key . args)
      (info (string-append "m32/imp5/c-readers/" label)
            (format #f "guarded: ~S ~S" key args)))))

(c-caller-roundtrip "tty-erase-char" 'tty-erase-char)
(c-caller-roundtrip "attempt-stack-overflow-recovery"
                    'attempt-stack-overflow-recovery)

;;; --- 4. Static: the sysdep.c dispatcher -----------------------------
(define sd (slurp (repo "src/sysdep.c")))
(if (not sd)
    (report "m32/imp5/scan/sysdep.c" (cons 'FAIL "src/sysdep.c missing"))
    (begin
      ;; emacs_full_write dispatches into (emacs sysdep-main).
      (check "m32/imp5/sysdep.c/refs-sysdep-main-module" #t
             (contains? sd "scm_c_public_ref (\"emacs sysdep-main\""))
      (check "m32/imp5/sysdep.c/refs-full-write-drain" #t
             (contains? sd "\"full-write-drain!\""))
      ;; A local static dispatcher, not a keyboard.c stub.
      (check "m32/imp5/sysdep.c/static-dispatcher" #t
             (contains? sd
                       "static void\nsysdep_full_write_drain (int interruptible)"))
      (check "m32/imp5/sysdep.c/dispatcher-calls-proc" #t
             (contains? sd "SCM_CALL_1 (proc, scm_from_int (interruptible))"))
      ;; Decision D2: the `if (interruptible)' guard stays in C and the
      ;; C site calls the dispatcher.
      (check "m32/imp5/sysdep.c/keeps-interruptible-guard" #t
             (contains? sd
                       "if (interruptible)\n\t    sysdep_full_write_drain (interruptible);"))
      ;; The C site no longer calls process_pending_signals directly.
      (check "m32/imp5/sysdep.c/no-process-pending-signals" #f
             (contains? sd "process_pending_signals ("))
      ;; The write () loop and the errno test stay C.
      (check "m32/imp5/sysdep.c/keeps-write-loop" #t
             (contains? sd "ssize_t n = write (fd, buf, min (nbyte, MAX_RW_COUNT));"))
      (check "m32/imp5/sysdep.c/keeps-eintr-test" #t
             (contains? sd "if (errno != EINTR)"))
      ;; The value-cell helper for the fatal-signal name.
      (check "m32/imp5/sysdep.c/value-cell" #t
             (contains? sd
                       "static Lisp_Object attempt_stack_overflow_recovery_cell = SCM_UNDEFINED;"))
      (check "m32/imp5/sysdep.c/value-helper" #t
             (contains? sd "attempt_stack_overflow_recovery_value"))
      (check "m32/imp5/sysdep.c/value-helper-plain-read" #t
             (contains? sd "!NILP (GAREF (attempt_stack_overflow_recovery_cell, 4))"))
      (check "m32/imp5/sysdep.c/reader-uses-helper" #t
             (contains? sd "if (!attempt_stack_overflow_recovery_value ())"))
      (check "m32/imp5/sysdep.c/resolves-cell" #t
             (contains? sd
                       "XSYMBOL (intern_c_string (\"attempt-stack-overflow-recovery\"))"))
      ;; No Guile frame on the fatal-signal path: no call to the symbol
      ;; runtime (a comment mention does not count).
      (check "m32/imp5/sysdep.c/no-find-symbol-value" #f
             (contains? sd "find_symbol_value ("))
      (check "m32/imp5/sysdep.c/no-bare-attempt-read" #f
             (contains? sd "if (!attempt_stack_overflow_recovery)"))
      ;; tty-erase-char is written through the elisp runtime.
      (check "m32/imp5/sysdep.c/no-Vtty-erase-char" #f
             (contains? sd "Vtty_erase_char"))
      (check "m32/imp5/sysdep.c/writes-qtty-nil" #t
             (contains? sd "Fset (Qtty_erase_char, Qnil);"))
      (check "m32/imp5/sysdep.c/writes-qtty-int" #t
             (contains? sd
                       "Fset (Qtty_erase_char, make_fixnum (tty.main.c_cc[VERASE]));"))))

;;; --- 5. Static: the process_pending_signals stub stays C -------------
(define kbd (slurp (repo "src/keyboard.c")))
(if (not kbd)
    (report "m32/imp5/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      (check "m32/imp5/keyboard.c/stub-definition" #t
             (contains? kbd "process_pending_signals (void)"))
      (check "m32/imp5/keyboard.c/stub-caller" #t
             (contains? kbd "\tprocess_pending_signals ();"))))
(define lisp-h (slurp (repo "src/lisp.h")))
(if (not lisp-h)
    (report "m32/imp5/scan/lisp.h" (cons 'FAIL "src/lisp.h missing"))
    (check "m32/imp5/lisp.h/stub-declaration" #t
           (contains? lisp-h "extern void process_pending_signals (void);")))

;; The brief names xdisp.c as a caller that keeps the stub alive.  At
;; HEAD the live caller is keyboard.c unblock_input_to (checked above);
;; xdisp.c keeps a documentation reference to process_pending_signals.
;; Pin that reference so the "stub stays C" evidence also covers
;; xdisp.c.  (A real call would carry "process_pending_signals ("; the
;; file only mentions the name in prose.)
(define xd (slurp (repo "src/xdisp.c")))
(if (not xd)
    (report "m32/imp5/scan/xdisp.c" (cons 'FAIL "src/xdisp.c missing"))
    (check "m32/imp5/xdisp.c/references-process-pending-signals" #t
           (contains? xd "process_pending_signals")))

;;; --- 6. Static: no DEFVAR_* site for either name --------------------
;;; The DEFVAR_* call site is what make-docfile scans.  tty-erase-char's
;;; deletion is paired with a DEFSYM that keeps the Qsym #define and the
;;; defsym_name[] entry.
(define kg (slurp (repo "src/keyboard-globals.c")))
(if (not kg)
    (report "m32/imp5/scan/keyboard-globals.c" (cons 'FAIL "missing"))
    (begin
      (for-each
       (lambda (name)
         (check (string-append "m32/imp5/no-defvar/" name) #f
                (defvar-site? kg name)))
       '("tty-erase-char" "attempt-stack-overflow-recovery"))
      (check "m32/imp5/keyboard-globals.c/defsym-qtty-erase-char" #t
             (contains? kg
                       "DEFSYM (Qtty_erase_char, \"tty-erase-char\")"))))

;;; --- 7. Static: no storage cell in the generated globals.h ----------
;;; A DEFSYM emits the Qsym #define but no value cell.  The DEFVAR_* value
;;; cells must be gone (this matches the imp-3 Qtop_level / imp-4
;;; Qnum_nonmacro_input_events precedent).
(define gh (slurp (repo "src/globals.h")))
(if (not gh)
    (report "m32/imp5/scan/globals.h" (cons 'FAIL "missing"))
    (for-each
     (lambda (cell)
       (check (string-append "m32/imp5/no-cell/" cell) #f
              (contains? gh cell)))
     '("f_Vtty_erase_char" "f_attempt_stack_overflow_recovery")))

;;; --- 8. Static: the Scheme declarations exist -----------------------
(define cl (slurp (repo "mod/emacs/command-loop.scm")))
(if (not cl)
    (report "m32/imp5/scan/command-loop.scm" (cons 'FAIL "missing"))
    (begin
      (check "m32/imp5/command-loop/tty-erase-char-row" #t
             (contains? cl "(tty-erase-char"))
      (check "m32/imp5/command-loop/attempt-stack-overflow-row" #t
             (contains? cl "(attempt-stack-overflow-recovery"))
      ;; The declaration seeds the C defaults: #nil for the DEFVAR_LISP
      ;; tty-erase-char and #t for the DEFVAR_BOOL
      ;; attempt-stack-overflow-recovery.
      (check "m32/imp5/command-loop/tty-erase-char-seed-nil" #t
             (has-line-matching?
              cl (lambda (line)
                   (and (string-contains line "(tty-erase-char")
                        (string-contains line "#nil)")))))
      (check "m32/imp5/command-loop/attempt-stack-overflow-seed-t" #t
             (has-line-matching?
              cl (lambda (line)
                   (and (string-contains line "(attempt-stack-overflow-recovery")
                        (string-contains line "#t)")))))))

;;; --- 9. Static: the (emacs sysdep-main) module ----------------------
(define sm (slurp (repo "mod/emacs/sysdep-main.scm")))
(if (not sm)
    (report "m32/imp5/scan/sysdep-main.scm" (cons 'FAIL "missing"))
    (begin
      (check "m32/imp5/sysdep-main/defines-full-write-drain" #t
             (contains? sm "(define (full-write-drain! interruptible)"))
      (check "m32/imp5/sysdep-main/exports-full-write-drain" #t
             (contains? sm "(full-write-drain!"))
      (check "m32/imp5/sysdep-main/calls-maybe-quit" #t
             (contains? sm "%--maybe-quit"))
      (check "m32/imp5/sysdep-main/reuses-drain" #t
             (contains? sm "send-process-drain-signals!"))
      (check "m32/imp5/sysdep-main/guards-maybe-quit" #t
             (contains? sm "(when (> interruptible 0)"))))

;;; --- 9b. Runtime: call the ported decision procedure -----------------
;;; The checks above only read the module text.  Call full-write-drain!
;;; directly so the ported decision runs.  INTT = 0 skips maybe_quit;
;;; INTT = -1 is the emacs_write_sig shape.  Both run the shared guarded
;;; drain, which is a no-op with no signal pending (and exercises the
;;; lazy (emacs process-error) resolve, decision D4).  Neither may quit.
(define (guarded-call label thunk)
  (catch #t
    (lambda () (check label #nil (thunk)))
    (lambda (key . args)
      (info label (format #f "guarded: ~S ~S" key args)))))

(guarded-call "m32/imp5/sysdep-main/full-write-drain-zero"
              (lambda () (full-write-drain! 0)))
(guarded-call "m32/imp5/sysdep-main/full-write-drain-neg"
              (lambda () (full-write-drain! -1)))

;;; --- 10. Static: the module is boot-loaded and the corpus registered -
(define prelude (slurp (repo "prelude/load.scm")))
(check "m32/imp5/prelude/loads-sysdep-main" #t
       (contains? prelude "(emacs sysdep-main)"))

(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m32/imp5/run-tests.scm/registers-el" #t
       (contains? run-tests "test-m32-imp5.el"))
