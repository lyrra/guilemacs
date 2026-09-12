;;; test-m31-imp2.scm --- M31 imp-2: dead SIGDANGER arm + auto-save-interval.
;;;
;;; brief.org (M31 imp-2).  Two jobs:
;;;
;;;   A. Delete the dead #ifdef SIGDANGER arm.  SIGDANGER is defined
;;;      nowhere in this build, so the compiler never saw the guarded
;;;      code.  Its last C reader, force_auto_save_soon, goes with it.
;;;   B. Move auto-save-interval (DEFVAR_INT, default 300) out of C.
;;;      No C file reads its C variable after the arm goes.  A
;;;      boot-loaded module (mod/emacs/command-loop.scm) declares it
;;;      special and sets the C default.
;;;
;;; This corpus checks (brief.org §6):
;;;
;;;   1. static scan: no DEFVAR_* site for auto-save-interval in
;;;      src/keyboard-globals.c;
;;;   2. static scan: no f_auto_save_interval storage cell in the
;;;      generated src/globals.h;
;;;   3. the name is special after boot (special? is #t);
;;;   4. the name has the C default value (300);
;;;   5. write-then-read from Scheme: set 77, read back, restore;
;;;   6. static scan of the arm deletion: src/keyboard.c, src/lisp.h and
;;;      src/sysdep.c hold no SIGDANGER and no force_auto_save_soon;
;;;   7. static scan: the src/alloc.c guard no longer holds
;;;      "defined SIGDANGER".
;;;
;;; Sourced by test/keyboard/test-m31-imp2.el via eval-scheme.
;;; Accumulates (NAME STATUS) pairs into test-results for readback from
;;; elisp.  Same shape as test-m31-imp1.scm.

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

(define (defvar-site? text name)
  "True when TEXT holds a DEFVAR_* call site for NAME.  A bare C
variable reference or a comment mention does not count."
  (let ((needle (string-append "\"" (symbol->string name) "\"")))
    (call-with-input-string text
      (lambda (port)
        (let loop ()
          (let ((line (read-line port)))
            (cond ((eof-object? line) #f)
                  ((and (string-contains line "DEFVAR_")
                        (string-contains line needle)) #t)
                  (else (loop)))))))))

(define (member-cell? text cell)
  "True when TEXT holds the generated globals.h member CELL."
  (and (string? text) (string-contains text cell)))

(define (contains? text needle)
  "True when TEXT holds NEEDLE as a substring."
  (and (string? text) (string-contains text needle)))

;;; The converted name.
(define converted-name 'auto-save-interval)

;;; The arm-deletion scan files, and the tokens that must be gone.
(define arm-scan-files '("src/keyboard.c" "src/lisp.h" "src/sysdep.c"))
(define arm-scan-tokens '("SIGDANGER" "force_auto_save_soon"))

;;; --- 3. the name is special after boot ------------------------------
;;; The C DEFVAR_* set SYMBOL_DECLARED_SPECIAL; proclaim-special! in
;;; command-loop.scm is the replacement.  A non-special name would let
;;; elisp let/setq compile lexical.

(check (string-append "m31/imp2/special/" (symbol->string converted-name)) #t
       (special? converted-name))

;;; --- 4. the name has the C default value ----------------------------
;;; The C default was 300.  Read the *default* (not the current value)
;;; through the runtime.

(check (string-append "m31/imp2/default/" (symbol->string converted-name)) 300
       ((symbol-function 'default-value) converted-name))

;;; --- 5. write-then-read from Scheme ---------------------------------
;;; (emacs read-char) reads the name with symbol-value.  Write a fresh
;;; value, read it back, restore the boot value.

(let ((old (symbol-value 'auto-save-interval)))
  (set-symbol-value! 'auto-save-interval 77)
  (check "m31/imp2/write-read/auto-save-interval" 77
         (symbol-value 'auto-save-interval))
  (set-symbol-value! 'auto-save-interval old))

;;; --- 1. static scan: no DEFVAR_* site in keyboard-globals.c ---------
;;; The DEFVAR_* call site is what make-docfile scans to emit the
;;; globals.h storage cell.  Delete the site and the storage goes.

(if (not (defined? '%m31-root))
    (report "m31/imp2/scan/root" (cons 'FAIL "root not bound by wrapper"))
    (let ((kg (slurp (string-append %m31-root "/src/keyboard-globals.c"))))
      (if (not kg)
          (report "m31/imp2/scan/keyboard-globals.c"
                  (cons 'FAIL "file missing"))
          (if (defvar-site? kg converted-name)
              (report "m31/imp2/no-defvar/auto-save-interval"
                      (cons 'FAIL "DEFVAR_* site for auto-save-interval present"))
              (report "m31/imp2/no-defvar/auto-save-interval" 'PASS)))))

;;; --- 2. static scan: no storage cell in the generated globals.h -----

(if (not (defined? '%m31-root))
    (report "m31/imp2/scan/root" (cons 'FAIL "root not bound by wrapper"))
    (let ((gh (slurp (string-append %m31-root "/src/globals.h"))))
      (if (not gh)
          (report "m31/imp2/scan/globals.h" (cons 'FAIL "file missing"))
          (if (member-cell? gh "f_auto_save_interval")
              (report "m31/imp2/no-cell/f_auto_save_interval"
                      (cons 'FAIL "globals.h member f_auto_save_interval present"))
              (report "m31/imp2/no-cell/f_auto_save_interval" 'PASS)))))

;;; --- 6. static scan: no SIGDANGER / force_auto_save_soon in the arm -
;;; The dead arm lived in keyboard.c, lisp.h and sysdep.c.  After the
;;; deletion no token remains in any of them.

(if (not (defined? '%m31-root))
    (report "m31/imp2/scan/root" (cons 'FAIL "root not bound by wrapper"))
    (for-each
     (lambda (file)
       (let ((text (slurp (string-append %m31-root "/" file))))
         (if (not text)
             (report (string-append "m31/imp2/scan/" file)
                     (cons 'FAIL "file missing"))
             (for-each
              (lambda (token)
                (let ((name (string-append "m31/imp2/no-token/" file "/" token)))
                  (if (contains? text token)
                      (report name (cons 'FAIL (format #f "~a present" token)))
                      (report name 'PASS))))
              arm-scan-tokens))))
     arm-scan-files))

;;; --- 7. static scan: alloc.c guard no longer holds defined SIGDANGER -

(if (not (defined? '%m31-root))
    (report "m31/imp2/scan/root" (cons 'FAIL "root not bound by wrapper"))
    (let ((ac (slurp (string-append %m31-root "/src/alloc.c"))))
      (if (not ac)
          (report "m31/imp2/scan/alloc.c" (cons 'FAIL "file missing"))
          (if (contains? ac "defined SIGDANGER")
              (report "m31/imp2/no-guard/alloc.c"
                      (cons 'FAIL "alloc.c guard still holds defined SIGDANGER"))
              (report "m31/imp2/no-guard/alloc.c" 'PASS)))))
