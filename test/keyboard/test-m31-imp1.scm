;;; test-m31-imp1.scm --- M31 imp-1: two DEFVAR_* names move to Scheme.
;;;
;;; brief.org (M31 imp-1).  Two names leave C: last-event-device
;;; (DEFVAR_LISP, default nil) and cannot-suspend (DEFVAR_BOOL, default
;;; false).  No C file reads their C variables, so their DEFVAR_* call
;;; sites are deleted from src/keyboard-globals.c.  A boot-loaded module
;;; declares them special and sets the C default (mod/emacs/command-loop.scm).
;;;
;;; This corpus checks (brief.org §6):
;;;
;;;   1. static scan: no DEFVAR_* site for either name in
;;;      src/keyboard-globals.c;
;;;   2. static scan: no f_Vlast_event_device / f_cannot_suspend storage
;;;      cell in the generated src/globals.h;
;;;   3. both names are special after boot (special? is #t);
;;;   4. both names have the C default value (#nil for both);
;;;   5. write-then-read from Scheme for last-event-device.  The elisp
;;;      side of check 5 (cannot-suspend) lives in test-m31-imp1.el.
;;;
;;; Sourced by test/keyboard/test-m31-imp1.el via eval-scheme.
;;; Accumulates (NAME STATUS) pairs into test-results for readback from
;;; elisp.  Same shape as test-m30-imp5.scm.

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

;;; The two converted names.
(define converted-names '(last-event-device cannot-suspend))

;;; --- 3. both names are special after boot ---------------------------
;;; The C DEFVAR_* set SYMBOL_DECLARED_SPECIAL; proclaim-special! in
;;; command-loop.scm is the replacement.  A non-special name would let
;;; elisp let/setq compile lexical.

(for-each
 (lambda (name)
   (check (string-append "m31/imp1/special/" (symbol->string name)) #t
          (special? name)))
 converted-names)

;;; --- 4. both names have the C default value -------------------------
;;; The C defaults were Qnil and false, i.e. #nil for both.  Read the
;;; *default* (not the current value) through the runtime.

(for-each
 (lambda (name)
   (check (string-append "m31/imp1/default/" (symbol->string name)) #nil
          ((symbol-function 'default-value) name)))
 converted-names)

;;; --- 5. write-then-read from Scheme for last-event-device -----------
;;; last-event-device is written by the lazy (emacs kbd-buffer) module
;;; with set-symbol-value!.  Write a fresh value, read it back, restore.

(let ((old (symbol-value 'last-event-device)))
  (set-symbol-value! 'last-event-device (list 'm31 'imp1 'device))
  (check "m31/imp1/write-read/last-event-device" (list 'm31 'imp1 'device)
         (symbol-value 'last-event-device))
  (set-symbol-value! 'last-event-device old))

;;; --- 1. static scan: no DEFVAR_* site in keyboard-globals.c ---------
;;; The DEFVAR_* call site is what make-docfile scans to emit the
;;; globals.h storage cell.  Delete the site and the storage goes.

(if (not (defined? '%m31-root))
    (report "m31/imp1/scan/root" (cons 'FAIL "root not bound by wrapper"))
    (let ((kg (slurp (string-append %m31-root "/src/keyboard-globals.c"))))
      (if (not kg)
          (report "m31/imp1/scan/keyboard-globals.c"
                  (cons 'FAIL "file missing"))
          (for-each
           (lambda (name)
             (if (defvar-site? kg name)
                 (report (string-append "m31/imp1/no-defvar/" (symbol->string name))
                         (cons 'FAIL (format #f "DEFVAR_* site for ~a present" name)))
                 (report (string-append "m31/imp1/no-defvar/" (symbol->string name))
                         'PASS)))
           converted-names))))

;;; --- 2. static scan: no storage cell in the generated globals.h -----

(if (not (defined? '%m31-root))
    (report "m31/imp1/scan/root" (cons 'FAIL "root not bound by wrapper"))
    (let ((gh (slurp (string-append %m31-root "/src/globals.h"))))
      (if (not gh)
          (report "m31/imp1/scan/globals.h" (cons 'FAIL "file missing"))
          (for-each
           (lambda (cell)
             (if (member-cell? gh cell)
                 (report (string-append "m31/imp1/no-cell/" cell)
                         (cons 'FAIL (format #f "globals.h member ~a present" cell)))
                 (report (string-append "m31/imp1/no-cell/" cell) 'PASS)))
           '("f_Vlast_event_device" "f_cannot_suspend")))))
