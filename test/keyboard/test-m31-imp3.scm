;;; test-m31-imp3.scm --- M31 imp-3: close-out audit.
;;;
;;; brief.org (M31 imp-3) is the close-out step of M31.  It ports no
;;; code and changes no C file.  It pins the M31 end state so a later
;;; commit that reintroduces a C DEFVAR_* site or a globals.h storage
;;; cell for a converted name is caught here.
;;;
;;; M31 moved three declarations out of C.  Their C variables have no
;;; reader left:
;;;
;;;   - last-event-device (DEFVAR_LISP, default nil)  -- imp-1, 9b6811b
;;;   - cannot-suspend     (DEFVAR_BOOL, default false) -- imp-1, 9b6811b
;;;   - auto-save-interval (DEFVAR_INT, default 300)   -- imp-2, 841cee3
;;;
;;; mod/emacs/command-loop.scm now declares each name special and sets
;;; the C default.
;;;
;;; This corpus is a static audit.  It reads the tree and the runtime.
;;; It checks (brief.org §4):
;;;
;;;   1. the repo root is bound (%m31-root);
;;;   2. exit criterion 1 -- no DEFVAR_* site for a converted name
;;;      stays in src/keyboard-globals.c (all three names);
;;;   3. exit criterion 3 -- no globals.h storage cell for a converted
;;;      name (f_Vlast_event_device, f_cannot_suspend,
;;;      f_auto_save_interval);
;;;   4. exit criterion 2 -- each converted name is special after boot
;;;      (special? is #t) and holds the C default (default-value):
;;;      #nil, #nil, 300;
;;;   5. a write-then-read round trip for one converted name;
;;;   6. over-deletion guard -- the 8 DEFVAR_KBOARD sites stay;
;;;   7. over-deletion guard -- the 31 DEFSYM sites stay;
;;;   8. the line counts, the site counts, and the DEFUN count are
;;;      printed as INFO (a line count moves; do not assert it).
;;;
;;; The repo root is bound by the .el wrapper as %m31-root (the
;;; harness loads the corpus with CWD=test/).
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m31-imp3.el.

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
  "True when TEXT holds NEEDLE as a substring."
  (and (string? text) (string-contains text needle)))

(define (count-occurrences text needle)
  "Count the non-overlapping occurrences of NEEDLE in TEXT."
  (let ((nlen (string-length needle)))
    (if (or (not (string? text)) (= nlen 0))
        0
        (let loop ((start 0) (n 0))
          (let ((idx (string-contains text needle start)))
            (if (not idx)
                n
                (loop (+ idx nlen) (+ n 1))))))))

;; count-calls: the number of MACRO call sites ("MACRO (") in TEXT.
;; A comment mention of the macro name (no open paren) does not count.
(define (count-calls text macro)
  (count-occurrences text (string-append macro " (")))

;; count-lines: the number of newline characters in the file at PATH
;; (wc -l), or #f when the file is absent.
(define (count-lines path)
  (let ((body (slurp path)))
    (if (not body)
        #f
        (let loop ((i 0) (n 0))
          (if (>= i (string-length body))
              n
              (loop (+ i 1)
                    (if (char=? (string-ref body i) #\newline)
                        (+ n 1) n)))))))

;; defun-count: the number of lines that begin with "DEFUN " (column 0).
(define (defun-count text)
  (if (not (string? text))
      #f
      (+ (count-occurrences text "\nDEFUN ")
         (if (string-prefix? "DEFUN " text) 1 0))))

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

;;; --- 1. The repo root must be known --------------------------------
(if (not (defined? '%m31-root))
    (begin (report "m31-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m31-root "."))
    (report "m31-root-bound" 'PASS))

(define (repo path) (string-append %m31-root "/" path))

;;; --- 4. Each converted name is special, with the C default ---------
;;; The C DEFVAR_* set SYMBOL_DECLARED_SPECIAL; proclaim-special! in
;;; command-loop.scm is the replacement.  A non-special name would let
;;; elisp let/setq compile lexical.  Read the *default* (not the
;;; current value) through the runtime.
(define converted
  ;; (name . C-default)
  '((last-event-device . #nil)
    (cannot-suspend . #nil)
    (auto-save-interval . 300)))

(for-each
 (lambda (pair)
   (let ((name (car pair))
         (default (cdr pair)))
     (check (string-append "m31/imp3/special/" (symbol->string name)) #t
            (special? name))
     (check (string-append "m31/imp3/default/" (symbol->string name)) default
            ((symbol-function 'default-value) name))))
 converted)

;;; --- 5. Write-then-read round trip (one converted name) ------------
;;; (emacs kbd-buffer) writes last-event-device with set-symbol-value!.
;;; Write a fresh value, read it back, then restore the boot value.
(let ((old (symbol-value 'last-event-device)))
  (set-symbol-value! 'last-event-device 'm31-imp3-probe)
  (check "m31/imp3/write-read/last-event-device" 'm31-imp3-probe
         (symbol-value 'last-event-device))
  (set-symbol-value! 'last-event-device old)
  (check "m31/imp3/write-read-restored/last-event-device" #t
         (equal? old (symbol-value 'last-event-device))))

;;; --- 2. Static scan: no DEFVAR_* site in keyboard-globals.c ---------
;;; The DEFVAR_* call site is what make-docfile scans to emit the
;;; globals.h storage cell.  Delete the site and the storage goes.
(let ((kg (slurp (repo "src/keyboard-globals.c"))))
  (if (not kg)
      (report "m31/imp3/scan/keyboard-globals.c" (cons 'FAIL "file missing"))
      (for-each
       (lambda (pair)
         (let* ((name (car pair))
                (label (string-append "m31/imp3/no-defvar/"
                                      (symbol->string name))))
           (if (defvar-site? kg name)
               (report label
                       (cons 'FAIL (format #f "DEFVAR_* site for ~a present"
                                           name)))
               (report label 'PASS))))
       converted)))

;;; --- 3. Static scan: no storage cell in the generated globals.h -----
(let ((gh (slurp (repo "src/globals.h"))))
  (if (not gh)
      (report "m31/imp3/scan/globals.h" (cons 'FAIL "file missing"))
      (for-each
       (lambda (cell)
         (let ((label (string-append "m31/imp3/no-cell/" cell)))
           (if (member-cell? gh cell)
               (report label
                       (cons 'FAIL (format #f "globals.h member ~a present"
                                           cell)))
               (report label 'PASS))))
       '("f_Vlast_event_device" "f_cannot_suspend"
         "f_auto_save_interval"))))

;;; --- 6. Over-deletion guard: the 8 DEFVAR_KBOARD sites stay ---------
;;; M31 removes only the three converted names.  The relocated
;;; DEFVAR_KBOARD cross-file sites must stay in keyboard-globals.c.
(let ((kg (slurp (repo "src/keyboard-globals.c"))))
  (if (not kg)
      (report "m31/imp3/scan/keyboard-globals.c" (cons 'FAIL "file missing"))
      (check "m31/imp3/keep/kboard-sites" 8
             (count-calls kg "DEFVAR_KBOARD"))))

;;; --- 7. Over-deletion guard: the 31 DEFSYM sites stay ---------------
(let ((kg (slurp (repo "src/keyboard-globals.c"))))
  (if (not kg)
      (report "m31/imp3/scan/keyboard-globals.c" (cons 'FAIL "file missing"))
      (check "m31/imp3/keep/defsym-sites" 31
             (count-calls kg "DEFSYM"))))

;;; --- 8. Counts (INFO; printed, not asserted) ------------------------
;;; A line count moves with a comment or a rebuild.  Do not assert it.
(define kbd-path (repo "src/keyboard.c"))
(define kg-path (repo "src/keyboard-globals.c"))

;; src/keyboard.c is read only for the INFO counts (brief.org §4.8).  If
;; it is absent the counts print as #f (INFO) and do not FAIL.  The
;; static scans above still FAIL when keyboard-globals.c or globals.h is
;; absent, so a missing tree is caught there, not here.

(define kbd-lines (count-lines kbd-path))
(define kg-lines (count-lines kg-path))
(define combined (if (and kbd-lines kg-lines) (+ kbd-lines kg-lines) #f))

(define kg-body (slurp kg-path))
(define defvar-sites
  (if kg-body
      (+ (count-calls kg-body "DEFVAR_LISP")
         (count-calls kg-body "DEFVAR_INT")
         (count-calls kg-body "DEFVAR_BOOL")
         (count-calls kg-body "DEFVAR_KBOARD"))
      #f))
(define defsym-sites (if kg-body (count-calls kg-body "DEFSYM") #f))
(define defuns (defun-count (slurp kbd-path)))

(report "remnant:src/keyboard.c-lines" (list 'INFO kbd-lines))
(report "remnant:src/keyboard-globals.c-lines" (list 'INFO kg-lines))
(report "remnant:combined-lines" (list 'INFO combined))
(report "remnant:src/keyboard.c-DEFUN" (list 'INFO defuns))
(report "remnant:keyboard-globals.c-DEFVAR_-sites" (list 'INFO defvar-sites))
(report "remnant:keyboard-globals.c-DEFSYM-sites" (list 'INFO defsym-sites))
