;;; test-m41-imp2.scm --- M41 imp-2: the src/xdisp.c decision predicates.
;;;
;;; brief.org (M41 imp-2) moves the *decision* of two src/xdisp.c DEFUNs
;;; into the module (emacs xdisp):
;;;
;;;   long-line-optimizations-p -- the Flong_line_optimizations_p
;;;                                decision: one buffer bool -> elisp
;;;                                t / nil.
;;;   invisible-p               -- the Finvisible_p decision: the
;;;                                TEXT_PROP_MEANS_INVISIBLE code ->
;;;                                elisp nil / t / fixnum.
;;;
;;; The mechanism stays C: the current_buffer->long_line_optimizations_p
;;; read, FIXNATP / MARKERP, Fget_char_property, Qinvisible, and
;;; TEXT_PROP_MEANS_INVISIBLE.  Each DEFUN stays C, keeps its elisp
;;; name, and calls the module through a static dispatcher
;;; (scm_c_public_ref + SCM_CALL_1).  No C fallback.
;;;
;;; Two kinds of check: the decision value on synthetic inputs (the C
;;; rule, computed here independently of the module body spelling), and a
;;; static scan of the module, src/xdisp.c, and the harness registration.
;;;
;;; The repo root is bound by the .el wrapper as %m41-root.  The .el
;;; wrapper turns each (NAME PASS|FAIL) pair into an ERT test; see
;;; test/m41/test-m41-imp2.el.

(use-modules (srfi srfi-13))

(use-modules (emacs xdisp))

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

(define (repo path) (string-append %m41-root "/" path))

(define (contains? text needle)
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (count-occurrences text needle)
  "Count the non-overlapping occurrences of NEEDLE in TEXT."
  (if (not (string? text))
      0
      (let ((nlen (string-length needle)))
        (let loop ((start 0) (n 0))
          (let ((idx (string-contains text needle start)))
            (if (not idx)
                n
                (loop (+ idx nlen) (+ n 1))))))))

(define (count-lines-starting text prefix)
  "Count the lines of TEXT that start with PREFIX."
  (if (not (string? text))
      0
      (let loop ((lines (string-split text #\newline)) (n 0))
        (if (null? lines)
            n
            (loop (cdr lines)
                  (if (string-prefix? prefix (car lines)) (+ n 1) n))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m41-root))
    (begin (report "m41-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m41-root "."))
    (report "m41-root-bound" 'PASS))

;;; --- 1. The module exports the two procedures ----------------------
(define xdisp (resolve-module '(emacs xdisp)))
(define llp (module-ref xdisp 'xdisp-long-line-optimizations-p))
(define inv (module-ref xdisp 'xdisp-invisible-p))

(check "m41/imp2/export/xdisp-long-line-optimizations-p" #t
       (procedure? llp))
(check "m41/imp2/export/xdisp-invisible-p" #t (procedure? inv))

;;; --- 2. Unit: the decision value on synthetic inputs ---------------
;;; The C rule of long-line-optimizations-p (src/xdisp.c:20157):
;;;   return current_buffer->long_line_optimizations_p ? Qt : Qnil;
;;; The C passes the bool as elisp t / nil (Qt is SCM_BOOL_T, i.e. the
;;; Scheme #t).  The module owns the bool -> elisp-value map.
(check "m41/imp2/unit/llp/true" #t (llp #t))
(check "m41/imp2/unit/llp/false" #nil (llp #nil))

;;; The C rule of invisible-p (src/xdisp.c:29746):
;;;   invis == 0 -> nil, invis == 1 -> t, else the fixnum.
;;; The C computes INVIS and passes it as a fixnum; the module owns the
;;; code -> elisp-value map.  A Scheme exact integer reads back as the
;;; elisp fixnum (Lisp_Object is SCM; FIXNUMP is SCM_I_INUMP), so the
;;; module returns the integer directly.
(check "m41/imp2/unit/inv/zero" #nil (inv 0))
(check "m41/imp2/unit/inv/one" #t (inv 1))
(check "m41/imp2/unit/inv/two" 2 (inv 2))
(check "m41/imp2/unit/inv/three" 3 (inv 3))

;;; --- 3. Static: the module source and the export list -------------
(define xdisp-mod (slurp (repo "mod/emacs/xdisp.scm")))
(check "m41/imp2/module/exists" #t (and (string? xdisp-mod) #t))
(check "m41/imp2/module/export-long-line" #t
       (contains? xdisp-mod "xdisp-long-line-optimizations-p"))
(check "m41/imp2/module/export-invisible" #t
       (contains? xdisp-mod "xdisp-invisible-p"))
(check "m41/imp2/module/defines-long-line" #t
       (contains? xdisp-mod "(define (xdisp-long-line-optimizations-p"))
(check "m41/imp2/module/defines-invisible" #t
       (contains? xdisp-mod "(define (xdisp-invisible-p"))

;;; --- 4. Static: the C dispatchers and the two DEFUN bodies --------
(define xdisp-c (slurp (repo "src/xdisp.c")))
(check "m41/imp2/c/xdisp-exists" #t (and (string? xdisp-c) #t))

;; The two new static dispatchers.
(check "m41/imp2/c/dispatcher-long-line" #t
       (contains? xdisp-c "long_line_optimizations_decision"))
(check "m41/imp2/c/dispatcher-invisible" #t
       (contains? xdisp-c "invisible_p_decision"))

;; Each dispatcher resolves its module procedure once.
(check "m41/imp2/c/public-ref-long-line" #t
       (contains? xdisp-c "\"xdisp-long-line-optimizations-p\""))
(check "m41/imp2/c/public-ref-invisible" #t
       (contains? xdisp-c "\"xdisp-invisible-p\""))

;; Each DEFUN body is one call to its dispatcher: the decision moved, no
;; C fallback (the old inline ternary is gone).
(check "m41/imp2/c/defun-long-line-calls" #t
       (contains? xdisp-c
                  "return long_line_optimizations_decision (current_buffer->long_line_optimizations_p);"))
(check "m41/imp2/c/defun-invisible-calls" #t
       (contains? xdisp-c "return invisible_p_decision (invis);"))
(check "m41/imp2/c/no-inline-invisible-ternary" #t
       (if (contains? xdisp-c "invis == 1 ? Qt") #f #t))

;; The two DEFUNs stay, with their elisp names (the names still resolve).
(check "m41/imp2/c/defun-long-line-stays" 1
       (count-lines-starting xdisp-c "DEFUN (\"long-line-optimizations-p\""))
(check "m41/imp2/c/defun-invisible-stays" 1
       (count-lines-starting xdisp-c "DEFUN (\"invisible-p\""))

;; The C keeps the mechanism: the buffer field, the property lookup, and
;; the invisibility macro.
(check "m41/imp2/c/keeps-buffer-field" #t
       (contains? xdisp-c "current_buffer->long_line_optimizations_p"))
(check "m41/imp2/c/keeps-char-property" #t
       (contains? xdisp-c "Fget_char_property (pos, Qinvisible, Qnil)"))
(check "m41/imp2/c/keeps-invisibility-macro" #t
       (contains? xdisp-c "TEXT_PROP_MEANS_INVISIBLE (prop)"))

;; The imp-2 scm_c_public_ref sites land, plus the three imp-3 sites:
;; xdisp.c count 7 -> 12.
(check "m41/imp2/c/xdisp-scm-public-ref-12" 12
       (count-occurrences xdisp-c "scm_c_public_ref"))

;;; --- 5. Static: the harness registers the new corpus --------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m41/imp2/run-tests.scm/group-m41" #t
       (contains? run-tests "(group (m41)"))
(check "m41/imp2/run-tests.scm/registers-el" #t
       (contains? run-tests "test/m41/test-m41-imp2.el"))
