;;; test-m39-imp3.scm --- M39 imp-3: the process.c Group A accessors.
;;;
;;; brief.org (M39 imp-3) moves the decision of the src/process.c Group A
;;; accessors into the module (emacs process-accessors).  The slot stays
;;; C: each reader and writer reaches a struct Lisp_Process slot through
;;; the table-driven C bridge --process-ref / --process-set!.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - a runtime check: the module loads and installs every moved
;;;     accessor in the elisp function slot (define-elisp-inline);
;;;   - a static wiring check: the retired DEFUNs are gone from
;;;     src/process.c, the C bridge is defined with the slot table, the
;;;     module is loaded by the prelude, and run-tests.scm lists the
;;;     imp-3 corpus.
;;;
;;; The live slot behaviour is exercised by test/m39/test-m39-imp3.el,
;;; which calls the accessors on a real pipe process.
;;;
;;; The repo root is bound by the .el wrapper as %m39-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/m39/test-m39-imp3.el.

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
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (absent? text needle)
  (and (string? text) (not (contains? text needle))))

(define (repo path) (string-append %m39-root "/" path))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m39-root))
    (begin (report "m39-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m39-root "."))
    (report "m39-root-bound" 'PASS))

;;; --- 1. The module loads and installs every moved accessor ---------
(use-modules (emacs process-accessors))
(use-modules (emacs-elisp runtime))

;; define-elisp-inline installs the accessor in the elisp function slot.
(define (installed name)
  (let ((f (symbol-function name)))
    (and f (procedure? f))))

(for-each
 (lambda (name)
   (check (string-append "m39/imp3/installed/" (symbol->string name)) #t
          (installed name)))
 '(process-id process-command process-buffer process-mark process-filter
   process-sentinel process-thread process-plist process-coding-system
   process-query-on-exit-flag set-process-query-on-exit-flag
   set-process-inherit-coding-system-flag set-process-plist))

;;; --- 2. Static: the module source defines the accessors -------------
(define pa (slurp (repo "mod/emacs/process-accessors.scm")))
(if (not pa)
    (report "m39/imp3/scan/module"
            (cons 'FAIL "mod/emacs/process-accessors.scm missing"))
    (begin
      (check "m39/imp3/module/defines-buffer" #t
             (contains? pa "(define-elisp-inline (process-buffer process)"))
      (check "m39/imp3/module/defines-plist" #t
             (contains? pa "(define-elisp-inline (process-plist process)"))
      (check "m39/imp3/module/defines-set-plist" #t
             (contains? pa "(define-elisp-inline (set-process-plist process plist)"))
      (check "m39/imp3/module/defines-coding-system" #t
             (contains? pa "(define-elisp-inline (process-coding-system process)"))
      (check "m39/imp3/module/defines-query-flag" #t
             (contains? pa "(define-elisp-inline (process-query-on-exit-flag process)"))
      ;; The pid == 0 -> nil decision lives in the module.
      (check "m39/imp3/module/pid-zero-nil" #t
             (contains? pa "(if (= pid 0) #nil pid)"))
      ;; The query-on-exit invert lives in the module.
      (check "m39/imp3/module/query-invert" #t
             (contains? pa "(if (eq? flag #nil) #t #nil)"))
      ;; The C bridge is reached through the imported symbol-function,
      ;; so an inlined elisp body carries no module-local free variable.
      (check "m39/imp3/module/symbol-function-ref" #t
             (contains? pa "(symbol-function '--process-ref)"))
      (check "m39/imp3/module/symbol-function-set" #t
             (contains? pa "(symbol-function '--process-set!)"))))

;;; --- 3. Static: src/process.c bridge and retired DEFUNs -------------
(define proc-c (slurp (repo "src/process.c")))
(if (not proc-c)
    (report "m39/imp3/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      ;; The table-driven bridge exists.
      (check "m39/imp3/process.c/defines-ref" #t
             (contains? proc-c "DEFUN (\"--process-ref\""))
      (check "m39/imp3/process.c/defines-set" #t
             (contains? proc-c "DEFUN (\"--process-set!\""))
      (check "m39/imp3/process.c/slot-table" #t
             (contains? proc-c "static const struct proc_slot_entry proc_slot_table[] ="))
      (check "m39/imp3/process.c/table-buffer-row" #t
             (contains? proc-c "offsetof (struct Lisp_Process, buffer)"))
      (check "m39/imp3/process.c/table-plist-write-row" #t
             (contains? proc-c "\"--set-plist\", offsetof (struct Lisp_Process, plist), PROC_LISP_LIST"))
      ;; The bridge keeps the list check.
      (check "m39/imp3/process.c/check-list" #t
             (contains? proc-c "CHECK_LIST (val)"))
      ;; Every retired DEFUN is gone.
      (for-each
       (lambda (name)
         (check (string-append "m39/imp3/process.c/retired/" name) #t
                (absent? proc-c
                         (string-append "DEFUN (\"" name "\""))))
       '("process-id" "process-command" "process-buffer" "process-mark"
         "process-filter" "process-sentinel" "process-thread" "process-plist"
         "set-process-plist" "process-coding-system"
         "process-query-on-exit-flag" "set-process-query-on-exit-flag"
         "set-process-inherit-coding-system-flag" "process-connection"))
      ;; The dead #if 0 process-connection block is removed with them.
      (check "m39/imp3/process.c/no-dead-if0" #t
             (absent? proc-c "#if 0 /* Turned off because we don't currently record this info"))
      ;; The kept DEFUNs that still have live C callers stay.
      (check "m39/imp3/process.c/keeps-process-name" #t
             (contains? proc-c "DEFUN (\"process-name\""))
      (check "m39/imp3/process.c/keeps-process-status" #t
             (contains? proc-c "DEFUN (\"process-status\""))))

;;; --- 4. Static: the module is loaded by the prelude -----------------
(define prelude (slurp (repo "prelude/load.scm")))
(check "m39/imp3/prelude/loads-process-accessors" #t
       (contains? prelude "(use-modules (emacs process-accessors))"))

;;; --- 5. Static: run-tests.scm registers the imp-3 corpus ------------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m39/imp3/run-tests.scm/registers-el" #t
       (contains? run-tests "test/m39/test-m39-imp3.el"))
