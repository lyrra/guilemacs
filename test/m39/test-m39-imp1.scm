;;; test-m39-imp1.scm --- M39 imp-1: the accept-process-output decision.
;;;
;;; brief.org (M39 imp-1) moves the decision logic of
;;; Faccept_process_output (src/process.c, pre-M39 body at :4932-4970)
;;; into the module (emacs process-wait) as the exported procedure
;;; accept-process-output-decision.  The system call
;;; (wait_reading_process_output) stays C.
;;;
;;; This corpus pins the port end state.  Two kinds of check:
;;;
;;;   - a runtime check: the module loads, exports the new procedure,
;;;     and the procedure computes the same (secs nsecs flag) decision
;;;     as the pre-port C: the millisec fix-up, the fixnum/float timeout
;;;     branch, the nsecs = 0 default for a non-nil process, and the
;;;     just-this-one {-1, 0, 1} mapping.
;;;   - a static wiring check: the old inline decision code is gone from
;;;     src/process.c, the C dispatcher is defined and called, the type
;;;     checks and the syscall stay C, and the module is registered.
;;;
;;; The repo root is bound by the .el wrapper as %m39-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test
;;; and prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/m39/test-m39-imp1.el.

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

(define (repo path) (string-append %m39-root "/" path))

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

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m39-root))
    (begin (report "m39-root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m39-root "."))
    (report "m39-root-bound" 'PASS))

;;; --- 1. The module loads and exports the new procedure ------------
(use-modules (emacs process-wait))

(define %decision
  (let ((p (module-ref (resolve-module '(emacs process-wait))
                       'accept-process-output-decision)))
    p))

(check "m39/imp1/export/accept-process-output-decision" #t
       (and (defined? '%decision) (procedure? %decision)))

;;; --- 2. Runtime: the pre-port decision, case by case --------------
;;; Each row is (seconds millisec just-this-one have-process) -> the
;;; (secs nsecs flag) list the pre-M39 C produced.  have-process is a
;;; Scheme boolean (#f false) because it is a Scheme-side flag.
(define (call d)
  ;; d = (seconds millisec just-this-one have-process)
  (apply %decision d))

;; case 1: no timeout, no process -> secs 0, nsecs -1 (default), flag 0.
(check "m39/imp1/runtime/no-timeout-no-process"
       '(0 -1 0)
       (call (list #nil #nil #nil #f)))
;; case 2: no timeout, process non-nil -> nsecs 0 default.
(check "m39/imp1/runtime/no-timeout-with-process"
       '(0 0 0)
       (call (list #nil #nil #nil #t)))
;; case 3: fixnum seconds > 0 -> whole seconds, nsecs 0.
(check "m39/imp1/runtime/fixnum-seconds"
       '(5 0 0)
       (call (list 5 #nil #nil #f)))
;; case 4: fixnum seconds 0 -> no positive timeout, nsecs stays -1.
(check "m39/imp1/runtime/fixnum-zero-seconds"
       '(0 -1 0)
       (call (list 0 #nil #nil #f)))
;; case 5: float seconds -> dtotimespec, WAIT_READING_MAX cap.
(check "m39/imp1/runtime/float-seconds"
       '(1 500000000 0)
       (call (list 1.5 #nil #nil #f)))
;; case 6: negative float -> not > 0, nsecs stays -1.
(check "m39/imp1/runtime/negative-float-seconds"
       '(0 -1 0)
       (call (list -1.5 #nil #nil #f)))
;; case 7: obsolete millisec alone -> millisec/1000.0 seconds.
(check "m39/imp1/runtime/millisec-alone"
       '(1 500000000 0)
       (call (list #nil 1500 #nil #f)))
;; case 8: millisec plus fixnum seconds -> sum (1 + 0.5).
(check "m39/imp1/runtime/millisec-plus-seconds"
       '(1 500000000 0)
       (call (list 1 500 #nil #f)))
;; case 9: just-this-one t -> flag 1.
(check "m39/imp1/runtime/just-this-one-t"
       '(5 0 1)
       (call (list 5 #nil 't #f)))
;; case 10: just-this-one fixnum -> flag -1.
(check "m39/imp1/runtime/just-this-one-fixnum"
       '(5 0 -1)
       (call (list 5 #nil 0 #f)))
;; case 11: just-this-one bignum -> not a fixnum -> flag 1 (pre-port C
;; used !FIXNUMP, so a bignum gave 1, not -1).  F3.
(check "m39/imp1/runtime/just-this-one-bignum"
       '(5 0 1)
       (call (list 5 #nil (expt 2 62) #f)))

;;; --- 3. Runtime: the WAIT_READING_MAX cap on a huge float ---------
;;; 1e19 s > WAIT_READING_MAX (2^63 - 1); the C caps t.tv_sec.  The
;;; Scheme clamps secs to the same constant.
(let ((r (call (list 1e19 #nil #nil #f))))
  (report "m39/imp1/runtime/huge-float" (list 'INFO r))
  (check "m39/imp1/runtime/huge-float-capped-secs" (- (expt 2 63) 1) (car r))
  (check "m39/imp1/runtime/huge-float-flag" 0 (caddr r)))

;;; --- 4. Static: the module source defines and exports the procedure
(define pw (slurp (repo "mod/emacs/process-wait.scm")))
(if (not pw)
    (report "m39/imp1/scan/module" (cons 'FAIL "mod/emacs/process-wait.scm missing"))
    (begin
      (check "m39/imp1/module/defines-decision" #t
             (contains? pw "(define (accept-process-output-decision"))
      (check "m39/imp1/module/exports-decision" #t
             (contains? pw "accept-process-output-decision))"))
      (check "m39/imp1/module/dtotimespec" #t (contains? pw "(define (dtotimespec"))
      (check "m39/imp1/module/timespec-hz" #t (contains? pw "TIMESPEC-HZ 1000000000"))
      (check "m39/imp1/module/wait-reading-max" #t
             (contains? pw "WAIT-READING-MAX (- (expt 2 63) 1)"))
      ;; The just-this-one mapping keeps the {-1, 0, 1} contract and
      ;; uses the fixnum range (a bignum gives 1, like the pre-port C).
      (check "m39/imp1/module/just-this-one-flag" #t
             (and (contains? pw "most-negative-fixnum just-this-one")
                  (contains? pw "(eq? just-this-one #nil) 0")))))

;;; --- 5. Static: src/process.c wires the dispatcher, old code is gone
(define proc-c (slurp (repo "src/process.c")))
(if (not proc-c)
    (report "m39/imp1/scan/process.c" (cons 'FAIL "src/process.c missing"))
    (begin
      ;; The dispatcher is defined local to process.c and called once.
      (check "m39/imp1/process.c/defines-dispatcher" #t
             (contains? proc-c "accept_process_output_decision (Lisp_Object seconds"))
      (check "m39/imp1/process.c/calls-dispatcher" #t
             (contains? proc-c "= accept_process_output_decision (seconds, millisec"))
      (check "m39/imp1/process.c/public-ref" #t
             (contains? proc-c "\"accept-process-output-decision\""))
      ;; The old inline decision code is gone from the DEFUN body.
      (check "m39/imp1/process.c/no-old-millisec-fixup" #f
             (contains? proc-c "make_float (XFIXNUM (millisec)"))
      (check "m39/imp1/process.c/no-old-dtotimespec" #f
             (contains? proc-c "dtotimespec (XFLOAT_DATA (seconds))"))
      (check "m39/imp1/process.c/no-old-just-this-one" #f
             (contains? proc-c "!FIXNUMP (just_this_one) ? 1 : -1"))
      ;; F1: the dispatcher must not read SECS with XFIXNUM (the module
      ;; can return a bignum), and must use the range-safe conversion.
      (check "m39/imp1/process.c/no-xfixnum-secs" #f
             (contains? proc-c "*secs_out = XFIXNUM"))
      (check "m39/imp1/process.c/range-safe-secs" #t
             (contains? proc-c "scm_to_intmax (XCAR (result))"))
      ;; The type checks and the syscall stay C.
      (check "m39/imp1/process.c/keeps-check-process" #t
             (contains? proc-c "CHECK_PROCESS (process)"))
      (check "m39/imp1/process.c/keeps-wait-call" #t
             (contains? proc-c "wait_reading_process_output (secs, nsecs, 0, 0"))
      (check "m39/imp1/process.c/keeps-wrong-type" #t
             (contains? proc-c "wrong_type_argument (Qnumberp, seconds)"))
      ;; The DEFUN and its globals.h EXFUN are intact.
      (check "m39/imp1/process.c/keeps-defun" #t
             (contains? proc-c "DEFUN (\"accept-process-output\""))))

;;; --- 6. Static: run-tests.scm registers the imp-1 corpus -----------
(define run-tests (slurp (repo "tool/run-tests.scm")))
(check "m39/imp1/run-tests.scm/registers-el" #t
       (contains? run-tests "test/m39/test-m39-imp1.el"))
