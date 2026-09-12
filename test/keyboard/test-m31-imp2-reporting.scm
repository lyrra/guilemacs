;;; test-m31-imp2-reporting.scm --- M31 imp-2: reporting guards.
;;;
;;; cr.org (M31 imp-2 review) found no code defect.  Its remaining
;;; findings were in reporting.  This small corpus pins the two
;;; tracked-file invariants that the review relied on, so a later edit
;;; cannot silently break them:
;;;
;;;   1. test/keyboard/test-m31-imp2.el is registered in
;;;      tool/run-tests.scm, after the M31 imp-1 row (brief.org §6);
;;;   2. test/keyboard/test-m23-imp5.el no longer lists
;;;      "auto-save-interval" in its source-scan name list, because the
;;;      DEFVAR_* site left keyboard-globals.c (brief.org §7);
;;;   3. test/keyboard/test-m23-imp5.el still holds
;;;      (auto-save-interval 300) in gm5-cases: the name must stay bound
;;;      with default 300 (brief.org §7).
;;;
;;; Sourced by test/keyboard/test-m31-imp2-reporting.el via eval-scheme.
;;; Accumulates (NAME STATUS) pairs into test-results for readback from
;;; elisp.  Same shape as test-m31-imp2.scm.

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
  (and (string? text) (if (string-contains text needle) #t #f)))

(define (line-index text needle)
  "Return the 1-based line number of the first NEEDLE in TEXT, or #f."
  (and (string? text)
       (call-with-input-string text
         (lambda (port)
           (let loop ((n 1))
             (let ((line (read-line port)))
               (cond ((eof-object? line) #f)
                     ((string-contains line needle) n)
                     (else (loop (1+ n))))))))))

(define (guard name thunk)
  "Report a FAIL when THUNK raises, else THUNK's result."
  (catch #t
    (lambda () (thunk))
    (lambda (key . args)
      (report name (list 'FAIL 'exception (cons key args)))
      #f)))

;;; --- 1. the imp-2 .el file is registered after the imp-1 row --------
;;; brief.org §6: register the .el file in tool/run-tests.scm after the
;;; test/keyboard/test-m31-imp1.el row.

(if (not (defined? '%m31-root))
    (report "m31/imp2r/scan/root" (cons 'FAIL "root not bound by wrapper"))
    (let ((rt (guard "m31/imp2r/scan/run-tests"
                     (lambda () (slurp (string-append %m31-root "/tool/run-tests.scm"))))))
      (if (not rt)
          (report "m31/imp2r/scan/run-tests.scm" (cons 'FAIL "file missing"))
          (let ((i1 (guard "m31/imp2r/index/imp1"
                           (lambda () (line-index rt "test/keyboard/test-m31-imp1.el"))))
                (i2 (guard "m31/imp2r/index/imp2"
                           (lambda () (line-index rt "test/keyboard/test-m31-imp2.el")))))
            (check "m31/imp2r/registered/imp2" #t (and i1 i2 (integer? i1) (integer? i2)))
            (check "m31/imp2r/registered/imp2-after-imp1" #t
                   (and i1 i2 (> i2 i1)))))))

;;; --- 2. the m23-imp5 scan list drops auto-save-interval ------------
;;; brief.org §7.1: remove "auto-save-interval" from the source-scan
;;; name list.  The scan entries are quoted: "auto-save-interval".  A
;;; hit would fail at HEAD, because the DEFVAR_* site is gone.

(if (not (defined? '%m31-root))
    (report "m31/imp2r/scan/root" (cons 'FAIL "root not bound by wrapper"))
    (let ((m5 (guard "m31/imp2r/scan/m23-imp5"
                     (lambda () (slurp (string-append %m31-root "/test/keyboard/test-m23-imp5.el"))))))
      (if (not m5)
          (report "m31/imp2r/scan/m23-imp5.el" (cons 'FAIL "file missing"))
          (begin
            (check "m31/imp2r/m23-imp5/scan-drops/quoted-auto-save-interval" #f
                   (contains? m5 "\"auto-save-interval\""))
            ;; --- 3. gm5-cases still holds (auto-save-interval 300) -----
            (check "m31/imp2r/m23-imp5/keeps/gm5-case" #t
                   (contains? m5 "(auto-save-interval 300)"))))))
