;;; test-m38-imp1.scm --- M38 imp-1: the ERT count mismatch must fail the run.
;;;
;;; brief.org (M38 imp-1, D1): tool/run-tests.scm prints
;;; "ERROR: N passed, but M counted pass." and still exits 0.  A failing
;;; ERT test emits no "passed" line, so it leaves the pass count and
;;; leaves no fail record -- a silent false green.  imp-1 records the
;;; mismatch in the failure accumulator, so the exit status at the report
;;; is non-zero.  The ERROR text stays.
;;;
;;; Checks:
;;;    1. The repo root is bound by the wrapper (%m38-root).
;;;    2. The ERROR text is kept, exactly (no weakening).
;;;    3. run-tests-loadup-emacs records the mismatch as a real failure:
;;;       a non-empty fail list is returned when the observed pass names
;;;       (plus controlled skips) do not match the ERT total M.  The
;;;       guard uses the TOTAL M, not the index of the last pass, so a
;;;       failing LAST test is seen (review F1).
;;;    3c. A batch whose subprocess crashes before ert-run-tests-batch-
;;;        and-exit ever runs is its own failure, not a silent pass-
;;;        through: TOT stays 0 (the M38 imp-1 guard is satisfied
;;;        vacuously, 0 = 0 + 0) exactly like a group that legitimately
;;;        selects zero tests (every test tag-excluded).  The two are
;;;        told apart by ERT's own completion banner ("Ran N tests, M
;;;        results as expected, K unexpected"): its *absence* -- not
;;;        TOT == 0 -- is the real signal something crashed.  Found
;;;        running a real full suite: test-m39-imp5.el and
;;;        test-m40-imp0-audit.el each read a docs/ file without
;;;        guarding its absence, silently passing under the old guard.
;;;    4. run-tests pushes that fail list into %total-failed-ert-tests.
;;;    5. The report computes num-total-failed-ert-tests from both the
;;;       scanned-missing set and the %total-failed-ert-tests accumulator.
;;;    5b. The report prints one number (review F3), and the dead
;;;       num-total-missing-ert-tests binding is gone.
;;;    6. The exit status reads num-total-failed-ert-tests.  There is one
;;;       exit path only (no second exit path).
;;;    7. run-tests-bare-emacs has no numeric count line to compare, so no
;;;       count check is added there (INFO).  Its begin/end protocol
;;;       already records an unmatched test as a failure.
;;;    8. Registered: the m38-imp1 corpus and the count-mismatch fixture
;;;       are both in the group list.
;;;
;;; There is no automated behavior check: it used to shell out to
;;; tool/run-tests.sh via call-process from the .el wrapper, which is the
;;; same run-tests.sh-inside-run-tests.sh recursion removed from
;;; test-m38-imp2/3/4.el (see test-m38-imp1.el's header).  Exercise the
;;; registered fixture by hand instead:
;;;   ./tool/run-tests.sh --filter=m38-imp1-fixture                (green)
;;;   GUILEMACS_M38_FIXTURE=middle ./tool/run-tests.sh --filter=m38-imp1-fixture  (exit 1)
;;;   GUILEMACS_M38_FIXTURE=last   ./tool/run-tests.sh --filter=m38-imp1-fixture  (exit 1)
;;;   GUILEMACS_M38_FIXTURE=empty  ./tool/run-tests.sh --filter=m38-imp1-fixture  (green -- legitimate zero tests)
;;;   GUILEMACS_M38_FIXTURE=crash  ./tool/run-tests.sh --filter=m38-imp1-fixture  (exit 1 -- the real bug)
;;;
;;; All checks read files, so the corpus needs no C entry point and is
;;; batch-safe.  The repo root is bound by the .el wrapper as %m38-root.

(use-modules (ice-9 rdelim))
(use-modules (ice-9 ftw))
(use-modules (srfi srfi-13))
(use-modules (srfi srfi-1))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (info name value)
  (report name (list 'INFO value)))

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

(define (count-substr text sub)
  (if (not (string? text)) 0
      (let ((n (string-length sub)))
        (let loop ((i 0) (acc 0))
          (if (> (+ i n) (string-length text))
              acc
              (if (string=? sub (substring text i (+ i n)))
                  (loop (+ i n) (1+ acc))
                  (loop (1+ i) acc)))))))

(define (repo path) (string-append %m38-root "/" path))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m38-root))
    (begin (report "m38/imp1/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m38-root "."))
    (report "m38/imp1/root-bound" 'PASS))

;;; --- The live harness source ---------------------------------------
(define rt (slurp (repo "tool/run-tests.scm")))
(if (not rt)
    (report "m38/imp1/scan/run-tests.scm" (cons 'FAIL "tool/run-tests.scm missing"))
    (begin
      ;; --- 2. The ERROR text is kept, exactly. -----------------------
      (check "m38/imp1/fix/error-text-kept" #t
             (contains? rt "ERROR: ~a passed, but ~a counted pass~a."))

      ;; --- 3. run-tests-loadup-emacs records the mismatch. -----------
      ;; The mismatch value is named and turned into a one-element fail
      ;; list; an empty list is returned when the counts agree.
      (check "m38/imp1/fix/mismatch-named" #t
             (contains? rt "ERT count mismatch"))
      ;; Review F1: the guard must compare the observed pass count (plus
      ;; controlled skips) with the ERT TOTAL, not with the index of the
      ;; last "passed" line -- else a failing LAST test is hidden.
      (check "m38/imp1/fix/guard-compares-observed-to-total" #t
             (contains? rt "(mismatch? (not (= (+ (length pass) skipped) tot)))"))
      (check "m38/imp1/fix/tot-is-ert-total" #t
             (contains? rt "(set! tot (string->number total))"))
      (check "m38/imp1/fix/regex-captures-total" #t
             (contains? rt "/([0-9]+)"))
      (check "m38/imp1/fix/returns-pass-pass-faillist" #t
             (contains? rt "(list pass pass"))

      ;; --- 3c. The crashed-batch blind spot is closed, without a false
      ;; positive on a group that legitimately selects zero tests. -------
      (check "m38/imp1/fix/completion-banner-tracked" #t
             (contains? rt "(set! ran-summary? #t)"))
      (check "m38/imp1/fix/completion-banner-detects-string" #t
             (contains? rt "\"results as expected,\""))
      (check "m38/imp1/fix/crashed-is-banner-absence-not-tot" #t
             (contains? rt "(crashed? (not ran-summary?))"))
      (check "m38/imp1/fix/crashed-fails-too" #t
             (contains? rt "(if (or crashed? mismatch?)"))
      (check "m38/imp1/fix/crashed-message" #t
             (contains? rt "batch runner never completed"))

      ;; --- 4. run-tests pushes the fail list into the accumulator. ---
      (check "m38/imp1/fix/pushes-to-ert-fail-accumulator" #t
             (contains? rt "(push-append! %total-failed-ert-tests fail)"))

      ;; --- 5. The report reads the accumulator. ----------------------
      (check "m38/imp1/report/includes-accumulator" #t
             (contains? rt "(num-total-failed-ert-tests (+ (length failed-ert)"))

      ;; --- 5b. Review F3: one number, and the dead binding is gone. ---
      (check "m38/imp1/report/failed-line-uses-total" #t
             (contains? rt "Total number of failed/missing ERT tests"))
      (check "m38/imp1/report/old-missing-line-gone" #t
             (not (contains? rt "Total number of missing tests:")))
      (check "m38/imp1/report/dead-binding-gone" #t
             (not (contains? rt "num-total-missing-ert-tests")))

      ;; --- 6. The exit status reads it; one exit path. ---------------
      (check "m38/imp1/exit/reads-gen-failures" #t
             (contains? rt "num-total-failed-gen-tests"))
      (check "m38/imp1/exit/reads-ert-failures" #t
             (contains? rt "num-total-failed-ert-tests"))
      (check "m38/imp1/exit/single-exit-path" 1 (count-substr rt "(exit "))

      ;; --- 7. run-tests-bare-emacs: no numeric count line. -----------
      ;; The bare path has no "passed N/M" summary to compare.  Its
      ;; begin/end protocol records an unmatched test as a failure, so no
      ;; count check is added (brief.org M38 imp-1 Step 4 decision).
      (info "m38/imp1/fix/bare-emacs-decision"
            "no count line; begin/end protocol records the failure")

      ;; --- 8. Registration. ------------------------------------------
      (check "m38/imp1/register/corpus-el" #t
             (contains? rt "\"test/keyboard/test-m38-imp1.el\""))
      (check "m38/imp1/register/fixture-el" #t
             (contains? rt "\"test/m38/test-m38-imp1-fixture.el\""))))
