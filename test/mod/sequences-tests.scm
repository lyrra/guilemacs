;;; SRFI-64 tests for pure procedures in (emacs sequences).

(use-modules (srfi srfi-64)
             (emacs sequences))

;; Pinned case count.  A suite that loses a case must fail (cr.org F3).
(define expected-passes 3)

;; No SRFI-64 log file: it would land in the working directory (cr.org F4).
(set! test-log-to-file #f)

(test-begin "Guilemacs sequences module")
(define test-runner (test-runner-current))

(test-equal "nth returns the selected element"
            'beta
            (elisp-nth 1 '(alpha beta gamma)))
(test-equal "nth returns nil past the end"
            #nil
            (elisp-nth 9 '(alpha beta gamma)))
(test-equal "nthcdr returns the selected tail"
            '(beta gamma)
            (elisp-nthcdr 1 '(alpha beta gamma)))

(test-end "Guilemacs sequences module")

(let ((passes (test-runner-pass-count test-runner))
      (fails  (test-runner-fail-count test-runner)))
  (format #t "~a: ~a passed, ~a failed (expected ~a passed)~%"
          "Guilemacs sequences module" passes fails expected-passes)
  (exit (if (and (zero? fails) (= passes expected-passes)) 0 1)))
