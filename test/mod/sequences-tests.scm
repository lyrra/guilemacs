;;; SRFI-64 tests for pure procedures in (emacs sequences).

(use-modules (srfi srfi-64)
             (emacs sequences))

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
(exit (if (> (test-runner-fail-count test-runner) 0) 1 0))
