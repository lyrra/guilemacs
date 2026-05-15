;;; test-read-key-sequence.el --- M6a SRFI-64 suite

;; Same coverage as ertest-read-key-sequence.el, transcribed for the
;; test-framework.el / SRFI-64 harness.  Keep in sync.

(test-begin "read-key-sequence")

;;;; Existence checks

(test-assert "wrapper/exists"     (fboundp '--read-key-sequence-vs))
(test-assert "elisp/read-key-sequence-fboundp"
             (fboundp 'read-key-sequence))
(test-assert "elisp/read-key-sequence-vector-fboundp"
             (fboundp 'read-key-sequence-vector))
(test-assert "helper/read-key-sequence-and-vector"
             (fboundp '--read-key-sequence-and-vector))
(test-assert "helper/make-event-array-from-vector"
             (fboundp '--make-event-array-from-vector))

;;;; Wrapper behavior — mocked --read-key-sequence-and-vector

(advice-add '--read-key-sequence-and-vector :around
            (lambda (orig &rest args) [?a ?b ?c]))

(let ((result (--read-key-sequence-vs nil t nil nil nil t nil)))
  (test-assert "wrapper/allow-string-stringp" (stringp result))
  (test-equal  "wrapper/allow-string-value"   "abc" result))

(let ((result (--read-key-sequence-vs nil t nil nil nil nil nil)))
  (test-assert "wrapper/disallow-string-vectorp" (vectorp result))
  (test-equal  "wrapper/disallow-string-length" 3 (length result)))

(advice-remove '--read-key-sequence-and-vector
               (lambda (orig &rest args) [?a ?b ?c]))

;;;; Counter reset behavior

(let (observed)
  (advice-add '--read-key-sequence-and-vector :around
              (lambda (orig &rest args)
                (setq observed (cons (--this-command-key-count)
                                     (--this-single-command-key-start)))
                []))
  (--set-this-command-key-count        5)
  (--set-this-single-command-key-start 3)
  (--read-key-sequence-vs nil nil nil nil nil nil nil)
  (test-equal "wrapper/continue-echo-nil-resets-count" 0 (car observed))
  (test-equal "wrapper/continue-echo-nil-resets-start" 0 (cdr observed))
  (advice-remove '--read-key-sequence-and-vector
                 (lambda (orig &rest args)
                   (setq observed (cons (--this-command-key-count)
                                        (--this-single-command-key-start)))
                   [])))

(test-end)
