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

;;;; M6b

(test-assert "m6b/discard-input-exists" (fboundp 'discard-input))
(test-assert "m6b/dispatch-shim-exists" (fboundp '--discard-input))
(test-assert "m6b-helper/end-kbd-macro" (fboundp '--end-kbd-macro))
(test-assert "m6b-helper/discard-tty-input" (fboundp '--discard-tty-input))
(test-assert "m6b-helper/reset-kbd-ring-and-pending"
             (fboundp '--reset-kbd-ring-and-pending))

(let ((saved unread-command-events))
  (setq unread-command-events '(?a ?b ?c))
  (discard-input)
  (test-eq "m6b/clears-unread-command-events" nil unread-command-events)
  (setq unread-command-events saved))

(test-eq "m6b/returns-nil" nil (discard-input))

;;;; M6c

(test-assert "m6c/current-input-mode-exists" (fboundp 'current-input-mode))
(test-assert "m6c/set-input-mode-exists"     (fboundp 'set-input-mode))
(test-assert "m6c-helper/interrupt-input-p"  (fboundp '--interrupt-input-p))
(test-assert "m6c-helper/selected-frame-tty-p"
             (fboundp '--selected-frame-tty-p))
(test-assert "m6c-helper/selected-frame-tty-flow-control-p"
             (fboundp '--selected-frame-tty-flow-control-p))
(test-assert "m6c-helper/selected-frame-tty-meta-key"
             (fboundp '--selected-frame-tty-meta-key))

(let ((m (current-input-mode)))
  (test-assert "m6c/current-input-mode-is-list" (listp m))
  (test-equal  "m6c/current-input-mode-length"  4 (length m))
  (test-assert "m6c/quit-is-integer" (integerp (nth 3 m))))

;;;; M6d

(test-assert "m6d/posn-at-point-exists" (fboundp 'posn-at-point))

(let ((r (with-current-buffer (window-buffer (selected-window))
           (posn-at-point))))
  (test-assert "m6d/posn-at-point-runs" (or (eq r nil) (consp r))))

;;;; M6e

(test-assert "m6e/input-pending-p-exists" (fboundp 'input-pending-p))
(test-assert "m6e-helper/requeued-events-pending-p"
             (fboundp '--requeued-events-pending-p))
(test-assert "m6e-helper/process-special-events"
             (fboundp '--process-special-events))
(test-assert "m6e-helper/get-input-pending"
             (fboundp '--get-input-pending))

(let ((r (input-pending-p)))
  (test-assert "m6e/input-pending-p-boolean"
               (or (eq r t) (eq r nil))))

;;;; M6f

(test-assert "m6f/active-maps-exists" (fboundp '--active-maps))

(let ((m (--active-maps ?a nil)))
  (test-assert "m6f/active-maps-consp" (consp m))
  (test-eq    "m6f/active-maps-car-keymap" 'keymap (car m)))

(test-end)
