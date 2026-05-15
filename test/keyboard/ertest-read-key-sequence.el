;;; ertest-read-key-sequence.el --- M6a ERT suite for (emacs read-key-sequence)

;; M6a — outer wrapper port (read_key_sequence_vs in src/keyboard.c).
;; The state machine itself stays C (--read-key-sequence-and-vector).
;; We test the housekeeping wrapper via the elisp-registered shim
;; `--read-key-sequence-vs' and stub the C primitive by rebinding its
;; symbol-function for each test (advice didn't compose reliably in
;; this Guile-elisp environment).
;;
;; See docs/keyboard.org §M6a.

(require 'ert)

;;;; Existence checks

(ert-deftest m6a-wrapper/exists ()
  (should (fboundp '--read-key-sequence-vs))
  ;; The user-visible DEFUNs still resolve (now via cached-SCM dispatch).
  (should (fboundp 'read-key-sequence))
  (should (fboundp 'read-key-sequence-vector)))

(ert-deftest m6a-helpers/exist ()
  (should (fboundp '--read-key-sequence-and-vector))
  ;; --make-event-array-from-vector is shared with M3/M5 (3-arg form).
  (should (fboundp '--make-event-array-from-vector)))

;;;; Test helper that rebinds the C subr's elisp dispatch for the
;;;; duration of THUNK then restores.  Avoids the advice machinery.

(defun m6a-with-stub-rks (stub thunk)
  "Run THUNK with --read-key-sequence-and-vector's elisp binding
replaced by STUB.  Restore afterwards regardless of how THUNK exits."
  (let ((saved (symbol-function '--read-key-sequence-and-vector)))
    (unwind-protect
        (progn
          (fset '--read-key-sequence-and-vector stub)
          (funcall thunk))
      (fset '--read-key-sequence-and-vector saved))))

;;;; Wrapper specbind behavior

(ert-deftest m6a-wrapper/specbinds-input-method-vars-when-cmd-loop-nil ()
  ;; When cmd-loop arg is nil, the two input-method vars are bound to t
  ;; for the duration of the read.
  (let ((saved-exit input-method-exit-on-first-char)
        (saved-echo input-method-use-echo-area)
        (observed nil))
    (unwind-protect
        (progn
          (setq input-method-exit-on-first-char nil
                input-method-use-echo-area nil)
          (m6a-with-stub-rks
           (lambda (&rest _args)
             (setq observed (cons input-method-exit-on-first-char
                                  input-method-use-echo-area))
             [])
           (lambda ()
             (--read-key-sequence-vs nil nil nil nil nil nil nil)))
          (should (eq t (car observed)))
          (should (eq t (cdr observed)))
          (should (eq nil input-method-exit-on-first-char))
          (should (eq nil input-method-use-echo-area)))
      (setq input-method-exit-on-first-char saved-exit
            input-method-use-echo-area saved-echo))))

(ert-deftest m6a-wrapper/resets-key-counters-when-continue-echo-nil ()
  (let (observed)
    (m6a-with-stub-rks
     (lambda (&rest _args)
       (setq observed (cons (--this-command-key-count)
                            (--this-single-command-key-start)))
       [])
     (lambda ()
       (--set-this-command-key-count        5)
       (--set-this-single-command-key-start 3)
       (--read-key-sequence-vs nil nil nil nil nil nil nil)))
    (should (= 0 (car observed)))
    (should (= 0 (cdr observed)))))

(ert-deftest m6a-wrapper/skips-counter-reset-when-continue-echo-non-nil ()
  (let (observed)
    (m6a-with-stub-rks
     (lambda (&rest _args)
       (setq observed (cons (--this-command-key-count)
                            (--this-single-command-key-start)))
       [])
     (lambda ()
       (--set-this-command-key-count        7)
       (--set-this-single-command-key-start 4)
       (--read-key-sequence-vs nil t nil nil nil nil nil)))
    (should (= 7 (car observed)))
    (should (= 4 (cdr observed)))))

(ert-deftest m6a-wrapper/allow-string-converts-vector ()
  (let ((result
         (m6a-with-stub-rks
          (lambda (&rest _args) [?a ?b ?c])
          (lambda ()
            (--read-key-sequence-vs nil t nil nil nil t nil)))))
    (should (stringp result))
    (should (equal "abc" result))))

(ert-deftest m6a-wrapper/disallow-string-returns-vector ()
  (let ((result
         (m6a-with-stub-rks
          (lambda (&rest _args) [?a ?b ?c])
          (lambda ()
            (--read-key-sequence-vs nil t nil nil nil nil nil)))))
    (should (vectorp result))
    (should (= 3 (length result)))))

;;;; M6b — discard-input

(ert-deftest m6b-discard-input/exists ()
  (should (fboundp 'discard-input))
  (should (fboundp '--discard-input)))

(ert-deftest m6b-helpers/exist ()
  (should (fboundp '--end-kbd-macro))
  (should (fboundp '--discard-tty-input))
  (should (fboundp '--reset-kbd-ring-and-pending)))

(ert-deftest m6b-discard-input/clears-unread-command-events ()
  ;; discard-input always sets unread-command-events to nil.
  (let ((saved unread-command-events))
    (unwind-protect
        (progn
          (setq unread-command-events '(?a ?b ?c))
          (discard-input)
          (should (eq nil unread-command-events)))
      (setq unread-command-events saved))))

(ert-deftest m6b-discard-input/returns-nil ()
  (should (eq nil (discard-input))))

(provide 'ertest-read-key-sequence)
