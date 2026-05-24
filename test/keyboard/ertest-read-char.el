;;; ertest-read-char.el --- M8a ERT suite for (emacs read-char)

;; M8a — foundation only.  Module skeleton + <rc-state> Scheme
;; record type + C-side state-pointer stack with 4 trivial getters.
;; No splices into read_char_1 yet — those start at M8e.
;;
;; See docs/keyboard.org §M8.

(require 'ert)

;;;; Existence checks

(ert-deftest m8a-helpers/exist ()
  (should (fboundp '--rc-state-depth))
  (should (fboundp '--rc-commandflag))
  (should (fboundp '--rc-map))
  (should (fboundp '--rc-prev-event))
  (should (fboundp '--rc-reread-p))
  (should (fboundp '--make-rc-state))
  (should (fboundp '--rc-state-fresh!)))

;;;; C-side stack at idle

(ert-deftest m8a-state-depth/zero-at-idle ()
  ;; Outside any in-flight read_char invocation, depth is 0.
  (should (= 0 (--rc-state-depth))))

(ert-deftest m8a-getters/defaults-when-stack-empty ()
  ;; Each accessor returns its struct-default when the stack is
  ;; empty (no crash on dereferencing the empty stack).
  (should (= 0 (--rc-commandflag)))
  (should (eq nil (--rc-map)))
  (should (eq nil (--rc-prev-event)))
  (should (eq nil (--rc-reread-p))))

;;;; Scheme record

(ert-deftest m8a-rc-state/constructs-non-nil ()
  (let ((s (--make-rc-state)))
    (should (not (null s)))))

(ert-deftest m8a-rc-state-fresh/runs-without-error ()
  ;; Resetting a freshly-constructed state is a no-op (defaults =
  ;; defaults) but must not error.
  (let ((s (--make-rc-state)))
    (--rc-state-fresh! s)
    (should t)))

;;;; M8b — extended accessors

(ert-deftest m8b-helpers/exist ()
  (should (fboundp '--rc-c))
  (should (fboundp '--set-rc-c))
  (should (fboundp '--rc-recorded-p))
  (should (fboundp '--set-rc-recorded))
  (should (fboundp '--set-rc-reread))
  (should (fboundp '--rc-set-used-mouse-menu)))

(ert-deftest m8b-setters/no-op-when-stack-empty ()
  ;; Outside any in-flight read_char, setters silently succeed
  ;; (return nil, mutate nothing).
  (should (eq nil (--set-rc-c 'sentinel)))
  (should (eq nil (--set-rc-recorded t)))
  (should (eq nil (--set-rc-reread t)))
  (should (eq nil (--rc-set-used-mouse-menu t))))

;;;; M8c — prologue drain

(ert-deftest m8c-helpers/exist ()
  (should (fboundp '--rc-prologue-drain-unread)))

(ert-deftest m8c-drain/fall-through-at-idle ()
  ;; Outside any in-flight read_char, the stack is empty and the
  ;; subr early-returns `fall-through' before touching anything.
  (should (eq 'fall-through (--rc-prologue-drain-unread!))))

(provide 'ertest-read-char)
