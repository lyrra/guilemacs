;;; test-stub.el

;; Verifies the keyboard.c → Guile port scaffolding loaded:
;; the (emacs keyboard-stub) module is on the load path, its
;; init-keyboard-stub-registrations ran during prelude/load.scm, and
;; kb-loaded-p is callable as an elisp function.

(require 'ert)

(ert-deftest keyboard-stub-loaded ()
  "(emacs keyboard-stub) module is wired into the prelude."
  (should (fboundp 'kb-loaded-p))
  (should (eq t (kb-loaded-p))))

(provide 'test-stub)
