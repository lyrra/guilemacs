;;; test-stub.el

;; Verifies the keyboard.c → Guile port scaffolding loaded:
;; the (emacs keyboard-stub) module is on the load path, its
;; init-keyboard-stub-registrations ran during prelude/load.scm, and
;; kb-loaded-p is callable as an elisp function.
;;

(test-begin "keyboard-stub")

(test-assert "kb-loaded-p/fboundp" (fboundp 'kb-loaded-p))
(test-eq     "kb-loaded-p/returns-t" t (kb-loaded-p))

(test-end)
