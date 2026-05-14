;;; ertest-recursive-edit.el --- M4 ERT suite for (emacs recursive-edit)

;; M4 gating tests.  Exercises the three user-facing DEFUNs now ported
;; to mod/emacs/recursive-edit.scm: exit-recursive-edit,
;; abort-recursive-edit, recursion-depth.  Batch mode means
;; command_loop_level is 0 (top level) and we can't actually enter a
;; recursive edit, but we can verify:
;;
;;   - recursion-depth reflects --command-loop-level + --minibuf-level
;;   - exit/abort signal user-error when no nesting is in progress
;;   - exit/abort throw to `exit' with the correct value when nesting
;;     is faked (we can't fake the C-side level, but we can verify the
;;     throw shape by catching it outside any actual loop)
;;
;; The full recursive-edit flow (Frecursive_edit + recursive_edit_1 +
;; command_loop) is M7 territory and is not exercised here.
;;
;; See docs/keyboard.org §"M4 — Recursive edit, command-loop level,
;; prefix args".

(require 'ert)

;;;; recursion-depth

(ert-deftest m4-recursion-depth/top-level ()
  ;; At batch top-level: command_loop_level = 0, minibuf_level = 0.
  (should (= (recursion-depth) 0)))

(ert-deftest m4-recursion-depth/matches-sum ()
  ;; The result equals --command-loop-level + --minibuf-level (by
  ;; construction).  Both should be non-negative ints at this point.
  (let ((cll (--command-loop-level))
        (mbl (--minibuf-level)))
    (should (integerp cll))
    (should (integerp mbl))
    (should (= (recursion-depth) (+ cll mbl)))))

;;;; exit-recursive-edit signals when not nesting

(ert-deftest m4-exit/signals-outside-nesting ()
  (should-error (exit-recursive-edit) :type 'user-error))

(ert-deftest m4-exit/signal-message ()
  ;; The message text matches the C original verbatim.
  (let ((err (should-error (exit-recursive-edit) :type 'user-error)))
    (should (equal (cadr err) "No recursive edit is in progress"))))

;;;; abort-recursive-edit signals when not nesting

(ert-deftest m4-abort/signals-outside-nesting ()
  (should-error (abort-recursive-edit) :type 'user-error))

(ert-deftest m4-abort/signal-message ()
  (let ((err (should-error (abort-recursive-edit) :type 'user-error)))
    (should (equal (cadr err) "No recursive edit is in progress"))))

;;;; The throw shape — exercise by catching 'exit ourselves

(ert-deftest m4-exit/throws-nil-when-nesting ()
  ;; We can't actually be inside a recursive-edit in batch, but we
  ;; can mock --command-loop-level locally to force the throw path.
  (cl-letf (((symbol-function '--command-loop-level) (lambda () 1)))
    (should (eq (catch 'exit (exit-recursive-edit) 'unreached) nil))))

(ert-deftest m4-abort/throws-t-when-nesting ()
  (cl-letf (((symbol-function '--command-loop-level) (lambda () 1)))
    (should (eq (catch 'exit (abort-recursive-edit) 'unreached) t))))

(ert-deftest m4-exit/triggered-by-minibuf-level ()
  ;; Either of the two counters being positive enables the throw.
  (cl-letf (((symbol-function '--minibuf-level) (lambda () 1)))
    (should (eq (catch 'exit (exit-recursive-edit) 'unreached) nil))))

(provide 'ertest-recursive-edit)

;;; ertest-recursive-edit.el ends here
