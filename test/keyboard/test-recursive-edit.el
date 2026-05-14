;;; test-recursive-edit.el --- M4 SRFI-64 suite for (emacs recursive-edit)

;; Same coverage as ertest-recursive-edit.el, transcribed for the
;; test-framework.el / SRFI-64 harness.  Keep in sync.

(test-begin "recursive-edit")

;;;; recursion-depth

(test-equal "recursion-depth/top-level" 0 (recursion-depth))

(test-equal "recursion-depth/matches-sum"
            (+ (--command-loop-level) (--minibuf-level))
            (recursion-depth))

;;;; exit-recursive-edit / abort-recursive-edit signal when not nesting

(test-assert "exit/signals-outside"
             (condition-case nil
                 (progn (exit-recursive-edit) nil)
               (user-error t)))

(test-assert "exit/signal-message"
             (condition-case e
                 (progn (exit-recursive-edit) nil)
               (user-error (equal (cadr e) "No recursive edit is in progress"))))

(test-assert "abort/signals-outside"
             (condition-case nil
                 (progn (abort-recursive-edit) nil)
               (user-error t)))

(test-assert "abort/signal-message"
             (condition-case e
                 (progn (abort-recursive-edit) nil)
               (user-error (equal (cadr e) "No recursive edit is in progress"))))

;;;; Throw shape — mock --command-loop-level to force the throw path

(test-eq "exit/throws-nil-when-nesting"
         nil
         (cl-letf (((symbol-function '--command-loop-level) (lambda () 1)))
           (catch 'exit (exit-recursive-edit) 'unreached)))

(test-eq "abort/throws-t-when-nesting"
         t
         (cl-letf (((symbol-function '--command-loop-level) (lambda () 1)))
           (catch 'exit (abort-recursive-edit) 'unreached)))

(test-eq "exit/triggered-by-minibuf-level"
         nil
         (cl-letf (((symbol-function '--minibuf-level) (lambda () 1)))
           (catch 'exit (exit-recursive-edit) 'unreached)))

(test-end)
