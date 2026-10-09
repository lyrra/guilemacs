;;; test-m52-imp3.el --- M52 imp-3 TTY output behavior tests.  -*- lexical-binding: t; -*-
;;;
;;; These cases start the built Emacs on a pseudo-terminal.  The child
;;; calls the (emacs tty-output) Scheme wrappers; the driver checks bytes
;;; read from the pty master.  This covers the C leaves, the Scheme
;;; wrappers, and their connection to Emacs's live TTY output streams.
;;;
;;; Source-layout checks do not belong in this behavior corpus.

(princ "=== m52 imp-3 TTY output behavior suite ===\n")

(require 'imp-ert-report)

(let ((dir (expand-file-name "../m42"
                             (file-name-directory
                              (or load-file-name default-directory)))))
  (add-to-list 'load-path dir)
  (require 'pty-runner))

(defvar m52-imp3--registered 0
  "Number of M52 output behavior cases registered by this corpus.")

(let* ((results
        (condition-case err
            (m52-imp3-run-driver)
          (error (list (cons "m52-imp3/runner" (cons 'FAIL (format "%S" err)))))))
       (wanted m52-imp3--cases))
  (when (null results)
    (setq results (list (cons "m52-imp3/report"
                              (cons 'FAIL "driver produced no case results")))))
  (dolist (name wanted)
    (unless (assoc name results)
      (setq results (append results
                            (list (cons name (cons 'FAIL "driver omitted this case")))))))
  (dolist (result results)
    (let ((name (car result))
          (status (cdr result)))
      (setq m52-imp3--registered (1+ m52-imp3--registered))
      (cond
       ((eq status 'PASS)
        (imp-register-check-as-ert-test name status)
        (princ (format "PASS %s\n" name)))
       ((and (consp status) (eq (car status) 'INFO))
        (imp-register-skip-as-ert-test name (cadr status))
        (princ (format "INFO %s %s\n" name (cadr status))))
       (t
        (imp-register-check-as-ert-test name status)
        (princ (format "FAIL %s %S\n" name (cdr result))))))))

(ert-deftest m52-imp3/gate-has-output-cases ()
  "The M52 group registers all three TTY output behavior cases."
  (should (>= m52-imp3--registered 3)))

;; The pty cases need a pty device.  Some hosts (a locked-down build
;; sandbox) cannot allocate one, so the driver returns an explicit INFO
;; skip and the byte-output checks never run there.  The four leaves
;; still have a checkable contract that needs no pty: a device that does
;; not resolve to a tty must return the negated errno -EINVAL (-22), the
;; same shape for all four leaves (brief.org section 5.1, cr1.org F6).
;; A non-bytevector BYTES argument is also -EINVAL (the bytevector rule,
;; cr1.org F2).  This check keeps the boundary contract covered on every
;; host, with or without pty support.
(ert-deftest m52-imp3/nil-device-contract ()
  "All four leaves return -22 (negated EINVAL) for a nil / bad device."
  (should (eql -22 (--tty-emit-cap nil "bell" nil)))
  (should (eql -22 (--tty-write-bytes nil "not-a-bytevector")))
  (should (eql -22 (--tty-flush nil)))
  (should (eql -22 (--tty-emit-seq nil (list (cons "bell" nil))))))

;; A second headless check keeps the Scheme side of the boundary covered:
;; the module must load and export its four thin wrappers.  This is
;; acceptance item "the module loads and crosses plain values only"
;; (brief.org section 12).  The pty cases reach the wrappers too, but
;; only when a pty exists, so this check runs on every host.  Resolve the
;; module through the elisp `eval-scheme' bridge; a missing module or a
;; missing export yields 0, so the check FAILS on any gap.
(ert-deftest m52-imp3/module-exports-wrappers ()
  "The (emacs tty-output) module loads and exports the 4 wrappers."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and (procedure? (module-ref m 'tty-emit-cap))"
          " (procedure? (module-ref m 'tty-write-bytes))"
          " (procedure? (module-ref m 'tty-flush))"
          " (procedure? (module-ref m 'tty-emit-seq)))"
          " 1 0))")))))

;; A third headless check drives the wrapper layer itself, not only its
;; export.  It calls each (emacs tty-output) wrapper through the module
;; with a nil device and asserts the leaf contract (-22, negated
;; EINVAL).  This exercises the wrapper -> C leaf plumbing (module-ref
;; plus the delayed defelisp reference) on every host.  The
;; nil-device-contract check above calls the C DEFUNs directly; it never
;; reaches a wrapper, so this is the only pty-free cover of the thin
;; wrappers.
(ert-deftest m52-imp3/wrappers-nil-device-contract ()
  "Each Scheme wrapper returns -22 for a nil device (no pty needed)."
  (should
   (eql 1
        (eval-scheme
         (concat
          "(let ((m (resolve-module '(emacs tty-output))))"
          " (if (and (= -22 ((module-ref m 'tty-emit-cap) #nil \"bell\" #nil))"
          "          (= -22 ((module-ref m 'tty-write-bytes) #nil #vu8(7)))"
          "          (= -22 ((module-ref m 'tty-flush) #nil))"
          "          (= -22 ((module-ref m 'tty-emit-seq) #nil"
          "                  (list (cons \"bell\" (list))))))"
          " 1 0))")))))

(princ (format "=== m52 imp-3 behavior suite done (%d cases) ===\n"
               m52-imp3--registered))
