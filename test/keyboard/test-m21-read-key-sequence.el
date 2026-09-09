;;; test-m21-read-key-sequence.el --- M21 imp-1 + imp-2 + imp-3 + imp-4 parity test suite.
;;;
;;; imp-1: the --access-keymap shim (Task 1, covered in
;;; test-read-key-sequence.el) plus the parity check that
;;; rks-setup-replay-entire-sequence! (explicit-state) and the runtime
;;; rks-setup-replay-entire-sequence-c! (rebases the live record) produce
;;; identical indec/fkey/keytran <keyremap> setups (Task 2).
;;;
;;; imp-2: direct unit checks (section 3 of the Scheme corpus) on the
;;; Scheme port rks-keyremap-step! of C keyremap_step +
;;; access_keymap_keyremap (src/keyboard.c:10601-10715), plus loop-level
;;; walk checks.
;;;
;;; imp-3: cut the three keyremap-walk shims, follow_key, and the
;;; mouse-event reduction cascade to Scheme, then delete the dead C
;;; bodies.  Sections 3.13-3.15 exercise the composed Scheme walk
;;; (rks-walk-translation-maps!), the follow_key port (rks-follow-key),
;;; and the mouse-reduction cascade on a pushed <rks-state>.
;;;
;;; imp-4: hoist the outer read_key_sequence skeleton into the Scheme
;;; entry points rks-read-key-sequence-start! / -run! / -finish!.  Section 4 of
;;; the Scheme corpus covers the entry points + with-rks-sync; the elisp
;;; end-to-end block below drives the *real, unmocked* read-key-sequence
;;; through the live C read_key_sequence (keybuf-stack push included)
;;; and checks the menu-reject path no longer leaks a state-stack slot.
;;;
;;; Wraps test/keyboard/test-m21-read-key-sequence.scm — the Scheme test
;;; corpus.  Loads the Scheme file via eval-scheme, then reads back
;;; `test-results` (list of (NAME STATUS) pairs) and reports each via
;;; princ.  Same harness as test-m20-menu-prompt.el.  See
;;; docs/m21-plan.org and brief.org.

(princ "=== m21 read-key-sequence test suite ===\n")

;; Run the Scheme test corpus.  Populates test-results in the
;; (guile-user) module.  Resolve the corpus path from load-file-name so
;; it works both from the repo root (run-all-tests.el) and from the
;; harness, which loads this file with CWD=test/.
(let* ((dir (file-name-directory (or load-file-name default-directory)))
       (corpus (expand-file-name "test-m21-read-key-sequence.scm" dir)))
  (condition-case err
      (eval-scheme
       (format "(primitive-load %S)" corpus))
    (error (princ (format "M21-CORPUS-LOAD-ERROR: %S\n" err)))))

;;;; ------------------------------------------------------------------
;;;; M21 imp-4 — true end-to-end: real (unmocked) read-key-sequence.
;;;; Drives the live C read_key_sequence — the keybuf-stack push and the
;;;; full Scheme start!/finish! round trip — for the first time.  The
;;;; older read-key-sequence suites mock --read-key-sequence-and-vector,
;;;; so none exercised this path.  Each check is pushed into the Scheme
;;;; test-results list so the summary below counts it.
(defun m21-imp4-report (name status)
  "Push (NAME STATUS) into the Scheme test-results list.
STATUS is either the symbol `PASS' or a FAIL list (FAIL KEY ...)."
  (eval-scheme
   (format "(set! test-results (cons (list %S (quote %S)) test-results))"
           name status)))

;; e2e/sequence: a single self-insert key (a complete binding) must
;; come back as the 1-element sequence "x" through the real C body.
(let ((saved-events unread-command-events))
  (setq unread-command-events '(120))        ; ?x
  (condition-case err
      (m21-imp4-report "m21/imp4/e2e/sequence"
                       (let ((seq (read-key-sequence nil)))
                         (if (equal seq "x") 'PASS
                           (list 'FAIL 'expected "x" 'got seq))))
    (error
     (m21-imp4-report "m21/imp4/e2e/sequence"
                      (list 'FAIL 'error (format "%S" err)))))
  (setq unread-command-events saved-events))

;; e2e/reuse: a second read after the first proves the success-path pop
;; (rks-read-key-sequence-finish!) balanced the state stack.
(let ((saved-events unread-command-events))
  (setq unread-command-events '(121))        ; ?y
  (condition-case err
      (m21-imp4-report "m21/imp4/e2e/reuse"
                       (let ((seq (read-key-sequence nil)))
                         (if (equal seq "y") 'PASS
                           (list 'FAIL 'expected "y" 'got seq))))
    (error
     (m21-imp4-report "m21/imp4/e2e/reuse"
                      (list 'FAIL 'error (format "%S" err)))))
  (setq unread-command-events saved-events))

;; e2e/menu-reject (Finding D): an event of `t` is the menu-reject
;; sentinel, so read_key_sequence returns -1 and read-key-sequence
;; signals `quit`.  A subsequent successful read then proves the -1
;; path popped the state record (no leaked state-stack slot).
(let ((saved-events unread-command-events))
  (setq unread-command-events '(t))
  (condition-case err
      (progn
        (read-key-sequence nil)
        (m21-imp4-report "m21/imp4/e2e/menu-reject"
                         (list 'FAIL 'expected 'quit 'got 'no-signal)))
    (quit (m21-imp4-report "m21/imp4/e2e/menu-reject" 'PASS))
    (error (m21-imp4-report "m21/imp4/e2e/menu-reject"
                            (list 'FAIL 'error (format "%S" err)))))
  ;; Stack must still be balanced after the rejected read.
  (setq unread-command-events '(122))        ; ?z
  (condition-case err
      (m21-imp4-report "m21/imp4/e2e/after-reject"
                       (let ((seq (read-key-sequence nil)))
                         (if (equal seq "z") 'PASS
                           (list 'FAIL 'expected "z" 'got seq))))
    (error
     (m21-imp4-report "m21/imp4/e2e/after-reject"
                      (list 'FAIL 'error (format "%S" err)))))
  ;; Undo the this-command-keys / raw-keybuf side effects of the reads
  ;; above.  These run in the same emacs process as the rest of the
  ;; keyboard gate, whose ERT tests (m5) assert the empty initial state.
  (condition-case err
      (progn
        (clear-this-command-keys)
        (--set-raw-keybuf-count 0))
    (error (princ (format "M21-IMP4-CLEANUP-ERROR: %S\n" err))))
  (setq unread-command-events saved-events))

;; Read each result back and report PASS/FAIL.
(let ((results (condition-case e
                   (eval-scheme "(reverse test-results)")
                 (error (princ (format "M21-READBACK-ERROR: %S\n" e)) '())))
      (pass 0)
      (fail 0))
  (dolist (result results)
    (let* ((name (car result))
           (status (cadr result))
           (ok (eq status 'PASS)))
      (if ok
          (setq pass (1+ pass))
        (setq fail (1+ fail)))
      (princ (format "%s %s%s\n" (if ok "PASS" "FAIL") name
                     (if ok "" (format " %S" (cdr result)))))))
  (princ (format "=== %d passed, %d failed, %d total ===\n"
                 pass fail (+ pass fail))))
