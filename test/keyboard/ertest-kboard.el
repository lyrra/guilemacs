;;; ertest-kboard.el --- M2 ERT suite for (emacs kboard)

;; M2 gating tests for the keyboard.c → Guile port.  Exercises the
;; KBOARD foreign-object wrapper: predicate, identity, the per-field
;; accessors (sampled), current-kboard/set-current-kboard, and the
;; with-kboard dynamic-wind operator (including unwind via throw).
;;
;; Batch mode has a single kboard so we can't test multi-kboard
;; switching here — that's covered by interactive multi-frame smoke.
;;
;; See docs/keyboard.org §"M2 — KBOARD foreign object".

(require 'ert)

;;;; predicate + identity

(ert-deftest m2-kboardp/positive ()
  (should (kboardp (current-kboard))))

(ert-deftest m2-kboardp/negative ()
  (should-not (kboardp 'not-a-kboard))
  (should-not (kboardp 42))
  (should-not (kboardp nil))
  (should-not (kboardp "string")))

(ert-deftest m2-kboard-eq/same-pointer ()
  ;; Two handles fetched separately should kboard-eq if they wrap
  ;; the same KBOARD*.
  (should (kboard-eq (current-kboard) (current-kboard))))

(ert-deftest m2-kboard-eq/checks-type ()
  (should-error (kboard-eq (current-kboard) 'not-a-kboard)
                :type 'wrong-type-argument))

;;;; accessor round-trips (sample three different field types)

(ert-deftest m2-accessor/last-command-roundtrip ()
  (let* ((kb (current-kboard))
         (orig (kboard-last-command kb)))
    (unwind-protect
        (progn
          (set-kboard-last-command kb 'sentinel-cmd)
          (should (eq (kboard-last-command kb) 'sentinel-cmd)))
      (set-kboard-last-command kb orig))))

(ert-deftest m2-accessor/echo-string-roundtrip ()
  (let* ((kb (current-kboard))
         (orig (kboard-echo-string kb)))
    (unwind-protect
        (progn
          (set-kboard-echo-string kb "C-x C-")
          (should (equal (kboard-echo-string kb) "C-x C-")))
      (set-kboard-echo-string kb orig))))

(ert-deftest m2-accessor/window-system-roundtrip ()
  (let* ((kb (current-kboard))
         (orig (kboard-window-system kb)))
    (unwind-protect
        (progn
          (set-kboard-window-system kb 'fake-win-sys)
          (should (eq (kboard-window-system kb) 'fake-win-sys)))
      (set-kboard-window-system kb orig))))

;;;; getter type-checking

(ert-deftest m2-accessor/getter-checks-type ()
  (should-error (kboard-last-command 'not-a-kboard)
                :type 'wrong-type-argument)
  (should-error (kboard-echo-string nil)
                :type 'wrong-type-argument))

(ert-deftest m2-accessor/setter-checks-type ()
  (should-error (set-kboard-last-command 'not-a-kboard 'foo)
                :type 'wrong-type-argument))

;;;; current-kboard / set-current-kboard

(ert-deftest m2-current-kboard/returns-kboard ()
  (should (kboardp (current-kboard))))

(ert-deftest m2-set-current-kboard/round-trip ()
  ;; Single-kboard environment: setting to the only kboard is a no-op.
  (let ((kb (current-kboard)))
    (set-current-kboard kb)
    (should (kboard-eq (current-kboard) kb))))

(ert-deftest m2-set-current-kboard/checks-type ()
  (should-error (set-current-kboard 'not-a-kboard)
                :type 'wrong-type-argument))

;;;; with-kboard

(ert-deftest m2-with-kboard/calls-thunk ()
  ;; Thunk runs and its return value is the result.
  (should (eq (with-kboard (current-kboard) (lambda () 'thunk-ran))
              'thunk-ran)))

(ert-deftest m2-with-kboard/identity-during-thunk ()
  ;; Inside the thunk, (current-kboard) is the kboard we passed.
  (let ((kb (current-kboard)))
    (with-kboard kb
      (lambda ()
        (should (kboard-eq (current-kboard) kb))))))

(ert-deftest m2-with-kboard/restores-after-throw ()
  ;; A throw out of the thunk must still restore the saved kboard
  ;; via dynamic-wind.  (Single-kboard env, so we just verify the
  ;; outer (current-kboard) survives and matches.)
  (let ((kb (current-kboard))
        (caught nil))
    (catch 'm2-tag
      (with-kboard kb
        (lambda () (throw 'm2-tag (setq caught 'thrown)))))
    (should (eq caught 'thrown))
    (should (kboardp (current-kboard)))
    (should (kboard-eq (current-kboard) kb))))

(provide 'ertest-kboard)

;;; ertest-kboard.el ends here
