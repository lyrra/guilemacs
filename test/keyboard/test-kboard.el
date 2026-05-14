;;; test-kboard.el --- M2 SRFI-64 suite for (emacs kboard)

;; Same coverage as ertest-kboard.el, transcribed for the
;; test-framework.el / SRFI-64 harness.  Keep in sync.

(test-begin "kboard")

;;;; predicate + identity

(test-assert "kboardp/positive"     (kboardp (current-kboard)))
(test-assert "kboardp/neg-symbol"   (not (kboardp 'not-a-kboard)))
(test-assert "kboardp/neg-fixnum"   (not (kboardp 42)))
(test-assert "kboardp/neg-nil"      (not (kboardp nil)))
(test-assert "kboardp/neg-string"   (not (kboardp "string")))

(test-assert "kboard-eq/same-pointer"
             (kboard-eq (current-kboard) (current-kboard)))

;;;; accessor round-trips

(let* ((kb (current-kboard))
       (orig (kboard-last-command kb)))
  (set-kboard-last-command kb 'sentinel-cmd)
  (test-eq "accessor/last-command" 'sentinel-cmd (kboard-last-command kb))
  (set-kboard-last-command kb orig))

(let* ((kb (current-kboard))
       (orig (kboard-echo-string kb)))
  (set-kboard-echo-string kb "C-x C-")
  (test-equal "accessor/echo-string" "C-x C-" (kboard-echo-string kb))
  (set-kboard-echo-string kb orig))

(let* ((kb (current-kboard))
       (orig (kboard-window-system kb)))
  (set-kboard-window-system kb 'fake-win-sys)
  (test-eq "accessor/window-system" 'fake-win-sys (kboard-window-system kb))
  (set-kboard-window-system kb orig))

;;;; current-kboard / set-current-kboard

(test-assert "current-kboard/is-kboard" (kboardp (current-kboard)))

(let ((kb (current-kboard)))
  (set-current-kboard kb)
  (test-assert "set-current-kboard/round-trip"
               (kboard-eq (current-kboard) kb)))

;;;; with-kboard

(test-eq "with-kboard/calls-thunk"
         'thunk-ran
         (with-kboard (current-kboard) (lambda () 'thunk-ran)))

(let ((kb (current-kboard))
      (caught nil))
  (catch 'm2-tag
    (with-kboard kb
      (lambda () (throw 'm2-tag (setq caught 'thrown)))))
  (test-eq "with-kboard/throw-caught"  'thrown caught)
  (test-assert "with-kboard/restored-after-throw"
               (kboard-eq (current-kboard) kb)))

(test-end)
