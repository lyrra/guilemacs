;;; test-consolidation.el --- SRFI-64 suite for the consolidation milestone

;; Same coverage as ertest-consolidation.el, transcribed for the
;; test-framework.el / SRFI-64 harness.  Keep in sync.

(test-begin "consolidation")

;;;; top-level

(test-assert "top-level/throws"
             (let ((caught 'unset))
               (catch 'top-level
                 (setq caught 'inside-catch)
                 (top-level)
                 (setq caught 'unreached))
               (eq caught 'inside-catch)))

(test-eq "top-level/returns-via-throw" nil
         (catch 'top-level (top-level) 'unreached))

;;;; set--this-command-keys — empty string

(clear-this-command-keys t)
(set--this-command-keys "")
(test-equal "set--tck/empty-string-count" 0 (--this-command-key-count))

;;;; ASCII roundtrip

(clear-this-command-keys t)
(set--this-command-keys "foo")
(test-equal "set--tck/ascii-count" 3 (--this-command-key-count))
(let ((v (--this-command-keys)))
  (test-equal "set--tck/ascii-0" ?f (aref v 0))
  (test-equal "set--tck/ascii-1" ?o (aref v 1))
  (test-equal "set--tck/ascii-2" ?o (aref v 2)))

;;;; M-x kludge: 248 → ?x | meta-modifier

(clear-this-command-keys t)
(set--this-command-keys "\xf8")
(test-equal "set--tck/kludge-count" 1 (--this-command-key-count))
(test-equal "set--tck/kludge-value"
            (logior ?x #x08000000)
            (aref (--this-command-keys) 0))

;;;; Kludge applies only to position 0

(clear-this-command-keys t)
(set--this-command-keys "x\xf8")
(test-equal "set--tck/kludge-only-first/count" 2 (--this-command-key-count))
(let ((v (--this-command-keys)))
  (test-equal "set--tck/kludge-only-first/0" ?x  (aref v 0))
  (test-equal "set--tck/kludge-only-first/1" 248 (aref v 1)))

;;;; Counter resets

(clear-this-command-keys t)
(set--this-command-keys "abc")
(test-equal "set--tck/reset-count-1"          3 (--this-command-key-count))
(test-equal "set--tck/reset-single-start-1"   0 (--this-single-command-key-start))
(set--this-command-keys "d")
(test-equal "set--tck/reset-count-2"          1 (--this-command-key-count))
(test-equal "set--tck/reset-single-start-2"   0 (--this-single-command-key-start))

;;;; Rejects non-string

(test-assert "set--tck/rejects-int"
             (condition-case nil
                 (progn (set--this-command-keys 42) nil)
               (wrong-type-argument t)))

(test-assert "set--tck/rejects-list"
             (condition-case nil
                 (progn (set--this-command-keys '(?a ?b)) nil)
               (wrong-type-argument t)))

(clear-this-command-keys t)

(test-end)
