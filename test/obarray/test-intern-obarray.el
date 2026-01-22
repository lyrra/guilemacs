;;; test-intern-obarray.el --- Test intern, obarray, and mapatoms -*- lexical-binding: t; -*-
;; Tests for symbol interning, obarrays, and mapatoms functionality.
;; These are critical for vanilla Guile compatibility in guilemacs.
;;  - Basic intern (returns symbol, same string returns eq symbol)
;;  - Canonical nil and t handling
;;  - intern-soft (finds existing, accepts symbol argument)
;;  - Custom obarrays (obarray-make, intern into custom, isolation)
;;  - mapatoms (iterates symbols, finds interned symbols, custom obarray count)
;;  - mapatoms finding symbols from loaded files (backup-inhibited, backup-buffer)
;;  - String wrapper handling (match-string results, buffer-substring)
;;  - Edge cases (empty string, keywords, unicode, special chars)
;;  - boundp/fboundp behavior after intern

(test-begin "intern-obarray")

;;; ============================================================
;;; Basic intern tests
;;; ============================================================

;; Test: intern returns a symbol
(test-assert "intern/returns-symbol"
             (symbolp (intern "test-symbol-123")))

;; Test: intern same string returns eq symbol
(test-eq "intern/same-string-eq"
         (intern "test-symbol-456")
         (intern "test-symbol-456"))

;; Test: intern "nil" returns canonical nil
(test-eq "intern/nil-canonical"
         nil
         (intern "nil"))

;; Test: intern "t" returns canonical t
(test-eq "intern/t-canonical"
         t
         (intern "t"))

;; Test: symbol-name of interned symbol
(test-equal "intern/symbol-name"
            "my-test-symbol"
            (symbol-name (intern "my-test-symbol")))

;;; ============================================================
;;; intern-soft tests
;;; ============================================================

;; Test: intern-soft finds existing symbol
(let ((sym (intern "existing-test-sym")))
  (test-eq "intern-soft/finds-existing"
           sym
           (intern-soft "existing-test-sym")))

;; Test: intern-soft with symbol argument
(let ((sym (intern "symbol-arg-test")))
  (test-eq "intern-soft/symbol-argument"
           sym
           (intern-soft sym)))

;; Test: intern-soft returns nil for non-existent in custom obarray
(let ((ob (obarray-make)))
  (test-nil "intern-soft/nonexistent-custom-obarray"
            (intern-soft "definitely-not-there" ob)))

;;; ============================================================
;;; Custom obarray tests
;;; ============================================================

;; Test: obarray-make creates an obarray
(test-assert "obarray-make/creates-obarray"
             (obarrayp (obarray-make)))

;; Test: intern into custom obarray
(let ((ob (obarray-make)))
  (let ((sym (intern "custom-sym" ob)))
    (test-assert "intern/custom-obarray-returns-symbol"
                 (symbolp sym))))

;; Test: intern-soft finds symbol in custom obarray
(let ((ob (obarray-make)))
  (let ((sym (intern "findme" ob)))
    (test-eq "intern-soft/custom-obarray-finds"
             sym
             (intern-soft "findme" ob))))

;; Test: symbols in custom obarray are isolated from global
(let ((ob (obarray-make)))
  (intern "isolated-symbol" ob)
  ;; The symbol should exist in custom obarray
  (test-not-nil "intern/custom-isolated-exists"
                (intern-soft "isolated-symbol" ob)))

;;; ============================================================
;;; mapatoms tests
;;; ============================================================

;; Test: mapatoms calls function on symbols
(let ((count 0))
  (mapatoms (lambda (s) (setq count (1+ count))))
  (test-assert "mapatoms/iterates-symbols"
               (> count 1000)))  ; Should have many symbols

;; Test: mapatoms finds interned symbol
(let ((test-sym (intern "mapatoms-test-symbol-unique-12345"))
      (found nil))
  (mapatoms (lambda (s)
              (when (eq s test-sym)
                (setq found t))))
  (test-assert "mapatoms/finds-interned-symbol"
               found))

;; Test: mapatoms on custom obarray
(let ((ob (obarray-make))
      (count 0))
  (intern "sym1" ob)
  (intern "sym2" ob)
  (intern "sym3" ob)
  (mapatoms (lambda (s) (setq count (1+ count))) ob)
  (test-equal "mapatoms/custom-obarray-count"
              3
              count))

;; Test: mapatoms finds symbols from loaded files
;; (These symbols are created by Guile's reader, not Fintern)
(require 'files)
(let ((found-inhibited nil)
      (found-buffer nil))
  (mapatoms (lambda (s)
              (when (eq s 'backup-inhibited)
                (setq found-inhibited t))
              (when (eq s 'backup-buffer)
                (setq found-buffer t))))
  (test-assert "mapatoms/finds-backup-inhibited"
               found-inhibited)
  (test-assert "mapatoms/finds-backup-buffer"
               found-buffer))

;;; ============================================================
;;; String wrapper handling tests
;;; ============================================================

;; Test: intern works with match-string results (emacs-string wrappers)
(let ((result nil))
  (with-temp-buffer
    (insert "(when (foo) (error bar))")
    (goto-char (point-min))
    (when (re-search-forward "(\\([a-z]+\\)" nil t)
      (setq result (intern-soft (match-string 1)))))
  (test-eq "intern-soft/match-string-result"
           'when
           result))

;; Test: intern works with buffer-substring results
(let ((result nil))
  (with-temp-buffer
    (insert "test-buffer-sym")
    (setq result (intern (buffer-substring (point-min) (point-max)))))
  (test-eq "intern/buffer-substring-result"
           'test-buffer-sym
           result))

;; Test: multiple match-string calls work
(let ((symbols nil))
  (with-temp-buffer
    (insert "(defun my-func (arg) body)")
    (goto-char (point-min))
    (while (re-search-forward "\\b\\([a-z-]+\\)\\b" nil t)
      (push (intern-soft (match-string 1)) symbols)))
  (test-assert "intern-soft/multiple-match-strings"
               (and (memq 'defun symbols)
                    (memq 'my-func symbols)
                    (memq 'arg symbols)
                    (memq 'body symbols))))

;;; ============================================================
;;; Edge cases
;;; ============================================================

;; Test: empty string intern
(test-assert "intern/empty-string"
             (symbolp (intern "")))

;; Test: keyword symbol
(let ((kw (intern ":keyword-test")))
  (test-assert "intern/keyword-is-symbol"
               (symbolp kw))
  (test-equal "intern/keyword-name"
              ":keyword-test"
              (symbol-name kw)))

;; Test: symbol with special characters
(let ((sym (intern "test-symbol-with-dashes")))
  (test-equal "intern/special-chars"
              "test-symbol-with-dashes"
              (symbol-name sym)))

;; Test: unicode symbol name
(let ((sym (intern "λ-test")))
  (test-equal "intern/unicode-name"
              "λ-test"
              (symbol-name sym)))

;;; ============================================================
;;; Boundp/fboundp after intern
;;; ============================================================

;; Test: newly interned symbol is not bound
(let ((sym (intern "brand-new-unbound-symbol-xyz")))
  (test-nil "intern/new-symbol-not-bound"
            (boundp sym)))

;; Test: set and boundp
(let ((sym (intern "test-bound-symbol")))
  (set sym 42)
  (test-assert "intern/set-makes-bound"
               (boundp sym))
  (test-equal "intern/symbol-value-after-set"
              42
              (symbol-value sym)))

;; Test: fset and fboundp
(let ((sym (intern "test-fbound-symbol")))
  (fset sym (lambda () "test"))
  (test-assert "intern/fset-makes-fbound"
               (fboundp sym)))

(test-end)
