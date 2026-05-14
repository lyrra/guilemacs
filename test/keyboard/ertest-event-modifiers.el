;;; ertest-event-modifiers.el --- M1 ERT suite for (emacs event-modifiers)

;; M1 gating tests for the keyboard.c → Guile port.  Exercises the
;; C entry points that route through mod/emacs/event-modifiers.scm
;; when GUILEMACS_KB_M1=1: event-convert-list, parse-modifiers (via
;; internal-event-symbol-parse-modifiers), reorder-modifiers (via
;; define-key/lookup-key), make-ctrl-char (via event-convert-list),
;; and parse-solitary-modifier (via event-convert-list element).
;;
;; See docs/keyboard.org §"M1 — Modifier parsing".

(require 'ert)

;;;; event-convert-list — character base

(ert-deftest m1-event-convert-list/plain-char ()
  (should (equal (event-convert-list '(?a)) ?a)))

(ert-deftest m1-event-convert-list/symbol-as-char ()
  ;; A single-char symbol resolves to the character code.
  (should (equal (event-convert-list '(a)) ?a)))

(ert-deftest m1-event-convert-list/shift-lowercase-uppercases ()
  ;; (shift a) → A; shift bit is cleared.
  (should (equal (event-convert-list '(shift a)) ?A)))

(ert-deftest m1-event-convert-list/control-a ()
  (should (equal (event-convert-list '(control a)) ?\C-a)))

(ert-deftest m1-event-convert-list/single-letter-modifier-names ()
  ;; Single-letter modifier-name parsing in parse-solitary-modifier.
  (should (equal (event-convert-list '(C M a)) (event-convert-list '(control meta a))))
  (should (equal (event-convert-list '(C M S a))
                 (event-convert-list '(control meta shift a)))))

(ert-deftest m1-event-convert-list/control-meta-a ()
  ;; meta-modifier | (control-modifier folded into make-ctrl-char ?a = 1)
  ;; = 0x08000000 | 1 = 134217729
  (should (= (event-convert-list '(control meta a)) 134217729)))

(ert-deftest m1-event-convert-list/super-symbol-base ()
  (should (equal (event-convert-list '(super f1)) 's-f1)))

(ert-deftest m1-event-convert-list/hyper-super-symbol ()
  (should (equal (event-convert-list '(hyper super f1)) 'H-s-f1)))

(ert-deftest m1-event-convert-list/modifier-order-canonical ()
  ;; Multiple input orderings must produce the same canonical symbol.
  (should (eq (event-convert-list '(control meta f1))
              (event-convert-list '(meta control f1))))
  (should (eq (event-convert-list '(C M S f1))
              (event-convert-list '(M C S f1)))))

;;;; internal-event-symbol-parse-modifiers

(ert-deftest m1-parse-modifiers/no-modifiers ()
  ;; Lispier representation: (BASE . MODIFIER-LIST).  An unmodified
  ;; symbol has an empty modifier list.
  (should (equal (internal-event-symbol-parse-modifiers 'f1) '(f1))))

(ert-deftest m1-parse-modifiers/control-meta ()
  ;; Modifier list is highest-bit-first: meta(27), control(26).
  (should (equal (internal-event-symbol-parse-modifiers 'C-M-a)
                 '(a meta control))))

(ert-deftest m1-parse-modifiers/cache-stable-identity ()
  ;; Cache returns identical cons across calls (eq, not just equal).
  (let ((p1 (internal-event-symbol-parse-modifiers 'C-M-x))
        (p2 (internal-event-symbol-parse-modifiers 'C-M-x)))
    (should (eq p1 p2))))

;;;; reorder-modifiers (exercised via define-key + lookup-key on symbol keys)

(ert-deftest m1-reorder-modifiers/canonical-via-define-key ()
  ;; define-key passes the key through reorder_modifiers so that
  ;; C-M-foo and M-C-foo bind the same slot.  We verify by storing
  ;; under one ordering and reading under the other.
  (let ((m (make-sparse-keymap)))
    (define-key m [C-M-f1] 'cmd1)
    (should (eq (lookup-key m [M-C-f1]) 'cmd1))
    (define-key m [M-C-f1] 'cmd2)
    (should (eq (lookup-key m [C-M-f1]) 'cmd2))))

;;;; make-ctrl-char (exercised via (control N) for various N)

(ert-deftest m1-make-ctrl-char/ascii-lowercase ()
  ;; (control a) → 1 (C-a)
  (should (= (event-convert-list '(control a)) 1)))

(ert-deftest m1-make-ctrl-char/ascii-uppercase-keeps-shift ()
  ;; (control A) — upper-case letters get the shift bit folded in by
  ;; make_ctrl_char: result is 1 | shift-modifier = 0x02000001.
  (should (= (event-convert-list '(control A)) #x02000001)))

(ert-deftest m1-make-ctrl-char/space ()
  ;; (control ? ) — space (0x20) is in the printable region, so
  ;; make_ctrl_char ORs in ctrl-modifier rather than collapsing: 0x04000020.
  (should (= (event-convert-list '(control ? )) #x04000020)))

(ert-deftest m1-make-ctrl-char/non-ascii ()
  ;; For non-ASCII chars, ctrl just ORs the modifier bit.
  (let* ((non-ascii ?å)
         (r (event-convert-list (list 'control non-ascii))))
    (should (eq (logand r non-ascii) non-ascii))
    ;; ctrl bit set
    (should (/= 0 (logand r ?\C-\ )))))

;;;; parse-solitary-modifier coverage (via event-convert-list element names)

(ert-deftest m1-solitary-modifier/full-names ()
  ;; All long modifier names recognized.
  (dolist (name '(alt control ctrl hyper meta shift super))
    (should (event-convert-list (list name 'f1)))))

(ert-deftest m1-solitary-modifier/single-letters ()
  ;; Single-letter modifier names — note A/C/H/M/S/s map to alt,
  ;; control, hyper, meta, shift, super respectively.
  (should (eq (event-convert-list '(A f1)) 'A-f1))
  (should (eq (event-convert-list '(C f1)) 'C-f1))
  (should (eq (event-convert-list '(H f1)) 'H-f1))
  (should (eq (event-convert-list '(M f1)) 'M-f1))
  (should (eq (event-convert-list '(S f1)) 'S-f1))
  (should (eq (event-convert-list '(s f1)) 's-f1)))

;;;; modifier-bit constants stable

(ert-deftest m1-modifier-bits-stable ()
  ;; Pin the bit positions by exercising event-convert-list output bits.
  ;; Note: (control a) folds ctrl into the ctrl-char encoding (no ctrl
  ;; bit set in result); (shift a) collapses to ?A (no shift bit).
  (should (= (logand (event-convert-list '(meta a))    #x08000000) #x08000000))
  (should (= (logand (event-convert-list '(control a)) #x04000000) 0))           ; folded
  (should (= (logand (event-convert-list '(shift a))   #x02000000) 0))           ; folded
  (should (= (logand (event-convert-list '(hyper a))   #x01000000) #x01000000))
  (should (= (logand (event-convert-list '(super a))   #x00800000) #x00800000))
  (should (= (logand (event-convert-list '(alt a))     #x00400000) #x00400000)))

(provide 'ertest-event-modifiers)

;;; ertest-event-modifiers.el ends here
