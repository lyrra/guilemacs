;;; test-event-modifiers.el --- M1 SRFI-64 suite for (emacs event-modifiers)

;; Same assertions as ertest-event-modifiers.el, transcribed for the
;; test-framework.el / SRFI-64 harness invoked by
;; test/summarize-results.sh.  Keep in sync with the ERT version.

(test-begin "event-modifiers")

;;;; event-convert-list — character base

(test-equal "ec/plain-char"            ?a (event-convert-list '(?a)))
(test-equal "ec/symbol-as-char"        ?a (event-convert-list '(a)))
(test-equal "ec/shift-lowercase"       ?A (event-convert-list '(shift a)))
(test-equal "ec/control-a"             1         (event-convert-list '(control a)))
;; meta | (C-a folded = 1) = 0x08000000 | 1
(test-equal "ec/control-meta-a"        134217729 (event-convert-list '(control meta a)))
(test-equal "ec/super-f1"              's-f1 (event-convert-list '(super f1)))
(test-equal "ec/hyper-super-f1"        'H-s-f1 (event-convert-list '(hyper super f1)))

;; Single-letter modifier names match the long names.
(test-equal "ec/single-letters-CMa"
            (event-convert-list '(control meta a))
            (event-convert-list '(C M a)))
(test-equal "ec/single-letters-CMSa"
            (event-convert-list '(control meta shift a))
            (event-convert-list '(C M S a)))

;; Canonicalization: modifier ordering doesn't matter.
(test-eq    "ec/canonical-CM-eq-MC"
            (event-convert-list '(control meta f1))
            (event-convert-list '(meta control f1)))

;;;; internal-event-symbol-parse-modifiers

(test-equal "psm/no-modifiers"
            '(f1)
            (internal-event-symbol-parse-modifiers 'f1))

(test-equal "psm/C-M-a → (a meta control)"
            '(a meta control)
            (internal-event-symbol-parse-modifiers 'C-M-a))

;; Cache returns identical cons (eq, not just equal).
(test-eq    "psm/cache-stable-identity"
            (internal-event-symbol-parse-modifiers 'C-M-x)
            (internal-event-symbol-parse-modifiers 'C-M-x))

;;;; reorder-modifiers (via define-key/lookup-key on symbol keys)

(let ((m (make-sparse-keymap)))
  (define-key m [C-M-f1] 'cmd1)
  (test-eq    "rm/canonical-CM-binds-as-MC" 'cmd1 (lookup-key m [M-C-f1]))
  (define-key m [M-C-f1] 'cmd2)
  (test-eq    "rm/canonical-overwrite"      'cmd2 (lookup-key m [C-M-f1])))

;;;; make-ctrl-char (via event-convert-list)

(test-equal "mcc/ctrl-a"     1          (event-convert-list '(control a)))
;; (control A) → 1 | shift-modifier (upper-case letter remembers shift)
(test-equal "mcc/ctrl-A"     #x02000001 (event-convert-list '(control A)))
;; (control SPC) → 0x04000020 (printable region, just ORs ctrl-modifier)
(test-equal "mcc/ctrl-space" #x04000020 (event-convert-list '(control ? )))

;;;; parse-solitary-modifier — single-letter mapping

(test-eq "psm-sl/A" 'A-f1 (event-convert-list '(A f1)))
(test-eq "psm-sl/C" 'C-f1 (event-convert-list '(C f1)))
(test-eq "psm-sl/H" 'H-f1 (event-convert-list '(H f1)))
(test-eq "psm-sl/M" 'M-f1 (event-convert-list '(M f1)))
(test-eq "psm-sl/S" 'S-f1 (event-convert-list '(S f1)))
(test-eq "psm-sl/s" 's-f1 (event-convert-list '(s f1)))

;;;; modifier bit positions stable

(test-equal "bits/meta"   #x08000000 (logand (event-convert-list '(meta a))  #x08000000))
(test-equal "bits/hyper"  #x01000000 (logand (event-convert-list '(hyper a)) #x01000000))
(test-equal "bits/super"  #x00800000 (logand (event-convert-list '(super a)) #x00800000))
(test-equal "bits/alt"    #x00400000 (logand (event-convert-list '(alt a))   #x00400000))

(test-end)
