;;; test-m28-imp5-f6.scm --- M28 imp-5, family 6: the tail.  Reclaim the
;;; self-sufficient forwarders; record the stay-C audit.
;;;
;;; brief.org (M28 imp-5 family 6) walks the 174 non-cell family-6
;;; shims (45 named groups + 129 singletons).  It expects the pure
;;; forwarders to be deleted and the rest to stay C because their body
;;; reads or writes raw C state.
;;;
;;; The brief's reclaim shortlist names 7 forwarders.  Four are genuine
;;; C-free forwarders and are reclaimed here:
;;;
;;;   --some-mouse-moved                -> (emacs read-key-sequence) some-mouse-moved
;;;   --record-recent-keys-cmd-pseudo-event
;;;                                     -> (emacs recent-keys) record-cmd-pseudo-event!
;;;   --coords-in-menu-bar-window       -> (emacs lispy-position) coords-in-menu-bar-window?
;;;   --line-number-mode-hscroll        -> (emacs lispy-position) line-number-mode-hscroll?
;;;
;;; Three named in the shortlist are NOT recoverable and stay C.  Their
;;; C bodies read C file-statics or have live C callers:
;;;
;;;   --adjust-point-for-property-cl1   reads the C file-statics
;;;                                     last_point_position + cl1_prev_modiff;
;;;                                     last_point_position has no Scheme source.
;;;   --this-single-command-key-start   called from C
;;;                                     (--rc-input-method-call-and-handle,
;;;                                     src/keyboard.c) as Fc_this_...
;;;   --set-this-single-command-key-start
;;;                                     called from C (keyboard.c) as Fc_set_this_...
;;;
;;; Procedure-step-1 grep ('Fc_NAME' src/) is what surfaces the three C
;;; callers; the brief's shortlist missed them.
;;;
;;; This corpus pins both sides of the decision:
;;;
;;;   - the 4 reclaimed DEFUNs read back as nil (C subr gone);
;;;   - the 4 target procedures resolve;
;;;   - the repointed modules load and no longer bind the %--... alias;
;;;   - a sample of the retained family-6 shims still register.
;;;
;;; Same harness as test-m28-imp5-f5.scm: Sourced by the .el wrapper via
;;; eval-scheme; accumulates (NAME STATUS) pairs into test-results.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (%sym name)
  (symbol-function name))

;;; --- 1. The four reclaimed DEFUNs are gone ----------------------------
;;; A removed C DEFUN stops being registered, so symbol-function is nil
;;; (mirrors test-m28-imp5-f4 / -f5 §1).
(define %reclaimed
  '("--some-mouse-moved"
    "--record-recent-keys-cmd-pseudo-event"
    "--coords-in-menu-bar-window"
    "--line-number-mode-hscroll"))

(for-each
 (lambda (name)
   (report (string-append "imp5/f6/no-defun/" name)
           (if (eq? (%sym (intern name)) #nil)
               'PASS
               (list 'FAIL 'still-bound name))))
 %reclaimed)

;;; --- 2. The four target procedures resolve ----------------------------
;;; Each reclaimed forwarder's Scheme target must exist in its module.
(define (target-resolves? mod-name sym)
  (let ((m (false-if-exception (resolve-module mod-name #:ensure #t))))
    (and m (procedure? (module-ref m sym)))))

(define %targets
  '(((emacs read-key-sequence) some-mouse-moved)
    ((emacs recent-keys)      record-cmd-pseudo-event!)
    ((emacs lispy-position)   coords-in-menu-bar-window?)
    ((emacs lispy-position)   line-number-mode-hscroll?)))

(for-each
 (lambda (spec)
   (let ((mod (car spec)) (sym (cadr spec)))
     (report (string-append "imp5/f6/target/" (symbol->string sym))
             (if (target-resolves? mod sym)
                 'PASS
                 (list 'FAIL 'unresolved mod sym)))))
 %targets)

;;; --- 3. The repointed modules load, and their %--... alias is gone ----
;;; Each module must load and must NOT still define the lazy alias that
;;; pointed at the deleted DEFUN.
(define %alias-absent
  '(((emacs kbd-buffer)      %--some-mouse-moved)
    ((emacs help-echo)       %--some-mouse-moved)
    ((emacs command-loop)    %--record-recent-keys-cmd-pseudo-event)
    ((emacs lispy-event)     %--coords-in-menu-bar-window)
    ((emacs lispy-event)     %--line-number-mode-hscroll)))

(for-each
 (lambda (spec)
   (let* ((mod-name (car spec)) (alias (cadr spec))
          (m (false-if-exception (resolve-module mod-name #:ensure #t)))
          (label (string-append "imp5/f6/module/"
                                (string-join
                                 (map symbol->string mod-name) " ")
                                "/"
                                (symbol->string alias))))
     (report label
             (cond ((not m) (list 'FAIL 'not-loadable mod-name))
                   ((module-variable m alias) (list 'FAIL 'still-bound alias))
                   (else 'PASS)))))
 %alias-absent)

;;; --- 4. A sample of the retained family-6 shims still register --------
;;; The rest of family 6 stays C: it reads/writes raw C state (C globals,
;;; C buffers, C tables) so the shim cannot move.  A stay-C DEFUN stays
;;; registered, so symbol-function is non-nil.  The three shortlist
;;; exceptions (C callers / C-static reads) are in this list too.
(define %stay-c
  '("--buffer-beg"
    "--buffer-end"
    "--this-command-keys"
    "--this-command-key-count"
    "--minibuf-level"
    "--total-keys"
    "--recent-keys-index"
    "--lossage-limit"
    "--raw-keybuf-count"
    "--double-click-count"
    "--set-double-click-count"
    "--recent-keys-index-set!"
    "--total-keys-set!"
    "--composition-adjust-point"
    "--display-prop-intangible-p"
    "--requeued-events-pending-p"
    "--process-special-events"
    "--input-blocked-p"
    "--lispy-function-keys"
    "--iso-lispy-function-keys"
    "--user-signal-list"
    "--user-signal-pending"
    ;; Shortlist exceptions that stay C.
    "--adjust-point-for-property-cl1"
    "--this-single-command-key-start"
    "--set-this-single-command-key-start"
    ;; Ambiguous companions decided here (brief.org §"Cell-accessor
    ;; exclusion") — raw C setters, stay C.
    "--set-read-key-sequence-remapped"
    "--set-kboard-kbd-queue-has-data"))

(for-each
 (lambda (name)
   (let ((sym (intern name)))
     (report (string-append "imp5/f6/stay-c/" name)
             (if (not (eq? (%sym sym) #nil))
                 'PASS
                 (list 'FAIL 'missing sym)))))
 %stay-c)
