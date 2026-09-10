;;; test-m28-imp5.scm --- M28 imp-5, family 2: reclaim the
;;; --ie-kind-from-name double-hop.
;;;
;;; brief.org (M28 imp-5 family 2) reclaims exactly one shim from the
;;; 20-shim --ie- input-event family:
;;;
;;;   --ie-kind-from-name  -> (emacs lispy-position) ie-kind-from-name
;;;
;;; The C DEFUN was a thin double-hop (scm_c_public_ref + SCM_CALL_1
;;; into ie-kind-from-name), so the Scheme callers now call the port
;;; directly and the DEFUN is deleted.
;;;
;;; The other 19 --ie- shims and the 4 --set-ie- write companions stay
;;; C this commit (opaque C ring; see docs/kb.org "M28 imp-5 family-2
;;; --ie-= decision audit").  This corpus pins both sides of that
;;; decision:
;;;
;;;   - the deleted DEFUN reads back as nil (C subr gone);
;;;   - the (emacs lispy-position) port the callers now use is present
;;;     and returns the captured event_kind integers;
;;;   - the 19 --ie- accessors and the 4 --set-ie- companions still
;;;     register (stay-C);
;;;   - (emacs lispy-event) and (emacs kbd-buffer) no longer define the
;;;     %--ie-kind-from-name lazy alias; kbd-buffer instead reaches the
;;;     port through the lazy %ie-kind-from-name module-ref, and its
;;;     event-kind constants match the port.
;;;
;;; Same harness as test-m28-imp1.scm: Sourced by the .el wrapper via
;;; eval-scheme; accumulates (NAME STATUS) pairs into test-results.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))
(use-modules (emacs lispy-position))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (%sym name)
  (symbol-function name))

;;; --- 1. The --ie-kind-from-name DEFUN is gone -----------------------
;;; A removed C DEFUN stops being registered, so symbol-function is nil
;;; (mirrors test-m28-imp1.scm §1).
(report "imp5/f2/no-defun/--ie-kind-from-name"
        (if (eq? (%sym '--ie-kind-from-name) #nil)
            'PASS
            (list 'FAIL 'still-bound '--ie-kind-from-name)))

;;; --- 2. The port the callers now use still resolves ----------------
;;; (emacs lispy-position) ie-kind-from-name must remain exported and
;;; return the same integers the retired C body did (captured values,
;;; see test-m19-kind.scm).  A representative slice, not the full table
;;; (test-m19-kind.scm already covers the whole mapping).
(define lp (resolve-module '(emacs lispy-position) #:ensure #t))
(report "imp5/f2/port/ie-kind-from-name-present"
        (if (module-variable lp 'ie-kind-from-name) 'PASS 'FAIL))

(for-each
 (lambda (entry)
   (let ((sym (car entry)) (want (cdr entry)))
     (report (string-append "imp5/f2/port/" (symbol->string sym))
             (let ((got (ie-kind-from-name sym)))
               (if (eqv? want got)
                   'PASS
                   (list 'FAIL 'expected want 'got got))))))
 '((dbus-event . 27)
   (no-event . 0)
   (ascii-keystroke . 1)
   (user-signal-event . 18)
   (help-echo . 19)
   (selection-request-event . 10)))

;; Unknown symbol resolves to -1 (same contract as the retired C body).
(report "imp5/f2/port/unknown->-1"
        (if (eqv? -1 (ie-kind-from-name 'not-a-real-event-kind))
            'PASS 'FAIL))

;;; --- 3. The 19 --ie- accessors stay C (register) -------------------
(for-each
 (lambda (name)
   (let ((sym (intern name)))
     (report (string-append "imp5/f2/stay-c/" name)
             (if (not (eq? (%sym sym) #nil))
                 'PASS
                 (list 'FAIL 'missing sym)))))
 '("--ie-kind" "--ie-code" "--ie-modifiers" "--ie-part" "--ie-x"
   "--ie-y" "--ie-frame-or-window" "--ie-arg" "--ie-device"
   "--ie-timestamp" "--ie-clear" "--ie-copy" "--ie-kind-alist"
   "--ie-kboard" "--ie-test-event" "--ie-help-event"
   "--ie-test-hold-quit" "--ie-user-signal-event"
   "--ie-ascii-keystroke-event"))

;;; --- 4. The 4 --set-ie- write companions stay C (register) ---------
(for-each
 (lambda (name)
   (let ((sym (intern name)))
     (report (string-append "imp5/f2/stay-c/" name)
             (if (not (eq? (%sym sym) #nil))
                 'PASS
                 (list 'FAIL 'missing sym)))))
 '("--set-ie-modifiers" "--set-ie-arg" "--set-ie-code"
   "--set-ie-frame-or-window"))

;;; --- 5. (emacs lispy-event): the %--ie-kind-from-name alias is gone -
;;; lispy-event.scm dropped the defelisp and calls the imported port
;;; directly; a kept C accessor (%--ie-kind) pins the module still loads.
(define lev (resolve-module '(emacs lispy-event) #:ensure #t))
(if lev
    (begin
      (report "imp5/f2/event/no-%--ie-kind-from-name"
              (if (not (module-variable lev '%--ie-kind-from-name))
                  'PASS
                  (list 'FAIL 'still-defined '%--ie-kind-from-name)))
      (report "imp5/f2/event/keeps-%--ie-kind"
              (if (module-variable lev '%--ie-kind)
                  'PASS
                  (list 'FAIL 'missing '%--ie-kind))))
    (report "imp5/f2/event/loadable" 'FAIL))

;;; --- 6. (emacs kbd-buffer): lazy module-ref replaced the defelisp ---
;;; kbd-buffer.scm replaced the defelisp with a lazy %ie-kind-from-name
;;; module-ref; the old alias must be gone and the new ref must resolve.
(define kb (resolve-module '(emacs kbd-buffer) #:ensure #t))
(if kb
    (begin
      (report "imp5/f2/kbd-buffer/no-%--ie-kind-from-name"
              (if (not (module-variable kb '%--ie-kind-from-name))
                  'PASS
                  (list 'FAIL 'still-defined '%--ie-kind-from-name)))
      (report "imp5/f2/kbd-buffer/has-%ie-kind-from-name"
              (if (module-variable kb '%ie-kind-from-name)
                  'PASS
                  (list 'FAIL 'missing '%ie-kind-from-name)))
      ;; The constants now computed through the port must equal the port.
      (for-each
       (lambda (entry)
         (let* ((const-name (car entry))
                (sym (cdr entry))
                (const (module-ref kb const-name))
                (want (ie-kind-from-name sym)))
           (report (string-append "imp5/f2/kbd-buffer/const-" (symbol->string sym))
                   (if (eqv? want const)
                       'PASS
                       (list 'FAIL 'expected want 'got const)))))
       '((SELECTION-REQUEST-EVENT . selection-request-event)
         (NO-EVENT . no-event)
         (ASCII-KEYSTROKE-EVENT . ascii-keystroke)
         (NON-ASCII-KEYSTROKE-EVENT . non-ascii-keystroke))))
    (report "imp5/f2/kbd-buffer/loadable" 'FAIL))
