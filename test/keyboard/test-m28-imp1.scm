;;; test-m28-imp1.scm --- M28 imp-1: reclaim the 5 residual M8/M10 shims.
;;;
;;; brief.org (M28 imp-1) reclaims 5 shims in src/keyboard.c:
;;;   3 dispatcher DEFUNs are deleted (their Scheme callers now call the
;;;   (emacs lispy-position) ports directly):
;;;     --tab-bar-enrich-position   -> tab-bar-enrich-position
;;;     --menu-bar-touch-activate   -> menu-bar-touch-activate
;;;     --mouse-click-menu-bar-intercept -> mouse-click-menu-bar-intercept
;;;   2 rc shims stay C (recorded reason in docs/kb.org):
;;;     --rc-maybe-help-form-recursive-read
;;;     --rc-input-method-call-and-handle
;;;
;;; This corpus asserts the reclaim:
;;;   - the 3 deleted subrs are no longer registered (C DEFUN gone, so
;;;     the elisp binding is gone);
;;;   - the 2 rc shims are still registered (stay-C);
;;;   - the (emacs lispy-position) ports the Scheme side now calls are
;;;     still present and re-exported;
;;;   - (emacs lispy-event) still loads and its 3 rewired handlers no
;;;     longer reference the deleted C subrs (module-variable gone),
;;;     while --menu-bar-touch-consume-p (kept, reads C statics) and the
;;;     menu_bar_touch_id accessors remain.
;;;
;;; Same harness as test-m19-shims.scm: Sourced by the .el wrapper via
;;; eval-scheme; accumulates (NAME STATUS) pairs into test-results.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (%sym name)
  (symbol-function name))

;;; --- 1. The 3 dispatcher DEFUNs are gone --------------------------
;;; A removed C DEFUN stops being registered, so symbol-function is nil
;;; (mirrors the --mlp-dispatch retirement check in test-m19-shims.scm).
(define %gone-alist
  '((retire/no-defun--tab-bar-enrich-position . --tab-bar-enrich-position)
    (retire/no-defun--menu-bar-touch-activate . --menu-bar-touch-activate)
    (retire/no-defun--mouse-click-menu-bar-intercept
     . --mouse-click-menu-bar-intercept)))
(for-each (lambda (entry)
            (let ((name (car entry)) (sym (cdr entry)))
              (report name
                      (if (eq? (%sym sym) #nil)
                          'PASS
                          (list 'FAIL 'still-bound sym)))))
          %gone-alist)

;;; --- 2. The 2 rc shims stay C (stay-C, recorded reason) -----------
(define %stay-alist
  '((stay-c/registered--rc-maybe-help-form-recursive-read
     . --rc-maybe-help-form-recursive-read)
    (stay-c/registered--rc-input-method-call-and-handle
     . --rc-input-method-call-and-handle)))
(for-each (lambda (entry)
            (let ((name (car entry)) (sym (cdr entry)))
              (report name
                      (if (not (eq? (%sym sym) #nil))
                          'PASS
                          (list 'FAIL 'missing sym)))))
          %stay-alist)

;;; --- 3. The (emacs lispy-position) ports remain ------------------
;;; The Scheme callers in (emacs lispy-event) now call these directly;
;;; they must still be exported and reachable.
(let ((mod (resolve-module '(emacs lispy-position))))
  (for-each
   (lambda (entry)
     (let ((name (car entry)) (sym (cdr entry)))
       (report name
               (if (module-variable mod sym)
                   'PASS
                   (list 'FAIL 'missing-port sym)))))
   '((port/present-tab-bar-enrich-position . tab-bar-enrich-position)
     (port/present-menu-bar-touch-activate . menu-bar-touch-activate)
     (port/present-mouse-click-menu-bar-intercept
      . mouse-click-menu-bar-intercept))))

;;; --- 4. (emacs lispy-event) rewiring -----------------------------
;;; The deleted subrs must have no lingering %--... delay/variable in
;;; (emacs lispy-event); the kept C-state accessors must remain.
(define lev (resolve-module '(emacs lispy-event)))
(if lev
    (begin
      ;; Deleted delays must be gone.
      (for-each
       (lambda (entry)
         (let ((name (car entry)) (sym (cdr entry)))
           (report name
                   (if (not (module-variable lev sym))
                       'PASS
                       (list 'FAIL 'still-defined sym)))))
       '((event/no-delay-%--tab-bar-enrich-position . %--tab-bar-enrich-position)
         (event/no-delay-%--menu-bar-touch-activate . %--menu-bar-touch-activate)
         (event/no-delay-%--mouse-click-menu-bar-intercept
          . %--mouse-click-menu-bar-intercept)))
      ;; Kept C-state accessors must remain.
      (for-each
       (lambda (entry)
         (let ((name (car entry)) (sym (cdr entry)))
           (report name
                   (if (module-variable lev sym)
                       'PASS
                       (list 'FAIL 'missing sym)))))
       '((event/stays-%--menu-bar-touch-consume-p . %--menu-bar-touch-consume-p)
         (event/stays-%--menu-bar-touch-id . %--menu-bar-touch-id)
         (event/stays-%--set-menu-bar-touch-id . %--set-menu-bar-touch-id))))
    ;; module not loadable in this context — assert fail so the reclaim
    ;; of lispy-event is not silently unverified.
    (report "event/lispy-event-loadable" 'FAIL))
