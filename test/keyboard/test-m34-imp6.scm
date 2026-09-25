;;; test-m34-imp6.scm --- M34 imp-6: the xdisp.c part-2 kboard + name
;;;                       readers.
;;;
;;; brief.org (M34 imp-6) ports the decision logic of the five live
;;; src/xdisp.c part-2 call sites into the module (emacs xdisp): the two
;;; push_kboard callers (S1 display_mode_line, S3 Fformat_mode_line),
;;; the two pop_kboard callers (S2, S4), and the three
;;; Voverriding_local_map_menu_flag readers (S5 update_menu_bar,
;;; update_tab_bar, update_tool_bar).  src/xdisp.c now calls three new
;;; static dispatchers; push_kboard and pop_kboard keep their C
;;; definitions at this imp (they are the (emacs single-kboard)
;;; dispatchers); imp-7 later retired the push side.  The
;;; overriding-local-map-menu-flag DEFVAR_LISP stays C; no stub retires
;;; at this imp and no keyboard.c line changes.  See docs/kb.org ** M34.
;;;
;;; Runtime checks cover the six exported procedures, push/pop on the
;;; live current kboard smob, and the S5 reader's nil and non-nil values.
;;; Every cell binding is saved and restored, including a previously
;;; void cell (kb shared-harness-cross-corpus-state-leak).
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m34-imp6.el.

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (safe thunk)
  (catch #t
    (lambda () (cons 'ok (thunk)))
    (lambda (key . args) (cons 'error (cons key args)))))

;;; --- 0. The repo root must be known --------------------------------
;;; --- 1. The module loads and exports its procedures ----------------
(use-modules (emacs xdisp))

(define xdisp-mod (resolve-module '(emacs xdisp)))

(define (exported? mod name)
  (let ((p (module-ref mod name)))
    (and (procedure? p) #t)))

;; The six procedures: three imp-5 names plus three imp-6 names.
(for-each
 (lambda (name)
   (check (string-append "m34/imp6/export/" (symbol->string name)) #t
          (exported? xdisp-mod name)))
 '(xdisp-run-activate-menubar-hook!
   xdisp-run-menu-bar-update-hook!
   xdisp-run-window-scroll-functions!
   xdisp-push-kboard!
   xdisp-pop-kboard!
   xdisp-overriding-local-map-menu-flag-p))

;;; --- 2. Runtime: the push/pop pair --------------------------------
;;; Bind a kboard smob from the live C state.  current-kboard returns a
;;; KBOARD smob (M2).  push then pop is net zero on the
;;; (emacs single-kboard) kboard-stack, so no state leaks.
(define (%c name) (symbol-function name))
(define %void (list 'void))

(define (cell-read name)
  (if ((%c 'boundp) name) (symbol-value name) %void))

(define (current-kboard-smob)
  ((%c 'current-kboard)))

(let ((r (safe current-kboard-smob)))
  (if (and (pair? r) (eq? (car r) 'ok))
      (let ((kb (cdr r)))
        (check "m34/imp6/runtime/push-no-error" 'ok
               (car (safe (lambda () (xdisp-push-kboard! kb)))))
        ;; Restore the stack in every case: if push consed and then
        ;; failed, pop still removes the one entry it added.
        (check "m34/imp6/runtime/pop-no-error" 'ok
               (car (safe (lambda () (xdisp-pop-kboard!))))))
      (report "m34/imp6/runtime/current-kboard"
              (cons 'FAIL (format "current-kboard failed: %S" r)))))

;;; --- 3. Runtime: the S5 cell reader --------------------------------
;;; Read the cell with boundp, and restore a previously-void cell with
;;; makunbound (the imp-5 F4 fix), so no cell state leaks.
(let ((old (cell-read 'overriding-local-map-menu-flag)))
  ;; nil arm: an elisp nil cell.
  (set-symbol-value! 'overriding-local-map-menu-flag #nil)
  (check "m34/imp6/runtime/s5-nil" #nil
         (xdisp-overriding-local-map-menu-flag-p))
  ;; non-nil arm: a non-nil cell yields elisp t.  In guilemacs Qt is
  ;; SCM_BOOL_T, i.e. the Scheme #t (src/lread.c:2878), so the reader
  ;; must return #t exactly -- not merely some non-#nil value (cr.org
  ;; F3).  This pins the brief.org 5.4 Qt/Qnil contract.
  (set-symbol-value! 'overriding-local-map-menu-flag #t)
  (check "m34/imp6/runtime/s5-t" #t
         (xdisp-overriding-local-map-menu-flag-p))
  ;; Any other non-nil value is normalized to elisp t (brief.org 5.5).
  (set-symbol-value! 'overriding-local-map-menu-flag 'some-symbol)
  (check "m34/imp6/runtime/s5-non-nil-normalized" #t
         (xdisp-overriding-local-map-menu-flag-p))
  ;; Restore: a previously-void cell returns to void, not to elisp nil.
  (if (eq? old %void)
      ((%c 'makunbound) 'overriding-local-map-menu-flag)
      (set-symbol-value! 'overriding-local-map-menu-flag old))
  (check "m34/imp6/runtime/s5-restored" old
         (cell-read 'overriding-local-map-menu-flag)))
