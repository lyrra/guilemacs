;;; test-m19-fixes.scm --- regression tests for the M19 cr.org findings
;;;
;;; Covers the two defects reported in cr.org for (emacs lispy-position):
;;;   * Finding 1 — vscroll-on-right? tested `(eq? vtype 't)` where elisp
;;;     t crosses into Scheme as `#t`.  The `t` branch (use-the-frame's
;;;     vertical-scroll-bar setting) never matched, so a right-hand scroll
;;;     bar returned the wrong buffer column for ON_VERTICAL_SCROLL_BAR
;;;     clicks.  We mock the window/frame primitives so the batch build
;;;     (no real scroll bars) can still exercise the branch.
;;;   * Finding 2 — the orchestrator (ml-dispatch-text-line-margin,
;;;     ml-dispatch-fringe-scroll, ml-dispatch-window-part) routed on a
;;;     wrong window_part enum table.  We assert each part routes to the
;;;     same leaf (same posn symbol) as the known-good C --mlp-dispatch
;;;     path.
;;;
;;; Sourced by test/keyboard/test-m19-fixes.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results`.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (%sym name)
  (symbol-function name))

(define (modfn name)
  (module-ref (resolve-module '(emacs lispy-position)) name))

(define mod (resolve-module '(emacs lispy-position)))

;;; --- Finding 1: vscroll-on-right? t-branch -------------------------
;;; vscroll-on-right? resolves the window's VERTICAL-TYPE through the
;;; frame's vertical-scroll-bars parameter when the type is t (elisp t,
;;; which is `#t` in Scheme).  Mock the three primitives it touches so
;;; the batch build can exercise that branch.
(define (mock-var name proc)
  "Replace module variable NAME with a delay returning PROC.
Return the previous value for restore."
  (let ((old (module-ref mod name)))
    (module-set! mod name (delay proc))
    old))

(define (run-vscroll vtype ftype)
  "Return (vscroll-on-right? w) with mocked scroll-bar TYPE and frame
VERTICAL-SCROLL-BARS FTYPE."
  (let ((old-sb (mock-var '%--window-scroll-bars
                          (lambda (w) (list 0 0 vtype 0 0 'nil #nil))))
        (old-wf (mock-var '%--window-frame (lambda (w) 'frame)))
        (old-fp (mock-var '%--frame-parameter
                          (lambda (f key)
                            (if (eq? key 'vertical-scroll-bars) ftype #nil)))))
    (let ((res ((modfn 'vscroll-on-right?) 'w)))
      (module-set! mod '%--window-scroll-bars old-sb)
      (module-set! mod '%--window-frame old-wf)
      (module-set! mod '%--frame-parameter old-fp)
      res)))

;; t-branch with a right-hand frame scroll bar -> #t (the bug: this was #f)
(report "vscroll/t/right"
        (if (run-vscroll #t 'right) 'PASS 'FAIL))
;; t-branch with a left-hand frame scroll bar -> #f
(report "vscroll/t/left"
        (if (run-vscroll #t 'left) 'FAIL 'PASS))
;; t-branch with frame scroll-bar side nil -> #f
(report "vscroll/t/nil"
        (if (run-vscroll #t #nil) 'FAIL 'PASS))
;; direct 'right branch (no frame lookup) -> #t
(report "vscroll/right/direct"
        (if (run-vscroll 'right 'right) 'PASS 'FAIL))
;; direct nil type -> #f
(report "vscroll/nil/type"
        (if (run-vscroll #nil 'right) 'FAIL 'PASS))

;;; --- Finding 2: orchestrator routing -------------------------------
;;; For each representative part, the orchestrator must produce the same
;;; posn symbol as the known-good C --mlp-dispatch leaf for that part.
(define (c-posn w part mx my)
  "Posn symbol from the C --mlp-dispatch path for PART."
  (car (cond
         ((= part 3) ((%sym '--mlp-dispatch) 5 w 3 mx my #nil #nil))  ; vertical border
         ((= part 5) ((%sym '--mlp-dispatch) 6 w 5 mx my #nil #nil))  ; tab line
         ((= part 6) ((%sym '--mlp-dispatch) 4 w #t mx my #nil #nil)) ; left fringe
         ((= part 7) ((%sym '--mlp-dispatch) 4 w #f mx my #nil #nil)) ; right fringe
         ((= part 8) ((%sym '--mlp-dispatch) 7 w 8 mx my #nil #nil))  ; left margin
         ((= part 9) ((%sym '--mlp-dispatch) 7 w 9 mx my #nil #nil))  ; right margin
         (else #f))))

(define (orch-posn w part mx my)
  "Posn symbol produced by the Scheme orchestrator for PART."
  (call-with-values
      (lambda () ((modfn 'ml-dispatch-window-part) w part mx my))
    (lambda (posn . rest) posn)))

(let* ((w ((%sym 'selected-window)))
       (f ((%sym 'selected-frame)))
       (mx 10) (my 5))
  (for-each
   (lambda (part)
     (let ((expected (c-posn w part mx my))
           (got (orch-posn w part mx my)))
       (report (string-append "route/part" (number->string part))
               (if (equal? expected got)
                   'PASS
                   (list 'FAIL 'expected expected 'got got)))))
   '(3 5 6 7 8 9)))
