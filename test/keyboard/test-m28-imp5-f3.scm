;;; test-m28-imp5-f3.scm --- M28 imp-5, family 3: the
;;; --frame- / --window- stay-C decision audit.
;;;
;;; brief.org (M28 imp-5 family 3) walks the 12 --frame- and 4 --window-
;;; shims plus the 1 write companion --set-frame-relative-event-pos.
;;; Every body reads or writes raw C state (a struct frame / struct
;;; window field, the Vframe_list global, a C geometry subroutine, an
;;; #ifdef HAVE_WINDOW_SYSTEM body, or a plain C subroutine), so all 16
;;; stay C and the --frame-relative-event-pos cell pair defers to M30.
;;; Zero reclaims: no C DEFUN and no Scheme caller is touched.
;;;
;;; This corpus pins that decision:
;;;
;;;   - all 17 registry names still register (symbol-function non-nil) —
;;;     the shims stay C (see docs/kb.org "M28 imp-5 family-3
;;;     --frame- / --window- decision audit");
;;;   - each Scheme caller module still defines the %--... alias it
;;;     routes through (help-echo, read-key-sequence, kbd-buffer,
;;;     lispy-position, lispy-event, gobble).
;;;
;;; Same harness as test-m28-imp5.scm: Sourced by the .el wrapper via
;;; eval-scheme; accumulates (NAME STATUS) pairs into test-results.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (%sym name)
  (symbol-function name))

;;; --- 1. All 17 --frame- / --window- / companion shims stay C ---------
;;; A stay-C DEFUN stays registered, so symbol-function is non-nil.
(define %stay-c '("--frame-set-mouse-moved!"
                  "--frame-mouse-moved-p"
                  "--frame-list-raw"
                  "--frame-focus-frame"
                  "--frame-last-mouse-device"
                  "--frame-internal-border-part"
                  "--frame-menu-bar-window"
                  "--frame-tab-bar-window"
                  "--frame-menu-bar-items"
                  "--frame-tab-bar-items"
                  "--frame-relative-event-pos"
                  "--frame-make-pointer-visible!"
                  "--window-box-left"
                  "--window-box-width"
                  "--window-frame-origin"
                  "--window-from-coordinates"
                  "--set-frame-relative-event-pos"))

(for-each
 (lambda (name)
   (let ((sym (intern name)))
     (report (string-append "imp5/f3/stay-c/" name)
             (if (not (eq? (%sym sym) #nil))
                 'PASS
                 (list 'FAIL 'missing sym)))))
 %stay-c)

;;; --- 2. Each caller module still defines its %--... routing alias ----
;;; The shims stay C, so the defelisp/delay aliases that reach them must
;;; remain.  Report the module's load state explicitly so a load failure
;;; is not a silent skip.
(define (check-module label mod-name vars)
  (let ((mod (false-if-exception (resolve-module mod-name #:ensure #t))))
    (if mod
        (begin
          (report (string-append "imp5/f3/module/" label "/loadable")
                  'PASS)
          (for-each
           (lambda (v)
             (report (string-append "imp5/f3/alias/" (symbol->string v))
                     (if (module-variable mod v)
                         'PASS
                         (list 'FAIL 'missing v))))
           vars))
        (report (string-append "imp5/f3/module/" label "/loadable")
                (list 'FAIL 'not-loadable label)))))

(check-module "help-echo"         '(emacs help-echo)        '(%--frame-set-mouse-moved!))
(check-module "read-key-sequence" '(emacs read-key-sequence) '(%frame-mouse-moved-p %frame-list-raw))
(check-module "kbd-buffer"        '(emacs kbd-buffer)        '(%--frame-focus-frame
                                                              %--frame-last-mouse-device))
(check-module "lispy-position"    '(emacs lispy-position)    '(%--frame-internal-border-part
                                                              %--window-box-left
                                                              %--window-box-width
                                                              %--window-frame-origin
                                                              %--window-from-coordinates
                                                              %--frame-menu-bar-window
                                                              %--frame-tab-bar-window
                                                              %--frame-menu-bar-items
                                                              %--frame-tab-bar-items))
(check-module "lispy-event"       '(emacs lispy-event)       '(%--frame-relative-event-pos
                                                              %--set-frame-relative-event-pos))
(check-module "gobble"            '(emacs gobble)            '(%--frame-make-pointer-visible!))
