;;; frame.scm --- M34 imp-2: the frame.c swallow and single-kboard callers
;;;               ((emacs frame))
;;;
;;; Moves the *decision* logic of the two live src/frame.c call sites of
;;; keyboard extern stubs into Scheme.  The *mechanism* stays C: the
;;; if (kb != NULL) test, the FOR_EACH_FRAME walk, the
;;; kb == FRAME_KBOARD (XFRAME (frame1)) comparison, the
;;; #ifdef HAVE_PGTK / FRAME_PGTK_P guard, the pgtk_clear_frame_selections
;;; call, and the make_kboard_smob wrap of the struct kboard * argument.
;;; See brief.org 3, 5.
;;;
;;; Two exported procedures:
;;;
;;;   frame-swallow-events!               -- site 1: swallow_events (false).
;;;   frame-maybe-not-single-kboard-state! -- site 2: the NILP
;;;                                          (frame_on_same_kboard) test.
;;;
;;; Note: site 1 is inside #ifdef HAVE_PGTK, which is undefined in this
;;; build (src/config.h), so its port is source-level only.  brief.org 3.
;;;
;;; Conventions (identical to M9-M34, cf. mod/emacs/display.scm):
;;; cross-module targets are resolved lazily with delay + module-ref; #nil
;;; is elisp nil; no defelisp (both targets are Scheme procedures); no
;;; module-level mutable state.

(define-module (emacs frame)
  #:declarative? #t
  #:export (frame-swallow-events!
            frame-maybe-not-single-kboard-state!))

;; (emacs kbd-buffer) holds the swallow_events port, (emacs single-kboard)
;; the single-kboard policy.  Resolve each lazily, so the module does not
;; eagerly import them (see the (emacs frame) entry in docs: eager
;; #:use-module drags the import chain).  See brief.org 5.1.
(define %kbd-buffer-swallow-events!
  (delay (module-ref (resolve-module '(emacs kbd-buffer))
                     'kbd-buffer-swallow-events!)))
(define %not-single-kboard-state
  (delay (module-ref (resolve-module '(emacs single-kboard))
                     'not-single-kboard-state)))

;;; --- Helpers -------------------------------------------------------
;;; Each module carries its own copy.  See mod/emacs/xterm.scm:74.
;;; Only %nilp is needed here: site 2 is a NILP test on a value that is
;;; only Qnil or a frame, so the wider truthy? test has no caller
;;; (cr.org 5.2, 6.1).  The other modules carry truthy? because they
;;; normalize a t/nil result from a C reference; this module does not.
(define (%nilp x) (eq? x #nil))

;;; --- frame-swallow-events! -----------------------------------------
;;; Port of the site-1 call in Fdelete_frame (src/frame.c, under #ifdef
;;; HAVE_PGTK): swallow_events (false).  The C passes false, which is
;;; elisp nil (#nil), not #f.  See brief.org 5.1 and
;;; cr-m34-imp1-response.org F5(a).
(define (frame-swallow-events!)
  ((force %kbd-buffer-swallow-events!) #nil))

;;; --- frame-maybe-not-single-kboard-state! --------------------------
;;; Port of the site-2 decision in Fdelete_frame (src/frame.c): the C test
;;; if (NILP (frame_on_same_kboard)) not_single_kboard_state (kb);.
;;; KBOARD is the kboard smob; FRAME-ON-SAME-KBOARD is a Lisp object.
;;; When it is nil, call (emacs single-kboard) not-single-kboard-state on
;;; KBOARD; else do nothing.  Return nothing.  See brief.org 5.1.
(define (frame-maybe-not-single-kboard-state! kboard frame-on-same-kboard)
  (when (%nilp frame-on-same-kboard)
    ((force %not-single-kboard-state) kboard)))
