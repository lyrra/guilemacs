;;; xdisp.scm --- M34 imp-5/-6: the xdisp.c hook, kboard and name callers
;;;                ((emacs xdisp))
;;;
;;; Moves the *decision* logic of live src/xdisp.c call sites into
;;; Scheme.  The *mechanism* stays C: the if (!hooks_run) block and the
;;; hooks_run = true write in update_menu_bar, the
;;; if (!NILP (Vwindow_scroll_functions)) guard in
;;; run_window_scroll_functions, the make_fixnum (CHARPOS (startp))
;;; wrap, the SET_TEXT_POS_FROM_MARKER call, the set_buffer_internal
;;; call, the push_kboard / pop_kboard unwind frame, the dynwind blocks,
;;; and the NILP test of the S5 reader.  See brief.org 3, 4, 6.
;;;
;;; Six exported procedures.
;;;
;;; imp-5 (the part-1 hook callers):
;;;
;;;   xdisp-run-activate-menubar-hook!    -- site S1 (src/xdisp.c:14279):
;;;                                          the Lucid hook run.
;;;   xdisp-run-menu-bar-update-hook!     -- site S2 (:14283): the
;;;                                          menu-bar update hook run.
;;;   xdisp-run-window-scroll-functions!  -- site S3 (:18933): the
;;;                                          window-scroll-functions run.
;;;
;;; imp-6 (the part-2 kboard and name readers):
;;;
;;;   xdisp-push-kboard!                  -- sites S1/S3 (:27683,
;;;                                          :28523): push the frame
;;;                                          kboard.
;;;   xdisp-pop-kboard!                   -- sites S2/S4 (:27739,
;;;                                          :28525): pop the kboard.
;;;   xdisp-overriding-local-map-menu-flag-p -- site S5 (:14315,
;;;                                          :14490, :15460): the three
;;;                                          NILP
;;;                                          (Voverriding_local_map_menu_flag)
;;;                                          readers.  One shared
;;;                                          procedure serves all three.
;;;
;;; The push/pop targets are the C stubs push_kboard and pop_kboard in
;;; src/keyboard.c.  Both are already Scheme-backed dispatchers into
;;; (emacs single-kboard) (M27 imp-1), so the imp-6 port is a call
;;; replacement and adds no C primitive.  Resolve them lazily with
;;; delay + module-ref, so the module does not eagerly import
;;; (emacs single-kboard).  brief.org 5.3, 7.
;;;
;;; The S5 reader reads the overriding-local-map-menu-flag cell with the
;;; delayed symbol-value reference.  The C keeps the NILP test and the
;;; DEFVAR_LISP site stays C at imp-6 (imp-7 may move it).  brief.org
;;; 5.4, 7.
;;;
;;; What stays C:
;;;
;;;   - site S4 of imp-5 (:16212, the tool-bar event store) is *not*
;;;     ported.  It calls kbd_buffer_store_event, which is already
;;;     Scheme-backed through kbd_buffer_store_buffered_event.  A full
;;;     port needs a new TOOL_BAR_EVENT builder in src/keyboard.c, which
;;;     rule 4.8 forbids.  Option B (no port) is the brief.org 5
;;;     default.
;;;   - track-mouse stays C (brief.org 5 rule 7).
;;;
;;; Conventions (identical to M34 imp-2/-4, cf. mod/emacs/frame.scm):
;;; cross-module targets are resolved lazily with delay + module-ref;
;;; #nil is elisp nil; a C DEFUN is reached through the (emacs elisp-ref)
;;; defelisp reference; no module-level mutable state.

(define-module (emacs xdisp)
  #:use-module (emacs elisp-ref)      ; defelisp
  #:declarative? #t
  #:export (xdisp-run-activate-menubar-hook!
            xdisp-run-menu-bar-update-hook!
            xdisp-run-window-scroll-functions!
            xdisp-push-kboard!
            xdisp-pop-kboard!
            xdisp-overriding-local-map-menu-flag-p))

;; (emacs command-loop) holds the safe_run_hooks ports.  Resolve each
;; lazily, so the module does not eagerly import (emacs command-loop)
;; (see the (emacs frame) entry in docs: eager #:use-module drags the
;; import chain).  See brief.org 3.
(define %safe-run-hooks!
  (delay (module-ref (resolve-module '(emacs command-loop))
                     'safe-run-hooks!)))
(define %safe-run-hooks-2!
  (delay (module-ref (resolve-module '(emacs command-loop))
                     'safe-run-hooks-2!)))

;;; --- xdisp-run-activate-menubar-hook! ------------------------------
;;; Port of the site-S1 call in update_menu_bar (src/xdisp.c:14279):
;;;   safe_run_hooks (Qactivate_menubar_hook);
;;; Call (emacs command-loop) safe-run-hooks! on the
;;; activate-menubar-hook symbol.  The C keeps the if (!hooks_run) guard.
;;; Return nothing.  See brief.org 3.
(define (xdisp-run-activate-menubar-hook!)
  ((force %safe-run-hooks!) 'activate-menubar-hook))

;;; --- xdisp-run-menu-bar-update-hook! -------------------------------
;;; Port of the site-S2 call in update_menu_bar (src/xdisp.c:14283):
;;;   safe_run_hooks (Qmenu_bar_update_hook);
;;; Call (emacs command-loop) safe-run-hooks! on the
;;; menu-bar-update-hook symbol.  Return nothing.  See brief.org 3.
(define (xdisp-run-menu-bar-update-hook!)
  ((force %safe-run-hooks!) 'menu-bar-update-hook))

;;; --- xdisp-run-window-scroll-functions! ----------------------------
;;; Port of the site-S3 call in run_window_scroll_functions
;;; (src/xdisp.c:18933):
;;;   safe_run_hooks_2   (C stub; retired at M34 imp-7)
;;;     (Qwindow_scroll_functions, window, make_fixnum (CHARPOS (startp)));
;;; Call (emacs command-loop) safe-run-hooks-2! on the
;;; window-scroll-functions symbol, passing WINDOW and STARTP.  The C
;;; keeps the if (!NILP (Vwindow_scroll_functions)) guard, the
;;; make_fixnum wrap, the SET_TEXT_POS_FROM_MARKER call, and the
;;; set_buffer_internal call.  safe-run-hooks-2! reads the hook variable
;;; and does nothing when the hook is nil, so the guard needs no Scheme
;;; re-test.  Return nothing.  See brief.org 3, 4.
(define (xdisp-run-window-scroll-functions! window startp)
  ((force %safe-run-hooks-2!) 'window-scroll-functions window startp))

;;; --- imp-6 lazy cross-module references ----------------------------
;;; The push/pop targets live in (emacs single-kboard).  Resolve each
;;; lazily, so the module does not eagerly import it.  brief.org 5.3, 7.
(define %push-kboard!
  (delay (module-ref (resolve-module '(emacs single-kboard)) 'push-kboard!)))
(define %pop-kboard!
  (delay (module-ref (resolve-module '(emacs single-kboard)) 'pop-kboard!)))

;; The S5 cell reader.  symbol-value is a C DEFUN; resolve it lazily
;; through the (emacs elisp-ref) defelisp reference.  brief.org 7.
(defelisp %symbol-value symbol-value)

;;; --- xdisp-push-kboard! --------------------------------------------
;;; Port of the site-S1/S3 calls in display_mode_line (src/xdisp.c:27683)
;;; and Fformat_mode_line (:28523):
;;;   push_kboard (FRAME_KBOARD (it.f));
;;; Push the frame kboard.  The C dispatcher makes the KBOARD smob and
;;; keeps the record_unwind_protect and the dynwind block.  Return
;;; nothing.  brief.org 6, 7.
(define (xdisp-push-kboard! kb) ((force %push-kboard!) kb))

;;; --- xdisp-pop-kboard! ---------------------------------------------
;;; Port of the site-S2/S4 calls in display_mode_line (src/xdisp.c:27739)
;;; and Fformat_mode_line (:28525):
;;;   pop_kboard ();
;;; Pop the kboard.  Return nothing.  brief.org 6, 7.
(define (xdisp-pop-kboard!) ((force %pop-kboard!)))

;;; --- xdisp-overriding-local-map-menu-flag-p ------------------------
;;; Port of the site-S5 reads in update_menu_bar (src/xdisp.c:14315),
;;; update_tab_bar (:14490), and update_tool_bar (:15460):
;;;   if (NILP (Voverriding_local_map_menu_flag))
;;; Return the test of the cell as elisp t (cell non-nil) or elisp nil
;;; (cell nil).  The C keeps NILP, so the NILP width does not change:
;;; NILP is true for #nil, #f, and ().  #nil is elisp nil; #t is a
;;; non-nil value.  In guilemacs Qt is SCM_BOOL_T, i.e. the Scheme #t
;;; (src/lread.c:2878: lispsym[iQt] = SCM_BOOL_T), so returning #t
;;; returns Qt as brief.org 5.4 asks; EQ against Qt holds, and the C
;;; NILP width is unchanged (cr.org F2).  One procedure serves all
;;; three sites.  brief.org 5.4, 6, 7.
(define (xdisp-overriding-local-map-menu-flag-p)
  (if (eq? ((force %symbol-value) 'overriding-local-map-menu-flag) #nil)
      #nil #t))
