;;; xdisp.scm --- M34 imp-5: the xdisp.c part-1 hook callers
;;;                ((emacs xdisp))
;;;
;;; Moves the *decision* logic of the three live src/xdisp.c hook call
;;; sites into Scheme.  The *mechanism* stays C: the if (!hooks_run)
;;; block and the hooks_run = true write in update_menu_bar, the
;;; if (!NILP (Vwindow_scroll_functions)) guard in
;;; run_window_scroll_functions, the make_fixnum (CHARPOS (startp))
;;; wrap, the SET_TEXT_POS_FROM_MARKER call, and the
;;; set_buffer_internal call.  See brief.org 3, 4.
;;;
;;; Three exported procedures:
;;;
;;;   xdisp-run-activate-menubar-hook!    -- site S1 (src/xdisp.c:14279):
;;;                                          the Lucid hook run.
;;;   xdisp-run-menu-bar-update-hook!     -- site S2 (:14283): the
;;;                                          menu-bar update hook run.
;;;   xdisp-run-window-scroll-functions!  -- site S3 (:18933): the
;;;                                          window-scroll-functions run.
;;;
;;; Site S4 (:16212, the tool-bar event store) is *not* ported.  It calls
;;; kbd_buffer_store_event, which is already Scheme-backed through
;;; kbd_buffer_store_buffered_event.  A full S4 port needs a new
;;; TOOL_BAR_EVENT builder in src/keyboard.c, which rule 4.8 forbids.
;;; Option B (no port) is the brief.org 5 default.
;;;
;;; Conventions (identical to M34 imp-2/-4, cf. mod/emacs/frame.scm):
;;; cross-module targets are resolved lazily with delay + module-ref; #nil
;;; is elisp nil; no defelisp (both targets are Scheme procedures); no
;;; module-level mutable state.

(define-module (emacs xdisp)
  #:declarative? #t
  #:export (xdisp-run-activate-menubar-hook!
            xdisp-run-menu-bar-update-hook!
            xdisp-run-window-scroll-functions!))

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
;;;   safe_run_hooks_2
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
