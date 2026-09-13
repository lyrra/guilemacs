;;; menu.scm --- M33 imp-2: the xmenu.c/gtkutil.c menu/help consumers
;;;                  ((emacs menu))
;;;
;;; Moves the *decision* logic of the X/GTK menu help and timer paths
;;; out of src/xmenu.c and src/gtkutil.c and into Scheme.  The C
;;; *mechanism* stays C: the XPending loop, the file-descriptor set
;;; build, the XFlush and xg_select / pselect call in
;;; x_menu_wait_for_event, and the g_timeout_add call in
;;; xg_maybe_add_timer.  See docs/m33-plan.org A5 ... A7.
;;;
;;; Four exported procedures:
;;;
;;;   menu-show-help-event      -- src/xmenu.c:727-738, the frame /
;;;                                no-frame choice of show_help_event.
;;;   menu-help-callback        -- src/xmenu.c:2492-2520, the
;;;                                menu_help_callback body.
;;;   x-menu-timer-wait         -- src/xmenu.c:195, the timer-wait
;;;                                decision of x_menu_wait_for_event.
;;;   xg-maybe-add-timer-delay  -- src/gtkutil.c:2436-2447, the re-arm
;;;                                decision of xg_maybe_add_timer.
;;;
;;; Port principle (brief.org 3.6): the module decides the *delay*.  The
;;; C forms the argument of its own system call -- a (SEC . NSEC) pair
;;; for pselect / xg_select, a millisecond count for g_timeout_add.  The
;;; C dispatcher in src/xmenu.c converts the pair with make_timespec; the
;;; C dispatcher in src/gtkutil.c passes the count to g_timeout_add.
;;;
;;; Divergence record.  menu-help-callback delegates to the imp-1
;;; procedure (emacs terminal) tty-menu-help-callback instead of
;;; duplicating its body.  The C body at src/xmenu.c:2492-2520 equals
;;; the body at src/term.c:3627 that imp-1 already ported (brief.org
;;; 3.3, the default assumption).  So the imp-1 code and
;;; test/keyboard/test-m33-imp1.scm stay unchanged.  The C caller keeps
;;; its name and its fn-pointer signature at src/xmenu.c:2817.
;;;
;;; Conventions (identical to M9-M33): defelisp delayed references for
;;; every C DEFUN ((force %--foo)); elisp list/vector values built with
;;; the plain Scheme cons and integers (a guilemacs Scheme integer is an
;;; elisp fixnum); #nil is elisp nil; no module-level mutable state.
;;;
;;; Cross-module targets are resolved lazily.  An eager import of (emacs
;;; help-echo) pulls in (emacs kbd-buffer) -> (emacs lispy-event), which
;;; does not load at this boot point.  (emacs timers) and (emacs
;;; terminal) use the same idiom (brief.org 3.1).

(define-module (emacs menu)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (menu-show-help-event
            menu-help-callback
            x-menu-timer-wait
            xg-maybe-add-timer-delay))

;;; --- lazy cross-module targets -------------------------------------
;; show-help-echo and store-help-event live in (emacs help-echo).
(define %show-help-echo
  (delay (module-ref (resolve-module '(emacs help-echo)) 'show-help-echo)))
(define %store-help-event
  (delay (module-ref (resolve-module '(emacs help-echo)) 'store-help-event)))
;; timer-check lives in (emacs timers); it returns #nil for "no active
;; timer" or a (SEC . NSEC) wait pair (its own loop consumes the #t
;; "call again" result).
(define %timer-check
  (delay (module-ref (resolve-module '(emacs timers)) 'timer-check)))
;; The imp-1 help-callback body lives in (emacs terminal).
(define %tty-menu-help-callback
  (delay (module-ref (resolve-module '(emacs terminal))
                     'tty-menu-help-callback)))

;;; --- helpers -------------------------------------------------------
(define (truthy? x)
  "Elisp truthiness: everything except #nil is true."
  (not (eq? x #nil)))

;;; --- menu-show-help-event ------------------------------------------
;;; Port of show_help_event (src/xmenu.c:727-738).  FRAME is the frame
;;; object, or #nil when the C frame pointer is NULL.  With a frame,
;;; store a help event; without one, show the help echo directly.  Both
;;; targets are Scheme procedures in (emacs help-echo); no C primitive.
(define (menu-show-help-event frame help)
  (if (truthy? frame)
      ((force %store-help-event) frame help)
      ((force %show-help-echo) help #nil #nil #nil))
  #nil)

;;; --- menu-help-callback --------------------------------------------
;;; Port of menu_help_callback (src/xmenu.c:2492-2520).  The body is
;;; identical to the tty_menu_help_callback body, so this procedure
;;; delegates to the imp-1 procedure.  HELP-STRING is a Scheme string
;;; or #nil; PANE and ITEM are fixnums.
(define (menu-help-callback help-string pane item)
  ((force %tty-menu-help-callback) help-string pane item))

;;; --- x-menu-timer-wait ---------------------------------------------
;;; Port of the timer decision at src/xmenu.c:195 (with the C-side
;;; timespec_valid_p / ntp choice at :213-216 staying C).  Return #nil
;;; for "no active timer", or the (SEC . NSEC) deadline that pselect /
;;; xg_select wait for.  Keep the port thin; the select call stays C.
(define (x-menu-timer-wait)
  ((force %timer-check)))

;;; --- xg-maybe-add-timer-delay --------------------------------------
;;; Port of the timer decision at src/gtkutil.c:2436-2447.  Return #nil
;;; for "no active timer", or the delay in milliseconds that
;;; g_timeout_add waits for.  TIMESPEC_HZ is 1000000000 (lib/timespec.h),
;;; so one millisecond is 1000000 nanoseconds; the form below is the C
;;; ceiling division (nsec + per_ms - 1) / per_ms.
(define (xg-maybe-add-timer-delay)
  (let ((t ((force %timer-check))))
    (if (eq? t #nil)
        #nil
        (let ((s (car t)) (nsec (cdr t)))
          (+ (* s 1000) (quotient (+ nsec 999999) 1000000))))))
