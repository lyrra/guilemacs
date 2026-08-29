;;; test-m19-kind.scm --- M19 imp-3: --ie-kind-from-name → Scheme lookup
;;;
;;; Verifies that the ported (emacs lispy-position) ie-kind-from-name
;;; returns the same event_kind integers as the retired C
;;; --ie-kind-from-name body, for this exact build.
;;;
;;; The expected integers below were captured live from the original
;;; fully-C --ie-kind-from-name on this build (HAVE_DBUS on,
;;; USE_FILE_NOTIFY on, HAVE_WINDOW_SYSTEM on, USE_TOOLKIT_SCROLL_BARS
;;; on, HAVE_EXT_MENU_BAR on; THREADS_ENABLED/HAVE_XWIDGETS/HAVE_NTGUI/
;;; HAVE_NS/HAVE_HAIKU/HAVE_ANDROID off).  They are build-configuration
;;; dependent and must not be treated as portable — the whole point of
;;; the port is that these integers keep coming from C.  See
;;; docs/m19-plan.org §imp-3 and brief.org "Read this first".
;;;
;;; Sourced by test/keyboard/test-m19-kind.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results`.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))
(use-modules (emacs lispy-position))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

;;; Expected symbol → integer, captured from the original C build.
(define %expected-alist
  '((dbus-event . 27)
    (thread-event . -1)
    (xwidget-event . -1)
    (xwidget-display-event . -1)
    (file-notify . 29)
    (no-event . 0)
    (delete-frame . 12)
    (iconify-frame . 14)
    (make-frame-visible . 15)
    (move-frame . 24)
    (select-window . 25)
    (save-session . 26)
    (config-changed-event . 28)
    (preedit-text . 30)
    (end-session . -1)
    (language-change . -1)
    (user-signal-event . 18)
    (help-echo . 19)
    (focus-in . 22)
    (focus-out . 23)
    (tab-bar . 20)
    (tool-bar . 21)
    (drag-n-drop . 17)
    (menu-bar . 13)
    (scroll-bar-click-toolkit . 8)
    (horizontal-scroll-bar-click-toolkit . 9)
    (ascii-keystroke . 1)
    (multibyte-char-keystroke . 2)
    (non-ascii-keystroke . 3)
    (ns-nonkey . -1)
    (ns-text-event . -1)
    (multimedia-key . -1)
    (wheel-event . 6)
    (horizontal-wheel-event . 7)
    (touch-end . 31)
    (pinch . 35)
    (touchscreen-begin . 33)
    (touchscreen-end . 34)
    (touchscreen-update . 32)
    (mouse-click-event . 5)
    (scroll-bar-click-event . -1)
    (horizontal-scroll-bar-click-event . -1)
    (selection-request-event . 10)
    (selection-clear-event . 11)
    (monitors-changed . 36)
    (menu-bar-activate-event . 16)
    (notification-event . -1)))

;;; Every known symbol must map to its captured integer.
(for-each
 (lambda (entry)
   (let* ((sym (car entry))
          (expected (cdr entry))
          (got (ie-kind-from-name sym)))
     (report (string-append "kind/" (symbol->string sym))
             (if (eqv? expected got)
                 'PASS
                 (list 'FAIL 'expected expected 'got got)))))
 %expected-alist)

;;; Unknown symbol resolves to -1.
(report "kind/unknown-symbol"
        (if (eqv? -1 (ie-kind-from-name 'not-a-real-event-kind))
            'PASS 'FAIL))
