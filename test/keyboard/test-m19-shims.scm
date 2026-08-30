;;; test-m19-shims.scm --- M19 imp-2 test corpus for the menu/tab-bar/
;;; hscroll helper ports and shims in (emacs lispy-position).
;;;
;;; Sourced by test/keyboard/test-m19-shims.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See docs/m19-plan.org §imp-2 and brief.org.
;;;
;;; Covers:
;;;   * the 9 new C shims in src/keyboard.c (registration + no-error +
;;;     value sanity where deterministic on this GTK build);
;;;   * coords-in-menu-bar-window? / coords-in-tab-bar-window? /
;;;     toolkit-menubar-in-use? (true and false cases, mocked);
;;;   * line-number-mode-hscroll? (matching, different-window, short-list);
;;;   * posn-at-x-y (window with whole nil/non-nil, frame case);
;;;   * mouse-click-menu-bar-intercept / tab-bar-enrich-position (no-hit
;;;     cases — full hit-testing needs a live non-toolkit menu/tab bar,
;;;     which a GTK batch build does not provide);
;;;   * --mlp-dispatch retirement (binding gone, ON_TEXT offset intact).
;;;
;;; The boolean helpers return plain Scheme #t/#f (their C DEFUN wrappers
;;; read them back with scm_is_true), so the checks compare with #t/#f.
;;;
;;; Batch limitation: the three glyph-matrix-dependent shims
;;; (--menu-bar-hpos-vpos, --menu-pixel-to-glyph-coords,
;;; --get-tab-bar-item-kbd) crash on a batch build (no live glyph
;;; matrices), so they are checked for registration only, not called.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

(define mod (resolve-module '(emacs lispy-position)))

(define (modfn name)
  (module-ref mod name))

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

;;; --- 0. Registration + no-error for the 9 new shims ----------------
(define shim-names
  '(--have-ext-menu-bar-p --frame-menu-bar-window --frame-tab-bar-window
    --line-number-display-width-for-window --frame-menu-bar-items
    --frame-tab-bar-items --get-tab-bar-item-kbd
    --menu-bar-hpos-vpos --menu-pixel-to-glyph-coords))
(for-each
 (lambda (n)
   (check (string-append "registered:" (symbol->string n))
          #t (not (eq? (%sym n) #nil))))
 shim-names)

(check "shim/have-ext/no-error" #t
       (no-error? (lambda () ((%sym '--have-ext-menu-bar-p)))))
(check "shim/frame-menu-bar-window/no-error" #t
       (no-error? (lambda () ((%sym '--frame-menu-bar-window) ((%sym 'selected-frame))))))
(check "shim/frame-tab-bar-window/no-error" #t
       (no-error? (lambda () ((%sym '--frame-tab-bar-window) ((%sym 'selected-frame))))))
(check "shim/line-number-width/no-error" #t
       (no-error? (lambda () ((%sym '--line-number-display-width-for-window)
                              ((%sym 'selected-window))))))
(check "shim/menu-bar-items/no-error" #t
       (no-error? (lambda () ((%sym '--frame-menu-bar-items) ((%sym 'selected-frame))))))
(check "shim/tab-bar-items/no-error" #t
       (no-error? (lambda () ((%sym '--frame-tab-bar-items) ((%sym 'selected-frame))))))

;; Deterministic value checks for this GTK build (HAVE_EXT_MENU_BAR on,
;; so no non-toolkit menu-bar window exists; the tab-bar window is nil
;; until a tab bar is displayed).
(check "shim/have-ext/t-on-gtk" #t (eq? ((%sym '--have-ext-menu-bar-p)) #t))
(check "shim/frame-menu-bar-window/nil-on-gtk" #t
       (eq? ((%sym '--frame-menu-bar-window) ((%sym 'selected-frame))) #nil))
(check "shim/line-number-width/fixnum" #t
       (integer? ((%sym '--line-number-display-width-for-window)
                  ((%sym 'selected-window)))))

;;; --- 1. coords-in-menu-bar-window? / coords-in-tab-bar-window? -----
;;; Box-test the two window-test helpers by mocking the frame-internal
;;; window accessor and window-edges to a fixed box (10 20 30 40).
(define (mock-var name proc)
  (let ((old (module-ref mod name)))
    (module-set! mod name (delay proc))
    old))

(let ((old-fmw (module-ref mod '%--frame-menu-bar-window))
      (old-we  (module-ref mod '%window-edges))
      (old-fbw (module-ref mod '%frame-internal-border-width)))
  (module-set! mod '%--frame-menu-bar-window (delay (lambda (f) 'w)))
  (module-set! mod '%window-edges (delay (lambda (w a b c) '(10 20 30 40))))
  (module-set! mod '%frame-internal-border-width (delay (lambda (f) 0)))
  (report "coords/menu/inside"
          (if (eq? ((modfn 'coords-in-menu-bar-window?) 'frame 15 25) #t) 'PASS 'FAIL))
  (report "coords/menu/outside-x"
          (if (eq? ((modfn 'coords-in-menu-bar-window?) 'frame 5 25) #f) 'PASS 'FAIL))
  (report "coords/menu/outside-y"
          (if (eq? ((modfn 'coords-in-menu-bar-window?) 'frame 15 50) #f) 'PASS 'FAIL))
  ;; internal-border offset: window-edges adds the frame's internal
  ;; border width to every edge, but the C macros add it only to the Y
  ;; edges for a menu/tab-bar window (WINDOW_TOP/BOTTOM_EDGE_Y,
  ;; src/window.h:794-803) while WINDOW_LEFT/RIGHT_EDGE_X always add it
  ;; (src/window.h:755-763).  So with border=2 on box (10 20 30 40) the
  ;; C box is x:[10,30], y:[18,38] -- X is NOT shifted.
  (module-set! mod '%frame-internal-border-width (delay (lambda (f) 2)))
  (report "coords/menu/border-inside"
          (if (eq? ((modfn 'coords-in-menu-bar-window?) 'frame 15 19) #t) 'PASS 'FAIL))
  (report "coords/menu/border-y-just-inside"
          (if (eq? ((modfn 'coords-in-menu-bar-window?) 'frame 15 18) #t) 'PASS 'FAIL))
  (report "coords/menu/border-y-just-outside"
          (if (eq? ((modfn 'coords-in-menu-bar-window?) 'frame 15 17) #f) 'PASS 'FAIL))
  ;; X must stay at the raw window-edges value: 9 (one inside 10) must be
  ;; rejected and 29 (one inside 30) accepted.  The pre-fix code wrongly
  ;; shifted both X edges left by the border, so 9 passed and 29 failed.
  (report "coords/menu/border-x-just-left"
          (if (eq? ((modfn 'coords-in-menu-bar-window?) 'frame 9 25) #f) 'PASS 'FAIL))
  (report "coords/menu/border-x-just-right"
          (if (eq? ((modfn 'coords-in-menu-bar-window?) 'frame 29 25) #t) 'PASS 'FAIL))
  (module-set! mod '%frame-internal-border-width (delay (lambda (f) 0)))
  (module-set! mod '%--frame-menu-bar-window old-fmw)
  (module-set! mod '%window-edges old-we)
  (module-set! mod '%frame-internal-border-width old-fbw))

(let ((old-ftw (module-ref mod '%--frame-tab-bar-window))
      (old-we  (module-ref mod '%window-edges))
      (old-fbw (module-ref mod '%frame-internal-border-width)))
  (module-set! mod '%--frame-tab-bar-window (delay (lambda (f) 'w)))
  (module-set! mod '%window-edges (delay (lambda (w a b c) '(10 20 30 40))))
  (module-set! mod '%frame-internal-border-width (delay (lambda (f) 0)))
  (report "coords/tab/inside"
          (if (eq? ((modfn 'coords-in-tab-bar-window?) 'frame 15 25) #t) 'PASS 'FAIL))
  (report "coords/tab/outside"
          (if (eq? ((modfn 'coords-in-tab-bar-window?) 'frame 5 25) #f) 'PASS 'FAIL))
  (module-set! mod '%--frame-tab-bar-window old-ftw)
  (module-set! mod '%window-edges old-we)
  (module-set! mod '%frame-internal-border-width old-fbw))

;;; --- 2. toolkit-menubar-in-use? -------------------------------------
;;; On this GTK build %--have-ext-menu-bar-p is #t; only the
;;; FRAME_WINDOW_P (window-system) leg is mocked.
(let ((old-ws (module-ref mod '%--window-system)))
  (module-set! mod '%--window-system (delay (lambda (f) #t)))
  (report "toolkit/window-t"
          (if (eq? ((modfn 'toolkit-menubar-in-use?) 'f) #t) 'PASS 'FAIL))
  (module-set! mod '%--window-system (delay (lambda (f) #nil)))
  (report "toolkit/window-nil"
          (if (eq? ((modfn 'toolkit-menubar-in-use?) 'f) #f) 'PASS 'FAIL))
  (module-set! mod '%--window-system old-ws))

;;; --- 3. line-number-mode-hscroll? -----------------------------------
(let ((old-dw (module-ref mod '%--down-mouse-line-number-width))
      (old-lw (module-ref mod '%--line-number-display-width-for-window)))
  (module-set! mod '%--down-mouse-line-number-width (delay (lambda () 5)))
  (module-set! mod '%--line-number-display-width-for-window (delay (lambda (w) 3)))
  (report "lnh/matching"
          (if (eq? ((modfn 'line-number-mode-hscroll?)
                    (list 'w 1 2 3 4 5 '(7 . 8))
                    (list 'w 1 2 3 4 5 '(7 . 9))) #t) 'PASS 'FAIL))
  (report "lnh/diff-win"
          (if (eq? ((modfn 'line-number-mode-hscroll?)
                    (list 'a 1 2 3 4 5 '(7 . 8))
                    (list 'b 1 2 3 4 5 '(7 . 8))) #f) 'PASS 'FAIL))
  (report "lnh/short"
          (if (eq? ((modfn 'line-number-mode-hscroll?)
                    '(w 1 2 3) '(w 1 2 3)) #f) 'PASS 'FAIL))
  (module-set! mod '%--down-mouse-line-number-width old-dw)
  (module-set! mod '%--line-number-display-width-for-window old-lw))

;;; --- 4. posn-at-x-y -------------------------------------------------
;;; Window case (whole nil and non-nil) and frame case (window nil).
(let* ((w ((%sym 'selected-window)))
       (f ((%sym 'window-frame) w))
       (res-a ((modfn 'posn-at-x-y) f w 5 5 #nil))
       (res-b ((modfn 'posn-at-x-y) f w 5 5 #t))
       (res-c ((modfn 'posn-at-x-y) f #nil 5 5 #nil)))
  (report "posn/win/whole-nil"
          (if (and (not (eq? res-a #nil)) (list? res-a)) 'PASS 'FAIL))
  (report "posn/win/whole-t"
          (if (and (not (eq? res-b #nil)) (list? res-b)) 'PASS 'FAIL))
  (report "posn/frame"
          (if (and (not (eq? res-c #nil)) (list? res-c)) 'PASS 'FAIL)))

;;; --- 5. mouse-click-menu-bar-intercept / tab-bar-enrich-position ----
;;; No-hit cases (a live non-toolkit menu/tab bar is unavailable on a
;;; GTK batch build, so the hit path cannot be exercised here — same
;;; limitation as test-m19-bodies.scm's image-hotspot corpus).
(report "intercept/no-hit-mod0"
        (if (eq? ((modfn 'mouse-click-menu-bar-intercept)
                  ((%sym 'selected-frame)) 0 0 0 0 #nil) #nil) 'PASS 'FAIL))
(let ((pos (list 'w 'text '(1 . 2) 0)))
  (report "tabbar/no-hit"
          (if (eq? ((modfn 'tab-bar-enrich-position)
                    ((%sym 'selected-frame)) 0 0 pos) pos) 'PASS 'FAIL)))

;;; --- 5b. menu-bar-touch-activate (M20 imp-4) -----------------------
;;; Port of the C --menu-bar-touch-activate body (keyboard.c:6978-7037),
;;; reusing menu-bar-item-for-column.  Mock the menu-bar window, the raw
;;; hpos/vpos shim, the frame menu-bar-lines parameter, and
;;; FRAME_MENU_BAR_ITEMS so the hit test is deterministic on a GTK batch
;;; build (which has no live non-toolkit menu-bar window).
(let ((old-fmw (module-ref mod '%--frame-menu-bar-window))
      (old-hv  (module-ref mod '%--menu-bar-hpos-vpos-raw))
      (old-fp  (module-ref mod '%--frame-parameter))
      (old-fmi (module-ref mod '%--frame-menu-bar-items)))
  (module-set! mod '%--frame-menu-bar-window (delay (lambda (f) 'w)))
  (module-set! mod '%--menu-bar-hpos-vpos-raw (delay (lambda (w x y) (cons 3 0))))
  (module-set! mod '%--frame-parameter
                 (delay (lambda (f k) (if (eq? k 'menu-bar-lines) 1 #nil))))
  ;; FRAME_MENU_BAR_ITEMS: 4-slot rows (KEY STR DEF HPOS); column 3 hits
  ;; the 4-char "File" string (HPOS 0, length 4) → KEY 'file.
  (module-set! mod '%--frame-menu-bar-items
                 (delay (lambda (f) (vector 'file "File" 'file-menu 0))))
  ;; Hit: column 3, row 0 within the single menu-bar line.
  (report "touch-activate/hit"
          (if (equal? ((modfn 'menu-bar-touch-activate) 'frame 0 0 'fow 9)
                      (list 'file (list 'fow 'menu-bar '(0 . 0) 9)))
              'PASS 'FAIL))
  ;; Column 20 misses every item → nil.
  (module-set! mod '%--menu-bar-hpos-vpos-raw (delay (lambda (w x y) (cons 20 0))))
  (report "touch-activate/column-miss"
          (if (eq? ((modfn 'menu-bar-touch-activate) 'frame 0 0 'fow 9) #nil)
              'PASS 'FAIL))
  ;; Row 5 out of range (only 1 line) → nil.
  (module-set! mod '%--menu-bar-hpos-vpos-raw (delay (lambda (w x y) (cons 3 5))))
  (report "touch-activate/row-out-of-range"
          (if (eq? ((modfn 'menu-bar-touch-activate) 'frame 0 0 'fow 9) #nil)
              'PASS 'FAIL))
  ;; No menu-bar window → nil.
  (module-set! mod '%--frame-menu-bar-window (delay (lambda (f) #nil)))
  (report "touch-activate/no-window"
          (if (eq? ((modfn 'menu-bar-touch-activate) 'frame 0 0 'fow 9) #nil)
              'PASS 'FAIL))
  (module-set! mod '%--frame-menu-bar-window old-fmw)
  (module-set! mod '%--menu-bar-hpos-vpos-raw old-hv)
  (module-set! mod '%--frame-parameter old-fp)
  (module-set! mod '%--frame-menu-bar-items old-fmi))

;;; --- 6. --mlp-dispatch retirement -----------------------------------
;;; The binding and the C DEFUN must be gone; the inlined ON_TEXT
;;; offset arithmetic must still agree with the shims.
(report "retire/no-mlp-dispatch-binding"
        (if (not (module-variable mod '%--mlp-dispatch)) 'PASS 'FAIL))
(report "retire/no-mlp-dispatch-defun"
        (if (eq? (%sym '--mlp-dispatch) #nil) 'PASS 'FAIL))
;; The ON_TEXT offset arithmetic now lives inline in Scheme (case 0 of
;; the retired --mlp-dispatch).  Mock the four shims it reads so the
;; check is deterministic and does not touch live glyph geometry:
;;   xret = mx - window-box-left(w,TEXT_AREA)
;;   yret = my - WINDOW_TOP_EDGE_Y - tab-line-height - header-line-height
(let ((old-orig (module-ref mod '%--window-frame-origin))
      (old-box  (module-ref mod '%--window-box-left))
      (old-tab  (module-ref mod '%--window-tab-line-height))
      (old-hdr  (module-ref mod '%--window-header-line-height)))
  (module-set! mod '%--window-frame-origin (delay (lambda (w) (cons 100 200))))
  (module-set! mod '%--window-box-left (delay (lambda (w a) 130)))
  (module-set! mod '%--window-tab-line-height (delay (lambda (w) 5)))
  (module-set! mod '%--window-header-line-height (delay (lambda (w) 8)))
  (call-with-values
      (lambda () ((modfn 'ml-dispatch-text-line-margin) 'w 1 10 5))
    (lambda (posn object string-info col row dx dy width height xret yret textpos)
      (report "text/offset-agrees"
              (if (and (= xret -120) (= yret -208)) 'PASS
                  (list 'FAIL 'expected '(-120 . -208)
                        'got (cons xret yret))))))
  (module-set! mod '%--window-frame-origin old-orig)
  (module-set! mod '%--window-box-left old-box)
  (module-set! mod '%--window-tab-line-height old-tab)
  (module-set! mod '%--window-header-line-height old-hdr))
