(define-module (emacs lispy-position)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (make-lispy-position))

;;; M9 imp-6.3 — per-region Scheme port of make_lispy_position.
;;;
;;; make_lispy_position (src/keyboard.c:6363–6667) builds a mouse-click
;;; position list from a frame and pixel coordinates.  The C body was
;;; decomposed into mlp_* helpers (imp-6.2); imp-6.3 adds thin adapter
;;; DEFUNs that compute wx/wy internally from frame-relative mx/my and
;;; pack out-params into single list returns.  This module stitches
;;; them together.

;;; Lazy C-primitive references.

(defelisp %--mlp-dispatch --mlp-dispatch)

;;; M19 imp-1 — thin C shim references.  These wrap the heavyweight C
;;; geometry/matrix functions the mlp_* bodies call; each is marked
;;; FIX-20260828-guilemacs: in src/keyboard.c.
(defelisp %--find-hot-spot            --find-hot-spot)
(defelisp %--frame-internal-border-part --frame-internal-border-part)
(defelisp %--window-box-left          --window-box-left)
(defelisp %--window-box-width         --window-box-width)
(defelisp %--window-frame-origin      --window-frame-origin)
(defelisp %--mode-line-string         --mode-line-string)
(defelisp %--marginal-area-string     --marginal-area-string)
(defelisp %--buffer-posn-from-coords  --buffer-posn-from-coords)
(defelisp %--window-from-coordinates  --window-from-coordinates)
(defelisp %--toolkit-position         --toolkit-position)

;;; Elisp accessors reused directly (no new shim).
(defelisp %--window-fringes            window-fringes)
(defelisp %--window-header-line-height window-header-line-height)
(defelisp %--window-tab-line-height    window-tab-line-height)
(defelisp %--window-right-divider-width window-right-divider-width)
(defelisp %--window-bottom-divider-width window-bottom-divider-width)
(defelisp %--window-scroll-bar-width  window-scroll-bar-width)
(defelisp %--window-scroll-bar-height window-scroll-bar-height)
(defelisp %--window-scroll-bars       window-scroll-bars)
(defelisp %--window-frame             window-frame)
(defelisp %--frame-parameter          frame-parameter)
(defelisp %--window-system            window-system)

;;; Elisp globals / predicates.
(defelisp %symbol-value symbol-value)
;; track-mouse is a dynamic variable — read fresh each call.
(define (track-mouse-value)
  ((force %symbol-value) 'track-mouse))
(defelisp %windowp windowp)

;;; Fringe scroll-bar "on right" test for buffer-posn-pass's x2 branch.
;;; Mirrors WINDOW_HAS_VERTICAL_SCROLL_BAR_ON_RIGHT by resolving the
;;; window's VERTICAL-TYPE through its frame default when it is `t'.
(define (vscroll-on-right? w)
  (let ((vtype (list-ref ((force %--window-scroll-bars) w) 2)))
    (if (eq? vtype 'right)
        #t
        (if (eq? vtype #t)
            (let ((ftype ((force %--frame-parameter)
                          ((force %--window-frame) w) 'vertical-scroll-bars)))
              (eq? ftype 'right))
            #f))))

;;; Per-region helpers — native Scheme ports of the mlp_* C bodies
;;; (src/keyboard.c).  The C mlp_* functions and --mlp-dispatch stay
;;; intact and callable until imp-2's cutover; these now use the shims
;;; above instead.

(define (image-hotspot-check object dx dy posn)
  "Return the hotspot id of OBJECT's :map at (DX, DY), or POSN.
See mlp_image_hotspot_check (src/keyboard.c).  The whole
HAVE_WINDOW_SYSTEM-guarded body lives in --find-hot-spot; on a build
without a window system it returns nil and we fall through to POSN."
  (let ((hit ((force %--find-hot-spot) object dx dy)))
    (if (eq? hit #nil) posn hit)))

(define (internal-border f x y posn)
  "Return the internal-border part symbol of F at (X, Y), or POSN.
See mlp_internal_border (src/keyboard.c).  The whole guarded body
(FRAME_WINDOW_P / FRAME_LIVE_P / nilp POSN / border width /
drag-internal-border param) lives in --frame-internal-border-part."
  (let ((sym ((force %--frame-internal-border-part) f x y posn)))
    (if (eq? sym #nil) posn sym)))

(define (frame-preamble f mx my)
  "Return (WINDOW-OR-FRAME PART POSN) for frame-relative (MX, MY).
See mlp_frame_preamble (src/keyboard.c)."
  (let* ((track (track-mouse-value))
         (res (if (eq? f #nil)
                  (list #nil 0 #nil)
                  ((force %--window-from-coordinates) f mx my)))
         (window (list-ref res 0))
         (part (list-ref res 1))
         (bar-kind (list-ref res 2))  ; 'tab-bar / 'tool-bar / nil
         (posn #nil))
    ;; tab-bar/tool-bar window identity (inside shim, HAVE_WINDOW_SYSTEM).
    (when (and (not (eq? bar-kind #nil))
               (or (eq? track #nil) (eq? track #t)))
      (set! posn bar-kind))
    (when (not (eq? bar-kind #nil))
      (set! window #nil))
    ;; toolkit position hook (inside shim).
    (let ((tk (if (eq? f #nil) #nil ((force %--toolkit-position) f mx my))))
      (when (and (not (eq? tk #nil))
                 (or (eq? track #nil) (eq? track #t)))
        (if (eq? (car tk) #t)
            (set! posn 'menu-bar)
            (if (eq? (cdr tk) #t)
                (set! posn 'tool-bar)))))
    ;; Non-window-system tab-bar strip check.
    (when (and (not (eq? f #nil))
               (not ((force %--window-system) f))
               (> ((force %--frame-parameter) f 'tab-bar-lines) 0)
               (>= my ((force %--frame-parameter) f 'menu-bar-lines))
               (< my (+ ((force %--frame-parameter) f 'menu-bar-lines)
                        ((force %--frame-parameter) f 'tab-bar-lines))))
      (set! posn 'tab-bar)
      (set! window #nil))
    (list window part posn)))

(define (fringes w left? mx my)
  "Left/right fringe click.  Returns (values POSN COL DX DY XRET YRET).
See mlp_fringes (src/keyboard.c)."
  (let* ((origin ((force %--window-frame-origin) w))
         (wx (- mx (car origin)))
         (wy (- my (cdr origin)))
         (outside? (eq? (list-ref ((force %--window-fringes) w) 2) #t))
         (lm ((force %--window-box-width) w 0))   ; LEFT_MARGIN_AREA
         (ta ((force %--window-box-width) w 1))   ; TEXT_AREA
         (rm ((force %--window-box-width) w 2))   ; RIGHT_MARGIN_AREA
         (dx (if left?
                 (- wx (if outside? 0 lm))
                 (- wx lm ta (if outside? rm 0))))
         (dy (- wy ((force %--window-tab-line-height) w)
                   ((force %--window-header-line-height) w))))
    (values (if left? 'left-fringe 'right-fringe) 0 dx dy wx dy)))

(define (scroll-border w part mx my)
  "Scroll-bar / border / divider click.  Returns
(values POSN WIDTH DX XRET DY YRET).  See mlp_scroll_border
(src/keyboard.c).  PART values are the real window_part enum
(dispextern.h): ON_VERTICAL_BORDER=3, ON_VERTICAL_SCROLL_BAR=10,
ON_HORIZONTAL_SCROLL_BAR=11, ON_RIGHT_DIVIDER=12, ON_BOTTOM_DIVIDER=13."
  (let* ((origin ((force %--window-frame-origin) w))
         (wx (- mx (car origin)))
         (wy (- my (cdr origin))))
    (cond
     ((= part 3)   ; ON_VERTICAL_BORDER
      (values 'vertical-line 1 0 wx wy wy))
     ((= part 10)  ; ON_VERTICAL_SCROLL_BAR
      (values 'vertical-scroll-bar
              ((force %--window-scroll-bar-width) w) wx wx wy wy))
     ((= part 11)  ; ON_HORIZONTAL_SCROLL_BAR
      (values 'horizontal-scroll-bar
              ((force %--window-scroll-bar-height) w) wx wx wy wy))
     ((= part 12)  ; ON_RIGHT_DIVIDER
      (values 'right-divider
              ((force %--window-right-divider-width) w) wx wx wy wy))
     (else         ; ON_BOTTOM_DIVIDER
      (values 'bottom-divider
              ((force %--window-bottom-divider-width) w) wx wx wy wy)))))

(define (mode-header-line w part mx my)
  "Mode/header/tab-line click.  Returns
(values POSN OBJECT STRING-INFO COL ROW DX DY WIDTH HEIGHT XRET).
See mlp_mode_header_line (src/keyboard.c)."
  (let* ((origin ((force %--window-frame-origin) w))
         (wx (- mx (car origin)))
         (wy (- my (cdr origin)))
         (res ((force %--mode-line-string) w part wx wy))
         (string (list-ref res 0))
         (charpos (list-ref res 1))
         (object (list-ref res 2))
         (col (list-ref res 3))
         (row (list-ref res 4))
         (dx (list-ref res 5))
         (dy (list-ref res 6))
         (width (list-ref res 7))
         (height (list-ref res 8))
         (posn (cond ((= part 2) 'mode-line)   ; ON_MODE_LINE
                     ((= part 5) 'tab-line)    ; ON_TAB_LINE
                     (else 'header-line)))     ; ON_HEADER_LINE
         (string-info (if (string? string) (cons string charpos) #nil)))
    (values posn object string-info col row dx dy width height wx)))

(define (margins w part mx my)
  "Left/right margin click.  Returns
(values POSN OBJECT STRING-INFO COL ROW DX DY WIDTH HEIGHT XRET YRET).
See mlp_margins (src/keyboard.c)."
  (let* ((origin ((force %--window-frame-origin) w))
         (wx (- mx (car origin)))
         (wy (- my (cdr origin)))
         (res ((force %--marginal-area-string) w part wx wy))
         (string (list-ref res 0))
         (charpos (list-ref res 1))
         (object (list-ref res 2))
         (col (list-ref res 3))
         (row (list-ref res 4))
         (dx (list-ref res 5))
         (dy (list-ref res 6))
         (width (list-ref res 7))
         (height (list-ref res 8))
         (posn (if (= part 8) 'left-margin 'right-margin))  ; ON_LEFT_MARGIN=8
         (string-info (if (string? string) (cons string charpos) #nil))
         (yret (- wy ((force %--window-tab-line-height) w)
                     ((force %--window-header-line-height) w))))
    (values posn object string-info col row dx dy width height wx yret)))

(define (buffer-posn-pass w part mx my xret posn)
  "Post-dispatch buffer-position pass.  Returns
(values TEXTPOS POSN OBJECT STRING-INFO COL ROW DX DY WIDTH HEIGHT).
See mlp_buffer_posn_pass (src/keyboard.c).  The x2/y2 branch logic
stays here; only the matrix walk is in --buffer-posn-from-coords."
  (let* ((origin ((force %--window-frame-origin) w))
         (wy (- my (cdr origin)))
         (x2 (cond ((= part 1) xret)                 ; ON_TEXT
                   ((or (= part 7) (= part 9)        ; ON_RIGHT_FRINGE / ON_RIGHT_MARGIN
                        (and (= part 10)             ; ON_VERTICAL_SCROLL_BAR
                             (vscroll-on-right? w)))
                    (- mx ((force %--window-box-left) w 1)))  ; TEXT_AREA
                   (else 0)))
         (res ((force %--buffer-posn-from-coords) w x2 wy))
         (string (list-ref res 0))
         (textpos (list-ref res 1))
         (string-pos (list-ref res 2))
         (object (list-ref res 3))
         (col (list-ref res 4))
         (row (list-ref res 5))
         (dx (list-ref res 6))
         (dy (list-ref res 7))
         (width (list-ref res 8))
         (height (list-ref res 9))
         (new-posn (if (eq? posn #nil) textpos posn))
         (string-info (if (and (eq? posn #nil)
                               (string? string))
                          (cons string string-pos)
                          #nil)))
    (values textpos new-posn object string-info col row dx dy width height)))

;;; 6.3.9 Orchestrator — replaces the C make_lispy_position body.
;;;
;;; Window-part enum values (must match src/dispextern.h:216):
;;;   ON_NOTHING = 0, ON_TEXT = 1, ON_MODE_LINE = 2,
;;;   ON_VERTICAL_BORDER = 3, ON_HEADER_LINE = 4, ON_TAB_LINE = 5,
;;;   ON_LEFT_FRINGE = 6, ON_RIGHT_FRINGE = 7, ON_LEFT_MARGIN = 8,
;;;   ON_RIGHT_MARGIN = 9, ON_VERTICAL_SCROLL_BAR = 10,
;;;   ON_HORIZONTAL_SCROLL_BAR = 11, ON_RIGHT_DIVIDER = 12,
;;;   ON_BOTTOM_DIVIDER = 13.

;;; Per-region dispatch — mirrors C-side imp-6.2 mlp_* decomposition.
;;; Each returns (values posn object string-info col row
;;;                    dx dy width height xret yret textpos).

(define (ml-dispatch-text-line-margin w part mx my)
  "Dispatch for text-area (1), mode/header/tab-line (2/4/5), and
margin (8/9) clicks."
  (cond
   ((= part 1)  ; ON_TEXT — just the text-area offset.
    (let ((xy ((force %--mlp-dispatch) 0 w mx my #nil #nil #nil)))
      (values #nil #nil #nil -1 -1 -1 -1 -1 -1
              (car xy) (cdr xy) 0)))
   ((or (= part 2) (= part 4) (= part 5))  ; ON_MODE_LINE / ON_HEADER_LINE / ON_TAB_LINE
    (call-with-values
        (lambda () (mode-header-line w part mx my))
      (lambda (p obj si c r dxv dyv wv hv xrv)
        (values p obj si c r dxv dyv wv hv xrv 0 -1))))
   (else  ; parts 8,9: margins
    (call-with-values
        (lambda () (margins w part mx my))
      (lambda (p obj si c r dxv dyv wv hv xrv yrv)
        (values p obj si c r dxv dyv wv hv xrv yrv 0))))))

(define (ml-dispatch-fringe-scroll w part mx my)
  "Dispatch for fringe (6/7) and border/scroll-bar/divider (3/10-13)
clicks."
  (cond
   ((= part 6)  ; ON_LEFT_FRINGE
    (call-with-values
        (lambda () (fringes w #t mx my))
      (lambda (p c dxv dyv xrv yrv)
        (values p #nil #nil c -1 dxv dyv -1 -1 xrv yrv 0))))
   ((= part 7)  ; ON_RIGHT_FRINGE
    (call-with-values
        (lambda () (fringes w #f mx my))
      (lambda (p c dxv dyv xrv yrv)
        (values p #nil #nil c -1 dxv dyv -1 -1 xrv yrv 0))))
   (else  ; parts 3,10,11,12,13: border/scroll-bar/dividers
    (call-with-values
        (lambda () (scroll-border w part mx my))
      (lambda (p wv dxv xrv dyv yrv)
        (values p #nil #nil -1 -1 dxv dyv wv -1 xrv yrv 0))))))

(define (ml-dispatch-window-part w part mx my)
  "Top-level window-part dispatcher."
  (if (or (= part 3) (= part 6) (= part 7) (>= part 10))
      (ml-dispatch-fringe-scroll w part mx my)
      (ml-dispatch-text-line-margin w part mx my)))

(define (ml-finish-window-position w part mx my xret yret posn object string-info
                                   textpos col row dx dy width height
                                   window-or-frame t)
  "Buffer-posn pass + image-hotspot + result assembly."
  (when (= textpos 0)
    (call-with-values
        (lambda () (buffer-posn-pass w part mx my xret posn))
      (lambda (tp p obj si c r dxv dyv wv hv)
        (set! textpos tp) (set! posn p)
        (when (eq? object #nil) (set! object obj))
        (set! string-info si)
        (when (< col 0)  (set! col c))
        (when (< row 0)  (set! row r))
        (when (< dx 0)   (set! dx dxv)  (set! dy dyv))
        (when (< width 0)  (set! width wv)  (set! height hv)))))
  (ml-assemble-position window-or-frame posn xret yret t
                        object string-info textpos col row dx dy
                        width height))

(define (ml-assemble-position window-or-frame posn xret yret t
                              object string-info textpos col row dx dy
                              width height)
  "Image-hotspot check + cons-chain result assembly."
  (set! posn (image-hotspot-check object dx dy posn))
  (let ((extra (cons (or string-info #nil)
                     (cons (if (< textpos 0) #nil textpos)
                           (cons (cons col row)
                                 (list (or object #nil)
                                       (cons dx dy)
                                       (cons width height)))))))
    (cons window-or-frame
          (cons posn
                (cons (cons xret yret)
                      (cons t extra))))))

(define (make-lispy-position f x y t)
  "Build a mouse-click position list from FRAME F and pixel coords X, Y.
See src/keyboard.c:6363–6667 (C original) and imp-6.3 decomposition."
  (let* ((mx x) (my y)
         (pre (frame-preamble f mx my))
         (window-or-frame (list-ref pre 0))
         (part (list-ref pre 1))
         (posn (list-ref pre 2)))
    (if ((force %windowp) window-or-frame)
        ;; Window click — dispatch on part, then finish.
        (call-with-values
            (lambda ()
              (ml-dispatch-window-part window-or-frame part mx my))
          (lambda (posn object string-info col row
                         dx dy width height xret yret textpos)
            (ml-finish-window-position
             window-or-frame part mx my xret yret posn object string-info
             textpos col row dx dy width height
             window-or-frame t)))
        ;; Frame / no-frame path — window-part dispatch not needed.
        (if f
            (list f (internal-border f mx my posn) (cons mx my) t)
            (let ((xret (if (eq? (track-mouse-value) 'drag-source) mx 0))
                  (yret (if (eq? (track-mouse-value) 'drag-source) my 0)))
              (list #nil posn (cons xret yret) t))))))
