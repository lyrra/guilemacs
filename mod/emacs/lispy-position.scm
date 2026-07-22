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

;;; Elisp globals / predicates.
(defelisp %symbol-value symbol-value)
;; track-mouse is a dynamic variable — read fresh each call.
(define (track-mouse-value)
  ((force %symbol-value) 'track-mouse))
(defelisp %windowp windowp)

;;; Per-region helpers — each calls (--mlp-dispatch region-id . args).

(define (image-hotspot-check object dx dy posn)
  ((force %--mlp-dispatch) 2 object dx dy posn #nil #nil))

(define (internal-border f x y posn)
  ((force %--mlp-dispatch) 1 f x y posn #nil #nil))

(define (frame-preamble f mx my)
  ((force %--mlp-dispatch) 3 (or f #nil) mx my (track-mouse-value) #nil #nil))

(define (fringes w left? mx my)
  (let ((res ((force %--mlp-dispatch) 4 w (if left? #t #nil) mx my #nil #nil)))
    (values (list-ref res 0) (list-ref res 1) (list-ref res 2)
            (list-ref res 3) (list-ref res 4) (list-ref res 5))))

(define (scroll-border w part mx my)
  (let ((res ((force %--mlp-dispatch) 5 w part mx my #nil #nil)))
    (values (list-ref res 0) (list-ref res 1) (list-ref res 2)
            (list-ref res 3) (list-ref res 4) (list-ref res 5))))

(define (mode-header-line w part mx my)
  (let ((res ((force %--mlp-dispatch) 6 w part mx my #nil #nil)))
    (values (list-ref res 0) (list-ref res 1) (list-ref res 2)
            (list-ref res 3) (list-ref res 4)
            (list-ref res 5) (list-ref res 6)
            (list-ref res 7) (list-ref res 8)
            (list-ref res 9))))

(define (margins w part mx my)
  (let ((res ((force %--mlp-dispatch) 7 w part mx my #nil #nil)))
    (values (list-ref res 0) (list-ref res 1) (list-ref res 2)
            (list-ref res 3) (list-ref res 4)
            (list-ref res 5) (list-ref res 6)
            (list-ref res 7) (list-ref res 8)
            (list-ref res 9) (list-ref res 10))))

(define (buffer-posn-pass w part mx my xret posn)
  (let ((res ((force %--mlp-dispatch) 8 w part mx my xret posn)))
    (values (list-ref res 0) (list-ref res 1) (list-ref res 2)
            (list-ref res 3)
            (list-ref res 4) (list-ref res 5)
            (list-ref res 6) (list-ref res 7)
            (list-ref res 8) (list-ref res 9))))

;;; 6.3.9 Orchestrator — replaces the C make_lispy_position body.
;;;
;;; Window-part enum values (must match src/keyboard.c):
;;;   ON_TEXT = 1, ON_MODE_LINE = 2, ON_HEADER_LINE = 3, ON_TAB_LINE = 4,
;;;   ON_LEFT_MARGIN = 5, ON_RIGHT_MARGIN = 6, ON_LEFT_FRINGE = 7,
;;;   ON_RIGHT_FRINGE = 8, ON_VERTICAL_BORDER = 9,
;;;   ON_VERTICAL_SCROLL_BAR = 10, ON_HORIZONTAL_SCROLL_BAR = 11,
;;;   ON_RIGHT_DIVIDER = 12, ON_BOTTOM_DIVIDER = 13.

;;; Per-region dispatch — mirrors C-side imp-6.2 mlp_* decomposition.
;;; Each returns (values posn object string-info col row
;;;                    dx dy width height xret yret textpos).

(define (ml-dispatch-text-line-margin w part mx my)
  "Dispatch for parts 1-6 (ON_TEXT, mode/header/tab, margins)."
  (cond
   ((= part 1)  ; ON_TEXT — just the text-area offset.
    (let ((xy ((force %--mlp-dispatch) 0 w mx my #nil #nil #nil)))
      (values #nil #nil #nil -1 -1 -1 -1 -1 -1
              (car xy) (cdr xy) 0)))
   ((or (= part 2) (= part 3) (= part 4))  ; mode/header/tab line
    (call-with-values
        (lambda () (mode-header-line w part mx my))
      (lambda (p obj si c r dxv dyv wv hv xrv)
        (values p obj si c r dxv dyv wv hv xrv 0 -1))))
   (else  ; parts 5,6: margins
    (call-with-values
        (lambda () (margins w part mx my))
      (lambda (p obj si c r dxv dyv wv hv xrv yrv)
        (values p obj si c r dxv dyv wv hv xrv yrv 0))))))

(define (ml-dispatch-fringe-scroll w part mx my)
  "Dispatch for parts 7+ (fringes, scroll-bar/border/dividers)."
  (cond
   ((= part 7)  ; left fringe
    (call-with-values
        (lambda () (fringes w #t mx my))
      (lambda (p c dxv dyv xrv yrv)
        (values p #nil #nil c -1 dxv dyv -1 -1 xrv yrv 0))))
   ((= part 8)  ; right fringe
    (call-with-values
        (lambda () (fringes w #f mx my))
      (lambda (p c dxv dyv xrv yrv)
        (values p #nil #nil c -1 dxv dyv -1 -1 xrv yrv 0))))
   (else  ; part >= 9: scroll-bar/border/dividers
    (call-with-values
        (lambda () (scroll-border w part mx my))
      (lambda (p wv dxv xrv dyv yrv)
        (values p #nil #nil -1 -1 dxv dyv wv -1 xrv yrv 0))))))

(define (ml-dispatch-window-part w part mx my)
  "Top-level window-part dispatcher."
  (if (<= part 6)
      (ml-dispatch-text-line-margin w part mx my)
      (ml-dispatch-fringe-scroll w part mx my)))

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
