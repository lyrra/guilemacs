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
  (let ((res ((force %--mlp-dispatch) 8 w part mx my xret posn #nil)))
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

(define (make-lispy-position f x y t)
  (let* ((mx x) (my y)                     ; frame-relative coords
         (pre (frame-preamble f mx my))
         (window-or-frame (list-ref pre 0))
         (part (list-ref pre 1))
         (posn (list-ref pre 2))
         ;; Shared locals matching C defaults.
         (object #nil) (string-info #nil)
         (textpos 0)
         (col -1) (row -1)
         (dx -1) (dy -1)
         (width -1) (height -1)
         (xret 0) (yret 0))

    (if ((force %windowp) window-or-frame)
        ;; Click inside a window — dispatch on part.
        (let ((w window-or-frame))
          (cond
           ((= part 1)  ; ON_TEXT
            (let ((xy ((force %--mlp-dispatch) 0 w mx my #nil #nil #nil)))
              (set! xret (car xy))
              (set! yret (cdr xy))))

           ((or (= part 2) (= part 3) (= part 4))  ; mode/header/tab line
            (call-with-values
                (lambda () (mode-header-line w part mx my))
              (lambda (p obj si c r dxv dyv wv hv xrv)
                (set! posn p)     (set! object obj)
                (set! string-info si)
                (set! col c)      (set! row r)
                (set! dx dxv)     (set! dy dyv)
                (set! width wv)   (set! height hv)
                (set! xret xrv)))
            (set! textpos -1))

           ((or (= part 5) (= part 6))  ; margins
            (call-with-values
                (lambda () (margins w part mx my))
              (lambda (p obj si c r dxv dyv wv hv xrv yrv)
                (set! posn p)     (set! object obj)
                (set! string-info si)
                (set! col c)      (set! row r)
                (set! dx dxv)     (set! dy dyv)
                (set! width wv)   (set! height hv)
                (set! xret xrv)   (set! yret yrv))))

           ((= part 7)  ; left fringe
            (call-with-values
                (lambda () (fringes w #t mx my))
              (lambda (p c dxv dyv xrv yrv)
                (set! posn p)     (set! col c)
                (set! dx dxv)     (set! dy dyv)
                (set! xret xrv)   (set! yret yrv))))

           ((= part 8)  ; right fringe
            (call-with-values
                (lambda () (fringes w #f mx my))
              (lambda (p c dxv dyv xrv yrv)
                (set! posn p)     (set! col c)
                (set! dx dxv)     (set! dy dyv)
                (set! xret xrv)   (set! yret yrv))))

           ((>= part 9)  ; scroll-bar/border/dividers
            (call-with-values
                (lambda () (scroll-border w part mx my))
              (lambda (p wv dxv xrv dyv yrv)
                (set! posn p)     (set! width wv)
                (set! dx dxv)     (set! xret xrv)
                (set! dy dyv)     (set! yret yrv)))))

          ;; Post-dispatch buffer-posn pass.
          (when (= textpos 0)
            (call-with-values
                (lambda () (buffer-posn-pass w part mx my xret posn))
              (lambda (tp p obj si c r dxv dyv wv hv)
                (set! textpos tp)
                (set! posn p)
                (when (eq? object #nil) (set! object obj))
                (set! string-info si)
                (when (< col 0)  (set! col c))
                (when (< row 0)  (set! row r))
                (when (< dx 0)   (set! dx dxv))
                (when (< dy 0)   (set! dy dyv))
                (when (< width 0)  (set! width wv))
                (when (< height 0) (set! height hv)))))

          ;; Image hotspot check.
          (set! posn (image-hotspot-check object dx dy posn))

          ;; Assemble result.
          (let ((extra (list (or object #nil)
                             (cons dx dy)
                             (cons width height))))
            (set! extra
                  (cons (or string-info #nil)
                        (cons (if (< textpos 0) #nil textpos)
                              (cons (cons col row) extra))))
            ;; cons-chain so extra_info splices into the tail
            ;; (matches C: Fcons(W, Fcons(P, Fcons((xy), Fcons(t, extra))))).
            (cons window-or-frame
                  (cons posn
                        (cons (cons xret yret)
                              (cons t extra))))))

        ;; Frame path (not inside a window).
        (if f
            (begin
              (set! xret mx)
              (set! yret my)
              (set! posn (internal-border f mx my posn))
              ;; Frame path — extra_info is Qnil, so 4-element list.
              (list f posn (cons xret yret) t))
            ;; No-frame / drag-source path.
            (begin
              (when (eq? (track-mouse-value) 'drag-source)
                (set! xret mx)
                (set! yret my))
              ;; No-frame / drag-source — extra_info is Qnil, 4-element list.
              (list #nil posn (cons xret yret) t))))))
