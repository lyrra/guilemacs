;;; test-m22-imp3.scm --- M22 imp-3 parity corpus.
;;;
;;; imp-3 ports four independent pieces of C keyboard logic to Scheme:
;;;   * adjust-point-for-property   -> (emacs command-loop)
;;;   * set-input-interrupt-mode / set-output-flow-control /
;;;     set-input-meta-mode / set-quit-char -> (emacs read-key-sequence)
;;;   * some-mouse-moved / tracking-off / internal-track-mouse
;;;     -> (emacs read-key-sequence)
;;;   * stuff_buffered_input       -> (emacs kbd-buffer) stuff-buffered-input
;;;
;;; The C DEFUNs are now thin dispatchers; these tests exercise the
;;; Scheme bodies directly and via the (repointed) C entry points.
;;;
;;; Sourced by test/keyboard/test-m22-imp3.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  Same harness as test-m22-input-pending.scm.

(use-modules (emacs read-key-sequence))
(use-modules (emacs command-loop))
(use-modules (emacs kbd-buffer))
(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())
(define (report name status)
  (set! test-results (cons (list name status) test-results)))
(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name) (symbol-function name))
(define (try-check name expected thunk)
  (catch #t
    (lambda () (check name expected (thunk)))
    (lambda (key . args)
      (report name (list 'ERROR key args)))))
(define ASCII-KEYSTROKE-EVENT (@@ (emacs kbd-buffer) ASCII-KEYSTROKE-EVENT))
(define NON-ASCII-KEYSTROKE-EVENT (@@ (emacs kbd-buffer) NON-ASCII-KEYSTROKE-EVENT))

;; kbd-buffer seeding shims (same set as test-m14-predicates / -m22-input-pending).
(define %fetch      (delay (%sym '--kbd-fetch-ptr-index)))
(define %store      (delay (%sym '--kbd-store-ptr-index)))
(define %set-fetch  (delay (%sym '--kbd-set-fetch-ptr-index)))
(define %set-store  (delay (%sym '--kbd-set-store-ptr-index)))
(define %mk-event   (delay (%sym '--ie-test-event)))
(define %store-ev   (delay (%sym '--kbd-store-buffered-event)))
(define %input-pending (delay (%sym '--rc-input-pending)))

;;; ---------------------------------------------------------------------
;;; 1. New C shims all resolve.
;;;
(define new-shims
  '(--decode-tty-terminal-p --tty-flow-control --tty-flow-control-set!
    --tty-meta-key --tty-meta-key-set! --reset-sys-modes --init-sys-modes
    --reset-all-sys-modes --init-all-sys-modes --controlling-tty-meta-key
    --reset-controlling-tty-sys-modes --init-controlling-tty-sys-modes
    --quit-char-set! --sigio-or-poll-usable-p --x-display-forces-interrupt-p
    --interrupt-input-set! --start-polling --track-mouse --track-mouse-set!
    --frame-mouse-moved-p --stuff-char --stuff-string --input-pending-set!
    --composition-adjust-point --display-prop-intangible-p
    --frame-list-raw point-byte))
(for-each (lambda (n)
            (check (string-append "m22/imp3/shims/" (symbol->string n))
                   #t (procedure? (%sym n))))
          new-shims)

;;; ---------------------------------------------------------------------
;;; 2. Input-mode quartet — batch (no tty) paths.
;;;
;;; In the noninteractive harness the selected frame is not a tty, so
;;; decode_tty_terminal (nil) is NULL and each setter returns nil without
;;; touching the terminal.  set-quit-char has no controlling tty, so it
;;; returns nil without validating QUIT (matching the C !t-first order).
;;; The interrupt_input global is saved/restored so the corpus leaves no
;;; persistent input-mode side effect for later test files.
(define saved-interrupt-input ((%c '--interrupt-input-p)))
(check "m22/imp3/decode-tty/nil" #nil ((%c '--decode-tty-terminal-p) #nil))
(check "m22/imp3/set-output-flow-control/nil-tty"
       #nil (set-output-flow-control #t #nil))
(check "m22/imp3/set-input-meta-mode/nil-tty"
       #nil (set-input-meta-mode 'encoded #nil))
(check "m22/imp3/set-input-interrupt-mode/returns-nil"
       #nil (set-input-interrupt-mode #t))
(check "m22/imp3/controlling-tty-meta-key/no-tty"
       #nil ((%c '--controlling-tty-meta-key)))
;; No controlling tty -> no ASCII-char validation even for invalid QUIT.
(check "m22/imp3/set-quit-char/no-tty-invalid-no-error"
       #nil (set-quit-char 1000))
(check "m22/imp3/set-quit-char/no-tty-valid"
       #nil (set-quit-char 7))
;; The generic set-input-mode entry (which routes through the four
;; setters) still works.
(check "m22/imp3/set-input-mode/batch" #nil (set-input-mode #t #nil 'encoded #nil))
((%c '--interrupt-input-set!) saved-interrupt-input)

;;; ---------------------------------------------------------------------
;;; 3. track-mouse trio.
;;;
;;; some-mouse-moved is a pure reader over the C track_mouse cell + the
;;; per-frame mouse_moved flag.  In batch no frame reports movement, so
;;; it is nil; the interesting logic (guard + per-frame scan) is
;;; exercised via --track-mouse-set! and internal-track-mouse's
;;; enable/restore.
(define saved-track-mouse ((%c '--track-mouse)))
(dynamic-wind
  (lambda () #f)
  (lambda ()
    ((%c '--track-mouse-set!) #nil)
    (check "m22/imp3/some-mouse-moved/track-off" #nil (some-mouse-moved)))
  (lambda () ((%c '--track-mouse-set!) saved-track-mouse)))

(dynamic-wind
  (lambda () #f)
  (lambda ()
    ((%c '--track-mouse-set!) #t)
    (check "m22/imp3/some-mouse-moved/track-on-no-motion" #nil (some-mouse-moved)))
  (lambda () ((%c '--track-mouse-set!) saved-track-mouse)))

;; track-mouse-set! / --track-mouse roundtrip.
(dynamic-wind
  (lambda () #f)
  (lambda ()
    ((%c '--track-mouse-set!) #nil)
    (check "m22/imp3/track-mouse-set/nil-readback" #nil ((%c '--track-mouse)))
    ((%c '--track-mouse-set!) #t)
    (check "m22/imp3/track-mouse-set/t-readback" #t ((%c '--track-mouse))))
  (lambda () ((%c '--track-mouse-set!) saved-track-mouse)))

;; internal-track-mouse enables tracking during BODYFUN and restores it
;; afterwards.  We start with track_mouse non-nil so the restore path is
;; tracking-off with a non-nil old value — avoiding the get-input-pending!
;; / gobble-input branch (reading stdin in batch can spuriously record a
;; key into recent-keys and trip the m3-recent-keys ERT tests).
(dynamic-wind
  (lambda () #f)
  (lambda ()
    ((%c '--track-mouse-set!) #t)
    (let ((during 'unset))
      ((%sym 'internal--track-mouse)
       (lambda ()
         (set! during ((%c '--track-mouse)))
         #t))
      (check "m22/imp3/internal-track-mouse/during" #t during)
      (check "m22/imp3/internal-track-mouse/after-restored"
             #t ((%c '--track-mouse)))))
  (lambda () ((%c '--track-mouse-set!) saved-track-mouse)))

;;; ---------------------------------------------------------------------
;;; 4. stuff-buffered-input.
;;;
;;; Drains every event between fetch and store, clearing each slot and
;;; leaving fetch == store with input_pending false.  A pending
;;; NON-ASCII keystroke event is cleared without being stuffed, so it
;;; can be seeded safely in batch (no tty write).  The ring cursors are
;;; restored afterwards.
(let ((saved-fetch ((force %fetch)))
      (saved-store ((force %store)))
      (ie ((force %mk-event) NON-ASCII-KEYSTROKE-EVENT 65 0 #nil)))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((force %set-fetch) saved-fetch)
      ((force %set-store) saved-fetch)
      ((force %store-ev) ie #nil)
      (check "m22/imp3/stuff-buffered-input/non-ascii-pending-before"
             (modulo (+ saved-fetch 1) 4096) ((force %store)))
      (stuff-buffered-input #nil)
      (check "m22/imp3/stuff-buffered-input/non-ascii-drained-fetch"
             ((force %store)) ((force %fetch)))
      (check "m22/imp3/stuff-buffered-input/input-pending-cleared"
             #nil ((force %input-pending))))
    (lambda () ((force %set-fetch) saved-fetch)
               ((force %set-store) saved-store))))

;; Empty ring + nil stuffstring: no-op drain.
(let ((saved-fetch ((force %fetch)))
      (saved-store ((force %store))))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      ((force %set-fetch) saved-fetch)
      ((force %set-store) saved-fetch)
      (stuff-buffered-input #nil)
      (check "m22/imp3/stuff-buffered-input/empty-fetch-eq-store"
             ((force %store)) ((force %fetch)))
      (check "m22/imp3/stuff-buffered-input/empty-input-pending-cleared"
             #nil ((force %input-pending))))
    (lambda () ((force %set-fetch) saved-fetch)
               ((force %set-store) saved-store))))

;;; ---------------------------------------------------------------------
;;; 5. adjust-point-for-property — invisible region skip.
;;;
;;; Deterministic text-property case: mark positions 4..6 (chars d,e,f)
;;; invisible.  Point inside the region must be moved out to its end
;;; (the beg<PT && end>PT path, which needs no get-pos-property — that
;;; primitive returns nil for a nil OBJECT in this build, faithfully
;;; matching C).  Point outside the region is left alone.  Works in
;;; batch because the invisible lookups use a Qnil window (buffer text
;;; properties), not the selected window.
(let* ((buf ((%c 'current-buffer))))
  ((%c 'erase-buffer))
  ((%c 'insert) "abcdefghi")
  ;; put invisible on buffer chars 4..6 (0-based d,e,f -> positions 4,5,6)
  ((%c 'put-text-property) 4 7 'invisible #t)
  ((%c 'goto-char) 5)
  (adjust-point-for-property 5 #f)
  (check "m22/imp3/adjust-point/invisible-inside-moved" 7 ((%c 'point)))
  ((%c 'goto-char) 2)
  (adjust-point-for-property 2 #f)
  (check "m22/imp3/adjust-point/not-invisible-unchanged" 2 ((%c 'point))))

;;; cr.org Finding 1 regression: invisible text reaching BEGV.  The
;;; backward scan must check (> b (point-min)) BEFORE reading the
;;; property at (b-1); otherwise it reads one position before BEGV and
;;; get-char-property-and-overlay signals args-out-of-range.  Invisible
;;; on positions 1..3 reaches BEGV=1; a point inside the region must
;;; move to its end (4) without erroring.
(let* ((buf ((%c 'current-buffer))))
  ((%c 'erase-buffer))
  ((%c 'insert) "abcdefghi")
  ((%c 'put-text-property) 1 4 'invisible #t)
  ((%c 'goto-char) 2)
  (adjust-point-for-property 2 #f)
  (check "m22/imp3/adjust-point/invisible-to-begv" 4 ((%c 'point))))

;;; ---------------------------------------------------------------------
;;; 5a. cr.org Finding 1: some-mouse-moved must scan the RAW Vframe_list,
;;; not the `frame-list' primitive (which drops tooltip frames and
;;; reverses order).  We cannot set the C mouse_moved bit from Scheme, so
;;; this checks the raw-list shim resolves, is a proper list of frames,
;;; and agrees with `frame-list' when no tooltip frame exists (batch).
(define (list-of-frames? xs)
  (cond ((null? xs) #t)
        ((not (pair? xs)) #f)
        ((eqv? #t ((%c 'frame-live-p) (car xs)))
         (list-of-frames? (cdr xs)))
        (else #f)))
;; same-member check (order- and direction-independent): every live frame
;; in RAW appears in `frame-list' and vice versa.  Robust whether or not
;; Fframe_list reverses/tooltip-filters (that branch is HAVE_WINDOW_SYSTEM
;; dependent).
(define (same-frame-set? a b)
  (or (and (null? a) (null? b))
      (and (pair? a)
           (let ((x (car a)))
             (and (memq x b) (same-frame-set? (cdr a) (delq x b)))))))
(let* ((raw ((%c '--frame-list-raw))))
  (check "m22/imp3/frame-list-raw/is-proper-frame-list"
         #t (list-of-frames? raw))
  ;; batch has no tooltip frame, so RAW and `frame-list' hold the same
  ;; frames; RAW is the forward-order Vframe_list copy (cr.org Finding 1).
  (check "m22/imp3/frame-list-raw/same-frames-as-frame-list"
         #t (same-frame-set? raw ((%c 'frame-list)))))

;;; point-byte (restored standard primitive) — value-tested, not just
;;; existence: in an all-ASCII buffer the byte position equals the
;;; character position.
(let* ((buf ((%c 'current-buffer))))
  ((%c 'erase-buffer))
  ((%c 'insert) "abcdefghi")
  ((%c 'goto-char) 5)
  (check "m22/imp3/point-byte/ascii-equals-charpos" 5 ((%c 'point-byte))))

;;; ---------------------------------------------------------------------
;;; 5b. adjust-point-for-property — display branch (cr.org Finding 2).
;;;
;;; A `display' string property is intangible: point inside the region
;;; must move to the region end (when point moved forward) or the
;;; region start (when point moved backward), matching the C
;;; adjust_point_for_property display branch.
(let* ((buf ((%c 'current-buffer))))
  ((%c 'erase-buffer))
  ((%c 'insert) "abcdefghi")
  ;; display property on chars d,e,f (positions 4..6, region [4,7)).
  ((%c 'put-text-property) 4 7 'display "XX")
  ;; forward: point moved forward (pt=5 > last-pt=2) -> region end 7.
  ((%c 'goto-char) 5)
  (try-check "m22/imp3/adjust-point/display-fwd/pt0" 5 (lambda () ((%c 'point))))
  (try-check "m22/imp3/adjust-point/display-fwd/adjust" 7
             (lambda () (adjust-point-for-property 2 #f) ((%c 'point))))
  (try-check "m22/imp3/adjust-point/display-fwd/after" 7 (lambda () ((%c 'point))))
  ;; backward: point moved backward (pt=5 < last-pt=8) -> region start 4.
  ((%c 'goto-char) 5)
  (try-check "m22/imp3/adjust-point/display-back/adjust" 4
             (lambda () (adjust-point-for-property 8 #f) ((%c 'point))))
  (try-check "m22/imp3/adjust-point/display-back/after" 4 (lambda () ((%c 'point)))))

;;; 5b2. display branch — zero-length display string (cr.org Finding 2).
;;; A `display' property whose value is the empty string is still
;;; intangible, and the (beg <= PT) + (string? val) + (= 0 length) clause
;;; fires.  In this build get_property_and_range (C and Scheme alike)
;;; derives the region start via previous-single-property-change, which
;;; returns BEGV when point sits on the region's first char, so the
;;; move clamps to (max (beg-1) BEGV) = 1.  Assert that exact parity
;;; value so a divergence in the range-finding is caught.
(let* ((buf ((%c 'current-buffer))))
  ((%c 'erase-buffer))
  ((%c 'insert) "abcdefghi")
  ((%c 'put-text-property) 4 7 'display "")
  (check "m22/imp3/adjust-point/display-empty-intangible"
         #t ((%c '--display-prop-intangible-p) "" #nil 4 4))
  ((%c 'goto-char) 4)
  (try-check "m22/imp3/adjust-point/display-empty-string/beg-clamp"
             1 (lambda () (adjust-point-for-property 8 #f) ((%c 'point))))
  (try-check "m22/imp3/adjust-point/display-empty-string/after"
             1 (lambda () ((%c 'point)))))

;;; ---------------------------------------------------------------------
;;; 5c. adjust-point-for-property — invisible "pretend area doesn't
;;; exist" round-trip (cr.org Finding 2).  An invisible region whose
;;; start equals last-pt and whose end equals PT triggers the
;;; (last-pt == beg) && (PT == end) clause, which moves point one past
;;; the region (end+1) so the area is skipped as if it were not there.
(let* ((buf ((%c 'current-buffer))))
  ((%c 'erase-buffer))
  ((%c 'insert) "abcdefghi")
  ;; invisible on positions 2..6 (chars b..f); region [2,7).
  ((%c 'put-text-property) 2 7 'invisible #t)
  ((%c 'goto-char) 4)
  (try-check "m22/imp3/adjust-point/invisible-boundary-roundtrip"
             8 (lambda () (adjust-point-for-property 2 #f) ((%c 'point))))
  (try-check "m22/imp3/adjust-point/invisible-boundary-roundtrip/after"
             8 (lambda () ((%c 'point)))))

;;; ---------------------------------------------------------------------
;;; 6. The corpus must not pollute the recent-keys ring: m3-recent-keys
;;; ERT tests assert the ring is empty at batch startup.
(check "m22/imp3/recent-keys-ring-empty-after"
       0 ((%c 'length) ((%c 'recent-keys))))
