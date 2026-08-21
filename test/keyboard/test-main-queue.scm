;;; test-main-queue.scm --- M12 imp-3 test corpus for (emacs main-queue)
;;;
;;; Sourced by test/keyboard/test-main-queue.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch
;;; stdout.
;;;
;;; No-blocking cases only; the real blocking read + the C-g smoke gate
;;; are imp-6 / the smoke gate.  The batch fast-path never fires here
;;; because every read is driven through a Vunread break (the first
;;; check of kbd-buffer-get-event outranks the noninteractive fast
;;; path), so `noninteractive` is left at its batch default (t) —
;;; which is exactly what the batch-EOF kill test needs.
;;;
;;; Environment facts relied on (probed):
;;;   - #nil is a distinct object (≠ () and ≠ #f): every C DEFUN result
;;;     carrying elisp truthiness goes through the truthy? idiom, and
;;;     nil matches are (eq? x #nil).
;;;   - The tty shims deref FRAME_TTY unguarded (Risk 4): calling
;;;     --selected-frame-tty-meta-key on this non-tty batch frame
;;;     segfaults.  The decode-branch tests therefore stub the tty gate
;;;     shims inside (emacs main-queue) (raw-text branch never touches
;;;     the decode shim), and the real-shim tests only feed ASCII bytes
;;;     that read-decoded itself gates — deterministic on every frame.
;;;   - A compiled (emacs main-queue).go in the Guile ccache inlines the
;;;     module's references to its own top-level bindings, so the
;;;     with-stubbed-refs rebinds would be invisible inside the module
;;;     (the fix.org trap: same failure as test-kbd-wait-loop.scm §8).
;;;     The load-main-queue-interpreted! recipe below therefore loads
;;;     the module interpretively before any test runs; the rebinds then
;;;     land (verified: event=-2 side-queue routing with stubbed
;;;     kboard-eq under an interpreted load).

(use-modules (emacs elisp-ref))      ; only for the load recipe below

;; Force `(use-modules (emacs main-queue))' to load the module
;; INTERPRETED, so runtime rebinds of its delayed DEFUN refs take
;; effect.  With the module compiled (.go in the ccache), Guile inlines
;; the module's references to its top-level bindings and the rebinds
;; are dead (fix.org).  Recipe: drop the compiled path and the ccache
;; fallback, disable auto-compilation, load, then restore.  The module
;; table keeps the interpreted module for the rest of the process.
(define (load-main-queue-interpreted!)
  (let ((saved-path %load-compiled-path)
        (saved-fallback %compile-fallback-path)
        (saved-should %load-should-auto-compile))
    (dynamic-wind
      (lambda ()
        (set! %load-compiled-path '())
        (set! %compile-fallback-path #f)
        (set! %load-should-auto-compile #f))
      (lambda () (use-modules (emacs main-queue)))
      (lambda ()
        (set! %load-compiled-path saved-path)
        (set! %compile-fallback-path saved-fallback)
        (set! %load-should-auto-compile saved-should)))))

(load-main-queue-interpreted!)

(use-modules (emacs event-modifiers))  ; ctrl-modifier (mask test)

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

(define (truthy? x)
  (not (eq? x #nil)))

;; Length of an elisp list (terminated by #nil, not '()).  Plain
;; `length' happens to accept these too — `(null? #nil)' is #t in this
;; runtime — but the explicit #nil check keeps the intent visible.
(define (elist-length l)
  (let loop ((l l) (n 0))
    (if (eq? l #nil) n (loop (cdr l) (+ n 1)))))

;; Run THUNK with (emacs main-queue)'s internal delayed DEFUN refs
;; rebound to the given (name . proc) pairs; restore afterwards.
;; Uses module-variable indirection: the `@@' syntax form requires a
;; literal identifier and cannot take a computed (car entry), and
;; resolve-module + variable-ref works on names computed at runtime.
;; NOTE: the stubs only take effect while the module is interpreted.
;; A compiled .go in the Guile ccache inlines the module's own
;; references to its top-level bindings, so the rebind is invisible to
;; the module internals (same trap as test-kbd-wait-loop.scm §8,
;; fix.org).  The harness loads this corpus through the embedded
;; interpreter, so the rebinds land; keep the suite in --batch and do
;; not rely on this pattern for C-shim behavior under a compiled load.
(define (with-stubbed-refs stubs thunk)
  (let* ((mod (resolve-module '(emacs main-queue)))
         (saved
          (map (lambda (entry)
                 (let ((var (module-variable mod (car entry))))
                   (cons var (variable-ref var))))
               stubs)))
    (dynamic-wind
      (lambda ()
        (for-each (lambda (entry)
                    (variable-set! (module-variable mod (car entry))
                                   (delay (cdr entry))))
                  stubs))
      thunk
      (lambda ()
        (for-each (lambda (entry)
                    (variable-set! (car entry) (cdr entry)))
                  saved)))))

;; Push (list EVENT ...) onto unread-command-events as an elisp list
;; (the Vunread break consumes it one event per kbd-buffer-get-event
;; call), then restore the previous value afterwards.
(define (with-unread events thunk)
  (let ((saved (symbol-value 'unread-command-events)))
    (dynamic-wind
      (lambda ()
        (set-symbol-value! 'unread-command-events
                           (let loop ((es events))
                             (if (null? es)
                                 #nil
                                 (cons (car es) (loop (cdr es)))))))
      thunk
      (lambda ()
        (set-symbol-value! 'unread-command-events saved)))))

;;; --- 1. Registration -------------------------------------------------

(check "registration/read-event" #t (procedure? read-event-from-main-queue))
(check "registration/read-decoded" #t (procedure? read-decoded-event-from-main-queue))

;;; --- 2. Deadline check (rec-free, --timespec-expired-p) --------------

;; Expired pointer → read-event returns (values #nil #nil) immediately,
;; without touching kbd-buffer-get-event (no Vunread needed, no block).
(let ((expired-ptr ((%sym '--rc-test-expired-end-time-ptr))))
  (call-with-values
      (lambda () (read-event-from-main-queue expired-ptr 'deadline-tag))
    (lambda (event umm)
      (check "deadline/expired-event" #nil event)
      (check "deadline/expired-umm" #nil umm))))

;; Far-future pointer: the shim itself says not-expired; do NOT call
;; read-event with it (the untimed read would sleep until year 2038).
(check "deadline/far-future-shim" #nil
       ((%sym '--timespec-expired-p) ((%sym '--rc-test-far-future-end-time-ptr))))
(check "deadline/expired-shim" #t
       (truthy? ((%sym '--timespec-expired-p) ((%sym '--rc-test-expired-end-time-ptr)))))

;;; --- 3. getctag dynamic-wind bracket ----------------------------------

;; The after-thunk must restore getctag after the read (Risk 1): the
;; read sets it to local-tag, the bracket restores the pre-read value.
(let ((sentinel 'pre-read-sentinel))
  (dynamic-wind
    (lambda () #f)
    (lambda ()
      (with-unread '(97)
        (lambda ()
          ((%sym '--set-ctag) sentinel)
          (call-with-values
              (lambda () (read-event-from-main-queue #nil 'during-tag))
            (lambda (event umm)
              (check "ctag/read-returns" 97 event)
              (check "ctag/restored" sentinel ((%sym '--get-ctag))))))))
    (lambda () ((%sym '--set-ctag) #nil))))

;;; --- 4. Standard keystroke passthrough -------------------------------

;; read-event: Vunread drain → the fixnum event, unchanged, umm nil.
(with-unread '(97)
  (lambda ()
    (call-with-values
        (lambda () (read-event-from-main-queue #nil 'tag))
      (lambda (event umm)
        (check "keystroke/read-event" 97 event)
        (check "keystroke/umm" #nil umm)))))

;; read-decoded: on a non-tty frame (or when the coding needs no
;; decoding) the gate short-circuits and the event passes through; on a
;; real decoding tty the single ASCII byte still decodes to itself.
;; Either way the result is 97 and the queue is drained.
(with-unread '(97)
  (lambda ()
    (call-with-values
        (lambda () (read-decoded-event-from-main-queue #nil 'tag #nil))
      (lambda (event umm)
        (check "keystroke/read-decoded" 97 event)
        (check "keystroke/read-decoded-umm" #nil umm)))))

;;; --- 5. extra_keyboard_modifiers fold (C :3191-3203) -----------------

;; The modifier mask: ~0xff7f & ~CHAR_CTL == #xfbff0080 (brief: verify
;; the constant; 32-bit window — Scheme lognot is infinite-precision).
(check "modifiers/mask" #xfbff0080
       (logand (lognot #xff7f) (lognot ctrl-modifier) #xffffffff))

;; ctrl path: extra's CHAR_CTL bit set → make-ctrl-char ('a' → C-a = 1).
;; The mask is ~0xff7f & ~CHAR_CTL (C :3191-3203), which EXCLUDES the
;; ctrl bit itself, so the fold is 1 | 0 = 1 (not #x4000001 — the
;; modifiers/mask check above already shows bit 26 is cleared).
(with-unread '(97)
  (lambda ()
    (let ((saved (symbol-value 'extra-keyboard-modifiers)))
      (dynamic-wind
        (lambda () (set-symbol-value! 'extra-keyboard-modifiers #x4000000))
        (lambda ()
          (call-with-values
              (lambda () (read-event-from-main-queue #nil 'tag))
            (lambda (event umm)
              (check "modifiers/ctrl-fold" 1 event))))
        (lambda () (set-symbol-value! 'extra-keyboard-modifiers saved))))))

;; meta path: extra's CHAR_META bit survives the mask → 97 | 0x8000000.
(with-unread '(97)
  (lambda ()
    (let ((saved (symbol-value 'extra-keyboard-modifiers)))
      (dynamic-wind
        (lambda () (set-symbol-value! 'extra-keyboard-modifiers #x8000000))
        (lambda ()
          (call-with-values
              (lambda () (read-event-from-main-queue #nil 'tag))
            (lambda (event umm)
              (check "modifiers/meta-fold" #x8000061 event))))
        (lambda () (set-symbol-value! 'extra-keyboard-modifiers saved))))))

;; low-byte path: extra keeps bit 7 (0x80) through the mask
;; (0xff7f clears bits 0-6 and 8-15, not bit 7) → 97 | 0x80.
(with-unread '(97)
  (lambda ()
    (let ((saved (symbol-value 'extra-keyboard-modifiers)))
      (dynamic-wind
        (lambda () (set-symbol-value! 'extra-keyboard-modifiers #xff))
        (lambda ()
          (call-with-values
              (lambda () (read-event-from-main-queue #nil 'tag))
            (lambda (event umm)
              (check "modifiers/low-byte-fold" #xe1 event))))
        (lambda () (set-symbol-value! 'extra-keyboard-modifiers saved))))))

;;; --- 6. Batch-EOF kill (C :3187-3189) --------------------------------

;; noninteractive is t in batch; a negative fixnum event must call
;; (kill-emacs 1 nil) through a recording wrapper.  The %kill-emacs
;; delay is only forced on this path, and this is the first negative
;; event in the corpus, so rebinding the elisp function slot catches
;; it.  After the (never-returning) kill, C continues to the fold —
;; mirror that: the call still returns the folded event.
(let ((recorded #f)
      (saved-kill (symbol-function 'kill-emacs)))
  (dynamic-wind
    (lambda ()
      (set-symbol-function! 'kill-emacs
                            (lambda args (set! recorded args))))
    (lambda ()
      (with-unread '(-3)
        (lambda ()
          (call-with-values
              (lambda () (read-event-from-main-queue #nil 'tag))
            (lambda (event umm)
              (check "batch-eof/kill-args" '(1 #nil) recorded)
              (check "batch-eof/returns" -3 event)))))
      (check "batch-eof/recorder-called" #t (not (eq? recorded #f))))
    (lambda ()
      (set-symbol-function! 'kill-emacs saved-kill))))

;;; --- 7. Side-queue routing (C :3165-3185) ----------------------------

;; Batch has a single kboard, so kb != current_kboard cannot arise from
;; a real event (ertest-kboard.el: "Batch mode has a single kboard").
;; Stub kboard-eq → nil (as if the event belonged to another kboard)
;; and single-kboard-p → nil (any-kboard mode): the routing must append
;; the event to the kboard's side queue and return the -2
;; wrong-kboard sentinel.  The append itself stays in C
;; (--kbd-enqueue-side-queue, imp-1.2 — covered by test-m12-shims.scm);
;; here we read the append back via kboard-kbd-queue and
;; --rc-pop-current-kboard-queue.
(let* ((kb ((%sym 'current-kboard)))
       (saved-queue ((%sym 'kboard-kbd-queue) kb)))
  (dynamic-wind
    (lambda () ((%sym 'set-kboard-kbd-queue) kb #nil))
    (lambda ()
      (with-stubbed-refs
        `((%kboard-eq . ,(lambda (a b) #nil))
          (%--kbd-single-kboard-p . ,(lambda () #nil)))
        (lambda ()
          (with-unread '(x)
            (lambda ()
              (call-with-values
                  (lambda () (read-event-from-main-queue #nil 'tag))
                (lambda (event umm)
                  (check "side-queue/returns-minus2" -2 event)
                  (check "side-queue/umm" #nil umm)))
              (check "side-queue/appended" 'x
                     (car ((%sym 'kboard-kbd-queue) kb)))
              (check "side-queue/flag-pops" 'x
                     ((%sym '--rc-pop-current-kboard-queue)))
              (check "side-queue/drained" #nil
                     ((%sym 'kboard-kbd-queue) kb)))))))
    (lambda () ((%sym 'set-kboard-kbd-queue) kb saved-queue))))

;;; --- 8. Decode gate (C :3241-3250) -----------------------------------

;; prev_event == Qt suppresses decoding even when the frame is a
;; decoding tty (raw xterm byte reads).  Stub the gate true; the
;; prev-event check alone must short-circuit to the raw event.
(with-stubbed-refs
  `((%--selected-frame-tty-p . ,(lambda () #t))
    (%--tty-keyboard-coding-requires-decoding-p . ,(lambda () #t)))
  (lambda ()
    (with-unread '(97)
      (lambda ()
        (call-with-values
            (lambda () (read-decoded-event-from-main-queue #nil 'tag #t))
          (lambda (event umm)
            (check "decode-gate/prev-event-t" 97 event)))))))

;;; --- 9. raw-text branch (C :3262-3277) -------------------------------

;; raw-text strips the high bit in Scheme and never loops.  The tty
;; shims are stubbed; the raw-text branch never calls the decode shim,
;; so no FRAME_TTY deref (Risk 4).  meta-key==0 (input-meta-mode nil):
;; 0x8D is below the 0x100 byte threshold (meta-key==1 would cap it at
;; 0x80 and treat 0x8D as a non-byte), so it is stripped → 0x0D.
(with-stubbed-refs
  `((%--selected-frame-tty-p . ,(lambda () #t))
    (%--tty-keyboard-coding-requires-decoding-p . ,(lambda () #t))
    (%--selected-frame-tty-meta-key . ,(lambda () 0))
    (%--tty-keyboard-coding-raw-text-p . ,(lambda () #t)))
  (lambda ()
    (with-unread '(141)              ; 0x8D
      (lambda ()
        (call-with-values
            (lambda () (read-decoded-event-from-main-queue #nil 'tag #nil))
          (lambda (event umm)
            (check "raw-text/meta1-strip" #x0d event)
            (check "raw-text/queue-drained" #nil
                   (symbol-value 'unread-command-events))))))))

;; meta-key==2: no strip (input-meta-mode encoded → bytes pass through).
(with-stubbed-refs
  `((%--selected-frame-tty-p . ,(lambda () #t))
    (%--tty-keyboard-coding-requires-decoding-p . ,(lambda () #t))
    (%--selected-frame-tty-meta-key . ,(lambda () 2))
    (%--tty-keyboard-coding-raw-text-p . ,(lambda () #t)))
  (lambda ()
    (with-unread '(141)
      (lambda ()
        (call-with-values
            (lambda () (read-decoded-event-from-main-queue #nil 'tag #nil))
          (lambda (event umm)
            (check "raw-text/meta2-nostrip" #x8d event)))))))

;; meta-key==3: strip + meta-modifier on the 8th bit (Scheme side of
;; the raw-text contract — the shim owns it for the real-decode path).
(with-stubbed-refs
  `((%--selected-frame-tty-p . ,(lambda () #t))
    (%--tty-keyboard-coding-requires-decoding-p . ,(lambda () #t))
    (%--selected-frame-tty-meta-key . ,(lambda () 3))
    (%--tty-keyboard-coding-raw-text-p . ,(lambda () #t)))
  (lambda ()
    (with-unread '(141)
      (lambda ()
        (call-with-values
            (lambda () (read-decoded-event-from-main-queue #nil 'tag #nil))
          (lambda (event umm)
            (check "raw-text/meta3-modifier" #x800000d event)))))))

;;; --- 10. Real decode via the stubbed shim ----------------------------

;; The decode branches (gate → byte accumulation → shim decode →
;; emit-and-unread) cannot run on a non-tty batch frame with the REAL
;; shims (Risk 4: --selected-frame-tty-meta-key derefs FRAME_TTY
;; unguarded → segfault).  These tests stub the tty gate true and the
;; decode shim to fixed decoded lists, exercising the full path:
;;   - decode-shim/returns-first: two bytes → shim returns a decoded
;;     ELISP list (Fcons-built, #nil-terminated — the exact shape
;;     --tty-decode-keyboard-bytes returns, keyboard.c:5281-5293); the
;;     first decoded event is returned and the rest go to
;;     unread-command-events in forward order (emit-and-unread reverses
;;     the tail — review cr.org F1).
;;   - decode-shim/incomplete-continues: the shim reports incomplete
;;     (#nil) after the first byte → read-decoded re-reads; once two
;;     bytes are accumulated the shim decodes → 233 returned.
;;   - decode-shim/flush-16: the shim NEVER completes → at n == 16 the
;;     accumulator flushes (Risk 5): first raw byte returned, 15
;;     unread — emit-and-unread of a Scheme-list tail.
;; The stubs land because the corpus loads (emacs main-queue)
;; interpretively (load-main-queue-interpreted! above).

;; Build an elisp list (terminated by #nil) from Scheme ELEMS — the
;; shape the decode shim returns after Fcons/Fnreverse.
(define (elisp-list . elems)
  (let loop ((es (reverse elems)) (acc #nil))
    (if (null? es) acc (loop (cdr es) (cons (car es) acc)))))

;; Forward-order check: UNREAD (an elisp list) must equal (ELEM ...).
(define (elisp-list-equal? unread elems)
  (equal? (let loop ((l unread) (acc '()))
            (if (eq? l #nil) (reverse acc) (loop (cdr l) (cons (car l) acc))))
          elems))

;; Stubbed decode shim shared by the continue/non-byte tests: decode =
;; identity over the accumulated bytes, but never complete before 2
;; bytes (drives the continue re-read).  The n == 16 flush test uses
;; its own always-incomplete stub below.
(define (fake-decode-shim bv)
  (let ((n (bytevector-length bv)))
    (if (< n 2)
        #nil
        (apply elisp-list (bytevector->u8-list bv)))))

(define (with-decode-shim-stubs thunk)
  (with-stubbed-refs
    `((%--selected-frame-tty-p . ,(lambda () #t))
      (%--tty-keyboard-coding-requires-decoding-p . ,(lambda () #t))
      (%--selected-frame-tty-meta-key . ,(lambda () 2))
      (%--tty-keyboard-coding-raw-text-p . ,(lambda () #nil))
      (%--tty-decode-keyboard-bytes . ,fake-decode-shim))
    thunk))

;; (195 169) → the shim is stubbed to a FIXED decoded elisp list
;; (233 234) once BOTH bytes are accumulated (incomplete for a single
;; byte — the review's F2 shape: "stub ... the decode shim to a fixed
;; decoded list") → return the first decoded event 233, unread the
;; rest (234) in forward order.  This drives emit-and-unread on a
;; `#nil'-terminated decoded list — the exact F1 scenario.
(with-stubbed-refs
  `((%--selected-frame-tty-p . ,(lambda () #t))
    (%--tty-keyboard-coding-requires-decoding-p . ,(lambda () #t))
    (%--selected-frame-tty-meta-key . ,(lambda () 2))
    (%--tty-keyboard-coding-raw-text-p . ,(lambda () #nil))
    (%--tty-decode-keyboard-bytes
     . ,(lambda (bv)
          (if (= (bytevector-length bv) 2)
              (elisp-list 233 234)
              #nil))))
  (lambda ()
    (with-unread '(195 169)
      (lambda ()
        (call-with-values
            (lambda () (read-decoded-event-from-main-queue #nil 'tag #nil))
          (lambda (event umm)
            (check "decode-shim/returns-first" 233 event)
            (check "decode-shim/umm" #nil umm)
            (check "decode-shim/unreads-rest-forward" #t
                   (elisp-list-equal? (symbol-value 'unread-command-events)
                                      '(234)))
            (check "decode-shim/queue-length" 1
                   (elist-length (symbol-value 'unread-command-events)))))))))

;; (195 169) with the shared fake shim (identity decode, incomplete
;; below 2 bytes): first read 195 → shim #nil → continue re-read;
;; second read 169 → shim decodes (195 169) → first 195 returned,
;; 169 unread.  Exercises the continue loop across two byte reads.
(with-decode-shim-stubs
  (lambda ()
    (with-unread '(195 169)
      (lambda ()
        (call-with-values
            (lambda () (read-decoded-event-from-main-queue #nil 'tag #nil))
          (lambda (event umm)
            (check "decode-shim/incomplete-continues" 195 event)
            (check "decode-shim/incomplete-unreads" #t
                   (elisp-list-equal? (symbol-value 'unread-command-events)
                                      '(169)))))))))

;; Single byte: the shim never completes below 2 bytes → #nil →
;; continue re-read; the next event is a NON-byte (symbol) → the
;; accumulated (195) plus the symbol are emitted: first byte 195
;; returned, symbol unread (C :3256 falls through to events[0]).
(with-decode-shim-stubs
  (lambda ()
    (with-unread '(195 x)
      (lambda ()
        (call-with-values
            (lambda () (read-decoded-event-from-main-queue #nil 'tag #nil))
          (lambda (event umm)
            (check "decode-shim/non-byte-emits-acc" 195 event)
            (check "decode-shim/non-byte-unreads-next" #t
                   (elisp-list-equal? (symbol-value 'unread-command-events)
                                      '(x)))))))))

;; Sixteen bytes, shim NEVER completes → flush at MAX-ENCODED-BYTES:
;; first raw byte returned, the other 15 unread (Risk 5: flush at
;; n == 16, never continue).  This needs its own always-incomplete
;; stub — the shared fake-decode-shim completes at n >= 2.
(with-stubbed-refs
  `((%--selected-frame-tty-p . ,(lambda () #t))
    (%--tty-keyboard-coding-requires-decoding-p . ,(lambda () #t))
    (%--selected-frame-tty-meta-key . ,(lambda () 2))
    (%--tty-keyboard-coding-raw-text-p . ,(lambda () #nil))
    (%--tty-decode-keyboard-bytes . ,(lambda (bv) #nil)))
  (lambda ()
    (with-unread '(97 98 99 100 101 102 103 104
                     105 106 107 108 109 110 111 112)
      (lambda ()
        (call-with-values
            (lambda () (read-decoded-event-from-main-queue #nil 'tag #nil))
          (lambda (event umm)
            (check "decode-shim/flush-16-returns-first" 97 event)
            (check "decode-shim/flush-16-unreads-15" 15
                   (elist-length (symbol-value 'unread-command-events)))
            (check "decode-shim/flush-16-order" #t
                   (elisp-list-equal? (symbol-value 'unread-command-events)
                                      '(98 99 100 101 102 103 104 105
                                        106 107 108 109 110 111 112)))))))))

;;; --- 11. Exact UTF-8 round-trip (tty frame only) ---------------------

;; 0xC3 0xA9 (é in UTF-8) needs meta_key >= 2 (the shim strips the high
;; bit for meta_key < 2, destroying 8-bit input) and a decoding tty —
;; not exercisable on a non-tty batch frame (Risk 4: the meta-key shim
;; segfaults there), so skip with a PASS note.
(if (truthy? ((%sym '--selected-frame-tty-p)))
    (let ((meta-key ((%sym '--selected-frame-tty-meta-key))))
      (if (>= meta-key 2)
          (with-unread '(195 169)
            (lambda ()
              (call-with-values
                  (lambda () (read-decoded-event-from-main-queue #nil 'tag #nil))
                (lambda (event umm)
                  (check "decode/utf8-e-acute" #xe9 event)
                  (check "decode/utf8-drained" #nil
                         (symbol-value 'unread-command-events))))))
          (report "decode/utf8-skip-meta-key-lt-2" 'PASS)))
    (report "decode/utf8-skip-non-tty" 'PASS))
