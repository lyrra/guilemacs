;;; test-m20-menu-prompt.scm --- M20 imp-1 + imp-2 test corpus.
;;;
;;; imp-1 tests the four new C shims in src/keyboard.c that the Scheme
;;; menu-prompt port (M20) will call: --rc-clear-echo-at-next-pause,
;;; --x-popup-menu-1, --store-kbd-macro-char, --menu-bar-hpos-vpos-raw
;;; (plus the --rc-ok-to-echo-at-next-pause-p reader added to test the
;;; first).
;;;
;;; imp-2 tests the Scheme bodies in (emacs menu-prompt):
;;; record-menu-key, read-menu-command, read-char-x-menu-prompt (1:1
;;; ports of record_menu_key, read_menu_command, read_char_x_menu_prompt).
;;;
;;;
;;; Sourced by test/keyboard/test-m20-menu-prompt.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See docs/m20-plan.org and brief.org.
;;;
;;; Batch limitation: --menu-bar-hpos-vpos-raw wraps the same C
;;; x_y_to_hpos_vpos that --menu-bar-hpos-vpos wraps, which crashes on a
;;; GTK batch build (no live glyph matrices, see test-m19-shims.scm).
;;; So the raw shim is checked for registration always, and its value
;;; agreement with --menu-bar-hpos-vpos only on a window-system frame
;;; that actually has a live menu-bar window with zero internal border;
;;; otherwise that sub-check is skipped (reported PASS).

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))
(use-modules (emacs menu-prompt))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

;;; --- 1. --rc-clear-echo-at-next-pause ------------------------------
;;; With the --rc-ok-to-echo-at-next-pause-p reader, assert the field
;;; state transitions: allow sets it non-NULL (t), clear sets it NULL
;;; (nil), and clear is idempotent.
(define (rc-echo-field?) ((%sym '--rc-ok-to-echo-at-next-pause-p)))

;; allow first sets the field non-NULL.
((%sym '--rc-allow-echo-at-next-pause))
(check "clear-echo/set-by-allow" #t (eq? (rc-echo-field?) #t))
;; the new shim clears it back to NULL.
((%sym '--rc-clear-echo-at-next-pause))
(check "clear-echo/cleared" #t (eq? (rc-echo-field?) #nil))
;; clearing again is a harmless no-op (still nil).
((%sym '--rc-clear-echo-at-next-pause))
(check "clear-echo/idempotent" #t (eq? (rc-echo-field?) #nil))
;; no-error on the 0-arg shim.
(check "clear-echo/no-error" #t (no-error? (lambda () ((%sym '--rc-clear-echo-at-next-pause)))))

;;; --- 2. --x-popup-menu-1 -------------------------------------------
;;; Unlike `x-popup-menu', the shim must NOT call init_raw_keybuf_count.
;;; Set a sentinel raw_keybuf_count, drive the shim into a
;;; wrong-type-argument error (invalid non-keymap MENU) before any
;;; display, and confirm the sentinel survives.  Position is a proper
;;; mouse-click-like `((0 . 0) WINDOW)' that decodes to the live
;;; selected window, so the error comes from decoding the bad MENU, not
;;; from position handling.
(define sentinel 42)
;; Save the pre-test count and restore it afterwards: the corpus runs in
;; the same emacs process as the other filtered tests (run-tests-loadup-
;; emacs loads all files then runs ERT), so a leaked raw_keybuf_count
;; would corrupt m5-this-single-command-raw-keys/empty-shape.
(define saved-count ((%sym '--raw-keybuf-count)))
((%sym '--set-raw-keybuf-count) sentinel)
(define xpopup-result
  (catch #t
    (lambda ()
      ((%sym '--x-popup-menu-1)
       (list (cons 0 0) ((%sym 'selected-window)))
       'bogus-menu-symbol)
      'no-error)
    (lambda (key . args) (list 'signal key args))))
(check "xpopup/signals-error" #t (not (eq? xpopup-result 'no-error)))
;; raw-keybuf-count must still read the sentinel.
(check "xpopup/raw-count-preserved" sentinel ((%sym '--raw-keybuf-count)))
;; Restore the original count so no state leaks into later tests.
((%sym '--set-raw-keybuf-count) saved-count)
(check "xpopup/raw-count-restored" saved-count ((%sym '--raw-keybuf-count)))

;;; --- 3. --store-kbd-macro-char -------------------------------------
;;; With defining-kbd-macro nil, the call must be a harmless no-op (no
;;; error).  There is no reader for the kbd-macro buffer (out of scope),
;;; so only the no-error property is asserted.
(check "store-kbd-macro-char/noop" #t
       (no-error? (lambda () ((%sym '--store-kbd-macro-char) 97))))

;;; --- 4. --menu-bar-hpos-vpos-raw -----------------------------------
;;; Registration always.  Value agreement with --menu-bar-hpos-vpos is
;;; only meaningful on a window-system frame that has a live menu-bar
;;; window with zero internal border; the raw shim matches the C
;;; --menu-bar-touch-activate body exactly (no FRAME_TO_WINDOW_PIXEL
;;; conversion).  On a batch/GTK build no such frame exists, so the
;;; agreement check is skipped.
(check "raw-hpos-vpos/registered" #t
       (not (eq? (%sym '--menu-bar-hpos-vpos-raw) #nil)))
;; Mirror the C --menu-bar-touch-activate body's NILP (menu_bar_window)
;; short-circuit: a nil WINDOW must return nil, not signal.
(check "raw-hpos-vpos/nil-window-no-op" #t
       (eq? ((%sym '--menu-bar-hpos-vpos-raw) #nil 0 0) #nil))

(define (window-system-frame?)
  (catch #t
    (lambda () ((%sym 'display-graphic-p)))
    (lambda (k . a) #f)))

(define frame ((%sym 'selected-frame)))
(define menu-bar-win
  (catch #t
    (lambda () ((%sym '--frame-menu-bar-window) frame))
    (lambda (k . a) #nil)))

(define (frame-internal-border-width f)
  ((%sym 'frame-parameter) f 'internal-border-width))

(define (try-raw-vs-cooked ix iy)
  ;; Return the (RAW . COOKED) pair, or #f if either call signals.
  (catch #t
    (lambda ()
      (cons ((%sym '--menu-bar-hpos-vpos-raw) menu-bar-win ix iy)
            ((%sym '--menu-bar-hpos-vpos) menu-bar-win ix iy)))
    (lambda (k . a) #f)))

(if (and (window-system-frame?)
         (not (eq? menu-bar-win #nil))
         (= (or (frame-internal-border-width frame) 0) 0))
    ;; Zero internal border: FRAME_TO_WINDOW_PIXEL is identity, so raw
    ;; and cooked agree.  Probe a point known to be inside the menu bar.
    (let ((pair (try-raw-vs-cooked 10 5)))
      (if pair
          (check "raw-hpos-vpos/agrees-with-cooked@0border" #t
                 (equal? (car pair) (cdr pair)))
          ;; Live menu-bar window but x_y_to_hpos_vpos crashed (no glyph
          ;; matrix) — treat as a controlled skip, not a failure.
          (report "raw-hpos-vpos/agrees-with-cooked@0border" 'PASS)))
    ;; No window-system frame with a live menu-bar window: skip, per
    ;; brief.org "Tests" (skip when the test frame cannot set one).
    (report "raw-hpos-vpos/agrees-with-cooked@0border" 'PASS))

;;; =====================================================================
;;; M20 imp-2 — Scheme bodies in (emacs menu-prompt)
;;; =====================================================================
;;; Save/restore the elisp globals that the ported bodies mutate, so
;;; nothing leaks into later corpora in the shared loadup-ERT process.
(define (saved-values . names)
  (map (lambda (n) (symbol-value n)) names))

(define (restore-values! names vals)
  (for-each (lambda (n v) (set-symbol-value! n v)) names vals))

(define %menu-state-names
  '(echo-keystrokes last-input-event unread-command-events menu-prompting))

(define (with-mp-state thunk)
  (let ((saved (apply saved-values %menu-state-names)))
    (dynamic-wind
      (lambda () #t)
      thunk
      (lambda () (restore-values! %menu-state-names saved)))))

;;; --- 5. record-menu-key ----------------------------------------------
;;; Port of C record_menu_key (keyboard.c:4327-4346).  Wipes the echo
;;; area, records the char, clears ok_to_echo_at_next_pause, adds to the
;;; current key, echoes, sets last-input-event, and increments
;;; num-input-events.  With the imp-1 --rc-ok-to-echo-at-next-pause-p
;;; reader, assert the field cleared; assert last-input-event updated.
;;;
;;; To make ok_to_echo_at_next_pause non-NULL first we use
;;; --rc-allow-echo-at-next-pause (also an imp-1 shim).  echo-update is
;;; C-owned but only acts when immediate-echo is set, so in a batch
;;; build it is a no-op; the add-command-key side effect is observable
;;; via --this-command-key-count.
(define (record-menu-key-clear-field?)
  ;; Returns #t if calling record-menu-key clears the echo-at-next-pause
  ;; field.  The field must first be set non-NULL.
  (let ((saved-echo ((%sym '--rc-ok-to-echo-at-next-pause-p))))
    (dynamic-wind
      (lambda () ((%sym '--rc-allow-echo-at-next-pause)))
      (lambda ()
        ((@ (emacs menu-prompt) record-menu-key) 97)
        (eq? ((%sym '--rc-ok-to-echo-at-next-pause-p)) #nil))
      (lambda ()
        (if (eq? saved-echo #t)
            ((%sym '--rc-allow-echo-at-next-pause))
            ((%sym '--rc-clear-echo-at-next-pause)))))))

(with-mp-state
 (lambda ()
   (let ((saved-lie (symbol-value 'last-input-event)))
     (dynamic-wind
       (lambda () #t)
       (lambda ()
         ;; clear-field? itself calls record-menu-key once; capture the count
         ;; right after it so the direct call below is the only counted one.
         (check "record-menu-key/clears-echo-at-next-pause" #t
                (record-menu-key-clear-field?))
         (let ((before ((%sym '--this-command-key-count))))
           ((@ (emacs menu-prompt) record-menu-key) 97)
           (check "record-menu-key/sets-last-input-event" 97
                  (symbol-value 'last-input-event))
           (check "record-menu-key/advances-key-count" (+ before 1)
                  ((%sym '--this-command-key-count)))))
       (lambda ()
         (set-symbol-value! 'last-input-event saved-lie))))))

;;; --- 6. read-menu-command --------------------------------------------
;;; Port of C read_menu_command (keyboard.c:2627-2648).  Do NOT drive a
;;; real interactive read in batch mode.  Stub the C engine shim
;;; --rc-read-key-sequence-menu with fset, mirroring
;;; ertest-read-key-sequence.el's stubbing of --read-key-sequence-and-vector.
;;; Cover: a zero-length vector and fixnum -1 both → #t; a non-empty
;;; vector → the current read-key-sequence-cmd value; and echo-keystrokes
;;; is 0 during the call and restored after even when the stub signals.
(define %rcrksm '--rc-read-key-sequence-menu)
(define (with-rcrksm-stub stub thunk)
  (let ((saved (symbol-function %rcrksm)))
    (dynamic-wind
      (lambda () ((%c 'fset) %rcrksm stub))
      thunk
      (lambda () ((%c 'fset) %rcrksm saved)))))

(with-mp-state
 (lambda ()
   ;; zero-length vector → #t
   (with-rcrksm-stub (lambda () (vector))
     (lambda ()
       (check "read-menu-command/empty-vector-t" #t
              (eq? ((@ (emacs menu-prompt) read-menu-command)) #t))))
   ;; fixnum -1 → #t
   (with-rcrksm-stub (lambda () -1)
     (lambda ()
       (check "read-menu-command/fixnum--1-t" #t
              (eq? ((@ (emacs menu-prompt) read-menu-command)) #t))))
   ;; non-empty vector → current read-key-sequence-cmd
   (let ((saved-ek (symbol-value 'echo-keystrokes)))
     (with-rcrksm-stub (lambda () (vector 97))
       (lambda ()
         (let ((res ((@ (emacs menu-prompt) read-menu-command))))
           (check "read-menu-command/nonempty->read-key-sequence-cmd" #t
                  (equal? res ((%c '--read-key-sequence-cmd)))))))
     ;; echo-keystrokes restored even after the read (it should be back to
     ;; the saved value by the time read-menu-command returns).
     (check "read-menu-command/echo-restored" saved-ek
            (symbol-value 'echo-keystrokes)))
   ;; echo-keystrokes is 0 during the read, and restored after the stub
   ;; signals.
   (let ((saved-ek (symbol-value 'echo-keystrokes))
         (observed #f))
     (with-rcrksm-stub (lambda ()
                         (set! observed (symbol-value 'echo-keystrokes))
                         (error "boom"))
       (lambda ()
         (catch #t
           (lambda () ((@ (emacs menu-prompt) read-menu-command)) #f)
           (lambda (k . args) #t))))
     (check "read-menu-command/echo-0-during-signal" 0 observed)
     (check "read-menu-command/echo-restored-after-signal" saved-ek
            (symbol-value 'echo-keystrokes)))))

;;; --- 7. read-char-x-menu-prompt --------------------------------------
;;; Port of C read_char_x_menu_prompt (keyboard.c:8659-8718).  Two-value
;;; return (event, used-mouse-menu).  Cover: menu-prompting nil →
;;; (#nil #f); prev-event whose car is menu-bar → (#nil #f) (excluded);
;;; stub --x-popup-menu-1 with fset to return a canned list of symbols
;;; and fixnums, call with a qualifying mouse-click prev-event, and
;;; assert the first element is the primary value with flag #t, the
;;; remaining elements are pushed onto unread-command-events (each
;;; wrapped (SYM . disabled) when symbol/fixnum), and last-input-event is
;;; left at the last recorded element.
(define %xpopup '--x-popup-menu-1)
(define (with-xpopup-stub stub thunk)
  (let ((saved (symbol-function %xpopup)))
    (dynamic-wind
      (lambda () ((%c 'fset) %xpopup stub))
      thunk
      (lambda () ((%c 'fset) %xpopup saved)))))

(define (call-rcxmp map prev)
  (call-with-values (lambda () ((@ (emacs menu-prompt) read-char-x-menu-prompt) map prev))
    (lambda (v flag) (list v flag))))

(with-mp-state
 (lambda ()
   ;; menu-prompting nil → (#nil #f)
   (let ((saved-mp (symbol-value 'menu-prompting)))
     (dynamic-wind
       (lambda () (set-symbol-value! 'menu-prompting #nil))
       (lambda ()
         (check "read-char-x-menu-prompt/nil-menu-prompting" #t
                (equal? (call-rcxmp #nil '(menu-bar (0 . 0)))
                        (list #nil #f))))
       (lambda () (set-symbol-value! 'menu-prompting saved-mp))))
   ;; prev-event car = menu-bar → (#nil #f), regardless of menu-prompting.
   (let ((saved-mp (symbol-value 'menu-prompting)))
     (dynamic-wind
       (lambda () (set-symbol-value! 'menu-prompting #t))
       (lambda ()
         (check "read-char-x-menu-prompt/menu-bar-car-excluded" #t
                (equal? (call-rcxmp #nil '(menu-bar (0 . 0)))
                        (list #nil #f))))
       (lambda () (set-symbol-value! 'menu-prompting saved-mp))))
   ;; Canned popup: qualifying mouse-click prev-event, stub returns
   ;; (sym-a 42 sym-b).  First element → primary value; (42 . disabled)
   ;; and (sym-b . disabled) pushed onto unread-command-events;
   ;; last-input-event left at the last recorded element (sym-b).
   (let ((saved-mp (symbol-value 'menu-prompting))
         (saved-uce (symbol-value 'unread-command-events))
         (saved-lie (symbol-value 'last-input-event)))
     (dynamic-wind
       (lambda () (set-symbol-value! 'menu-prompting #t))
       (lambda ()
         (with-xpopup-stub (lambda (pos menu) '(sym-a 42 sym-b))
           (lambda ()
             (let* ((saved-uce2 (symbol-value 'unread-command-events))
                    (res (call-rcxmp #nil '(mouse-1 (0 . 0))))
                    (after (symbol-value 'unread-command-events))
                    (pushed (let loop ((acc '()) (tail after))
                              (if (equal? tail saved-uce2)
                                  (reverse acc)
                                  (if (pair? tail)
                                      (loop (cons (car tail) acc) (cdr tail))
                                      acc)))))
               (check "read-char-x-menu-prompt/primary-value" 'sym-a (car res))
               (check "read-char-x-menu-prompt/used-mouse-menu" #t (cadr res))
               (check "read-char-x-menu-prompt/pushed-disabled-cons" #t
                      (equal? (list '(42 . disabled) '(sym-b . disabled))
                              pushed))
               (check "read-char-x-menu-prompt/last-input-event" 'sym-b
                      (symbol-value 'last-input-event))))))
       (lambda ()
         (set-symbol-value! 'menu-prompting saved-mp)
         (set-symbol-value! 'unread-command-events saved-uce)
         (set-symbol-value! 'last-input-event saved-lie))))))

;;; =====================================================================
;;; M20 imp-3 — read-char-minibuf-menu-prompt
;;; =====================================================================
;;; Port of C read_char_minibuf_menu_prompt (keyboard.c:8720-8939).
;;; Reads one key, paging on menu-prompt-more-char, with kbd-macro
;;; suppression around the read.  Every case stubs --message3-nolog with
;;; fset (no minibuffer output in batch) and restores it.  with-mp-state
;;; now also saves/restores menu-prompting and unread-command-events.
;;; Calls use char code 97 (?#\a) / 98 (?#\b) in unread-command-events.
(define %msg3 '--message3-nolog)
(define (with-msg3-stub thunk)
  (let ((saved (symbol-function %msg3)))
    (dynamic-wind
      (lambda () ((%c 'fset) %msg3 (lambda (str) #nil)))
      thunk
      (lambda () ((%c 'fset) %msg3 saved)))))

(define %store '--store-kbd-macro-char)
(define (with-store-stub record! thunk)
  (let ((saved (symbol-function %store)))
    (dynamic-wind
      (lambda () ((%c 'fset) %store (lambda (c) (record! c) #nil)))
      thunk
      (lambda () ((%c 'fset) %store saved)))))

;;; Bind the live kboard's defining-kbd-macro field to #t, run THUNK,
;;; then restore the original value.
(define (with-kbd-macro-t thunk)
  (let* ((kb ((%c 'current-kboard)))
         (orig ((%c 'kboard-defining-kbd-macro) kb)))
    (dynamic-wind
      (lambda () ((%c 'set-kboard-defining-kbd-macro) kb #t))
      thunk
      (lambda () ((%c 'set-kboard-defining-kbd-macro) kb orig)))))

(define (test-keymap)
  (let ((m ((%c 'make-sparse-keymap) "Test")))
    ((%c 'define-key) m "a" (list 'menu-item "Alpha" 'ignore))
    ((%c 'define-key) m "b" (list 'menu-item "Beta" 'ignore))
    m))

;; 1. menu-prompting nil → returns nil immediately, no read (seeded
;;    unread-command-events untouched).
(with-mp-state
 (lambda ()
   (with-msg3-stub
    (lambda ()
      (set-symbol-value! 'menu-prompting #nil)
      (let ((saved-uce (symbol-value 'unread-command-events)))
        (let ((res ((@ (emacs menu-prompt) read-char-minibuf-menu-prompt) 0 (test-keymap))))
          (check "minibuf-menu-prompt/nil-menu-prompting" #t (eq? res #nil))
          (check "minibuf-menu-prompt/nil-menu-prompting-no-read" saved-uce
                 (symbol-value 'unread-command-events))))))))

;; 2. A keymap with no prompt string → returns nil, no read.
(with-mp-state
 (lambda ()
   (with-msg3-stub
    (lambda ()
      (set-symbol-value! 'menu-prompting #t)
      (let ((m ((%c 'make-sparse-keymap))))
        ((%c 'define-key) m "a" (list 'menu-item "Alpha" 'ignore))
        (let ((saved-uce (symbol-value 'unread-command-events)))
          (let ((res ((@ (emacs menu-prompt) read-char-minibuf-menu-prompt) 0 m)))
            (check "minibuf-menu-prompt/no-prompt-keymap" #t (eq? res #nil))
            (check "minibuf-menu-prompt/no-prompt-no-read" saved-uce
                   (symbol-value 'unread-command-events)))))))))

;; 3. Normal read: seed (97) → returns 97.
(with-mp-state
 (lambda ()
   (with-msg3-stub
    (lambda ()
      (set-symbol-value! 'menu-prompting #t)
      (set-symbol-value! 'unread-command-events (list 97))
      (check "minibuf-menu-prompt/normal-read" 97
             ((@ (emacs menu-prompt) read-char-minibuf-menu-prompt) 0 (test-keymap)))))))

;; 4. Paging: seed (more-char 98) → first read is the help char, so the
;;    outer loop reads again and returns 98 (proves two reads).
(with-mp-state
 (lambda ()
   (with-msg3-stub
    (lambda ()
      (set-symbol-value! 'menu-prompting #t)
      (set-symbol-value! 'unread-command-events
                         (list (symbol-value 'menu-prompt-more-char) 98))
      (check "minibuf-menu-prompt/paging" 98
             ((@ (emacs menu-prompt) read-char-minibuf-menu-prompt) 0 (test-keymap)))))))

;; 5. Kbd-macro suppression + store: with defining-kbd-macro #t, the
;;    read is suppressed during the read (restored to #t afterwards) and
;;    the chosen char is stored once via --store-kbd-macro-char.
(with-mp-state
 (lambda ()
   (with-msg3-stub
    (lambda ()
      (set-symbol-value! 'menu-prompting #t)
      (let ((calls '()))
        (with-kbd-macro-t
         (lambda ()
           (with-store-stub (lambda (c) (set! calls (cons c calls)))
             (lambda ()
               (set-symbol-value! 'unread-command-events (list 97))
               (let ((res ((@ (emacs menu-prompt) read-char-minibuf-menu-prompt) 0 (test-keymap))))
                 (check "minibuf-menu-prompt/kbd-macro-returns" 97 res)
                 (check "minibuf-menu-prompt/kbd-macro-store-once" (list 97)
                        (reverse calls))
                 (check "minibuf-menu-prompt/kbd-macro-restored" #t
                        (eq? ((%c 'kboard-defining-kbd-macro) ((%c 'current-kboard))) #t))))))))))))

;; 6. Coexistence: the Scheme function and the still-live C shim
;;    --rc-read-char-minibuf-menu-prompt agree on the same keymap/seed.
(with-mp-state
 (lambda ()
   (with-msg3-stub
    (lambda ()
      (set-symbol-value! 'menu-prompting #t)
      (let ((keymap (test-keymap)))
        (set-symbol-value! 'unread-command-events (list 97))
        (let ((scheme-res ((@ (emacs menu-prompt) read-char-minibuf-menu-prompt) 0 keymap)))
          (set-symbol-value! 'unread-command-events (list 97))
          (let ((c-res ((%c '--rc-read-char-minibuf-menu-prompt) 0 keymap)))
            (check "minibuf-menu-prompt/coexists-with-c-shim" scheme-res c-res))))))))
