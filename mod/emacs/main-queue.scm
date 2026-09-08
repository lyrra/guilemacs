;;; main-queue.scm --- M12 imp-3: Scheme read-event-from-main-queue +
;;;                    read-decoded-event-from-main-queue
;;;
;;; Ports the two keyboard.c callers that sit between `(emacs read-char)`
;;; and the M11 kbd-buffer-get-event into Scheme (docs/m12-plan.org
;;; §imp-3; brief.org).  Pure transliteration of the C bodies — no
;;; algorithmic change.  The C bodies (src/keyboard.c:3140-3206 /
;;; :3213-3323) and the --rc-read-decoded-event-from-main-queue seam
;;; were deleted by imp-4; read-char.scm (imp-5 rewire, landed with
;;; imp-4) calls this port directly.
;;;
;;;     read-decoded-event-from-main-queue
;;;       └─ read-event-from-main-queue
;;;            └─ kbd-buffer-get-event       (values event kboard used-mouse-menu)
;;;
;;; Both return (values event used-mouse-menu).  KBOARD is consumed
;;; internally (side-queue routing) and dropped — C read_event never
;;; returns kb, it only compares kb != current_kboard.
;;;
;;; Conventions (identical to M9/M10/M11): defelisp delayed references
;;; for every C DEFUN ((force %--foo)); elisp variables via
;;; symbol-value / set-symbol-value!; #nil is elisp nil (a distinct
;;; object in this runtime — ≠ () and ≠ #f), so every C DEFUN result
;;; carrying elisp truthiness is wrapped in `truthy?' before use in a
;;; Scheme conditional.  No module-level mutable state.
;;;
;;; Transliteration notes vs the brief skeleton:
;;; - Every C-boolean DEFUN result (--timespec-expired-p,
;;;   --kbd-single-kboard-p, --selected-frame-tty-p,
;;;   --tty-keyboard-coding-requires-decoding-p, kboard-eq) is wrapped
;;;   in truthy? — the brief's bare `(and end-time-ptr X)` forms treat
;;;   #nil as Scheme-true and would invert the branches.
;;; - The decode gate tests FIXNATP semantics: (integer? nextevt) alone
;;;   would treat the -2 wrong-kboard sentinel (and any negative
;;;   fixnum) as an encoded byte; C requires non-negative (>= 0).
;;; - (emacs event-modifiers) exports ctrl-modifier, not char-ctl
;;;   (same value #x4000000) — the brief's import comment lists
;;;   char-ctl, which is not exported.
;;; - used-mouse-menu is OR-accumulated across decode-loop re-reads
;;;   (C's single *used_mouse_menu bool, threaded by pointer).
;;; - emit-and-unread reverses its tail with the local reverse-elisp
;;;   (nil-aware) instead of Scheme `reverse': the real-decode shim
;;;   result is an elisp list (Fcons-built, #nil-terminated) while the
;;;   byte paths build Scheme lists — both terminate fine here because
;;;   `(null? #nil)' is #t, but the explicit check pins the contract
;;;   (review cr.org F1).
;;;
;;; The C bodies being mirrored were src/keyboard.c:3140-3323 (deleted
;;; by imp-4); see the M12 imp-3 commit for the original.

(define-module (emacs main-queue)
  #:use-module (emacs elisp-ref)      ; %c, defelisp
  #:use-module (emacs-elisp runtime)  ; symbol-value, set-symbol-value!, ...
  #:use-module (emacs kbd-buffer)     ; kbd-buffer-get-event
  #:use-module (emacs event-modifiers); make-ctrl-char ctrl-modifier
                                      ; meta-modifier
  #:use-module (rnrs bytevectors)     ; u8-list->bytevector (decode shim in)
  #:declarative? #t
  #:export (read-event-from-main-queue
            read-decoded-event-from-main-queue))

;;; --- Constants ------------------------------------------------------

;; MAX_ENCODED_BYTES (src/keyboard.c:3210, file-scope #define above the
;; decode loop).  Spell it here (Risk 5) so the incomplete-continue /
;; n==16 flush boundary cannot drift.
(define MAX-ENCODED-BYTES 16)

;;; --- Helpers --------------------------------------------------------

(define (truthy? x)
  "Elisp truthiness: everything except #nil is true."
  (not (eq? x #nil)))

;;; --- C DEFUN references ---------------------------------------------

;; imp-1.1/1.2 — getctag bracket, single-kboard flag, side-queue append.
(defelisp %--get-ctag               --get-ctag)
(defelisp %--set-ctag               --set-ctag)
(defelisp %--kbd-single-kboard-p    --kbd-single-kboard-p)
(defelisp %--kbd-enqueue-side-queue --kbd-enqueue-side-queue)

;; imp-1.3 — rec-free end-time deadline check (--timespec-expired-p).
(defelisp %--timespec-expired-p     --timespec-expired-p)

;; imp-1.4 — tty keyboard-coding decode shims (Risk 4: gate every call
;; behind --selected-frame-tty-p at runtime).
(defelisp %--selected-frame-tty-p    --selected-frame-tty-p)
(defelisp %--selected-frame-tty-meta-key
          --selected-frame-tty-meta-key)
(defelisp %--tty-keyboard-coding-requires-decoding-p
          --tty-keyboard-coding-requires-decoding-p)
(defelisp %--tty-keyboard-coding-raw-text-p
          --tty-keyboard-coding-raw-text-p)
(defelisp %--tty-decode-keyboard-bytes
          --tty-decode-keyboard-bytes)

;; M8 — idle timer + kboard round-trip + kill-emacs.
(defelisp %--rc-timer-start-idle   --rc-timer-start-idle)
(defelisp %kboard-eq               kboard-eq)
(defelisp %current-kboard          current-kboard)
(defelisp %set-current-kboard      set-current-kboard)
(defelisp %kill-emacs              kill-emacs)

;;; --- read-event-from-main-queue --------------------------------------

(define (read-event-from-main-queue end-time-ptr local-tag)
  "Port of C read_event_from_main_queue (keyboard.c:3140-3206): read
one raw event from the main queue, routing events that belong to a
non-current kboard to that kboard's side queue (-2 wrong-kboard
sentinel), killing Emacs on batch EOF, and folding
extra-keyboard-modifiers into fixnum events.  Returns
(values event used-mouse-menu).  END-TIME-PTR is a foreign pointer
SCM (RC_SLOT_END_TIME) or #nil when untimed; LOCAL-TAG is the Guile
prompt tag minted by read-char-init-state."
  (let loop ()                       ; C `start:' label (:3148)
    ;; 1. Deadline check (C :3154) — OUTSIDE the getctag bracket: C
    ;;    checks end_time before save_tag, and each `goto start'
    ;;    re-enters it.  --timespec-expired-p returns elisp truthiness.
    (if (and end-time-ptr
             (truthy? ((force %--timespec-expired-p) end-time-ptr)))
        (values #nil #nil)           ; C: return c (c is Qnil here)
        (let ((saved ((force %--get-ctag))))
          (call-with-values
            (lambda ()
              ;; 2-4. getctag bracket around the read (C :3158-3163).
              ;;    dynamic-wind, never save/restore at return (Risk 1):
              ;;    getctag is the inhibit-quit-style state here, and
              ;;    the after-thunk must run even on a quit throw.
              ;;    (M28 imp-3: NOT collapsed to set-ctag-returns-old —
              ;;    --set-ctag documents "return TAG" (mirrors
              ;;    set-current-kboard) and test-m12-shims.scm pins that
              ;;    contract (ctag/set-returns-tag); set-and-return-old
              ;;    would break it.  Recorded in docs/m28-plan.org
              ;;    §imp-3.  Kept as 3 crossings.)
              (dynamic-wind
                (lambda ()
                  ;; C :3159-3161: getctag = local_tag; if (!end_time)
                  ;; timer_start_idle ().  `not end-time-ptr' would be
                  ;; wrong: #nil is Scheme-truthy — the elisp nil test
                  ;; is (eq? end-time-ptr #nil).
                  ((force %--set-ctag) local-tag)
                  (when (eq? end-time-ptr #nil)
                    ((force %--rc-timer-start-idle))))
                (lambda ()
                  ;; C :3162 — the read.  kb + used_mouse_menu come
                  ;; back as the 2nd/3rd values (imp-2 values-return).
                  (kbd-buffer-get-event end-time-ptr))
                (lambda ()
                  ;; C :3163 — restore BEFORE the side-queue routing.
                  ((force %--set-ctag) saved))))
            (lambda (event kboard used-mouse-menu)
              ;; 5. kboard side-queue routing (C :3165-3185).  The
              ;;    append stays in C (--kbd-enqueue-side-queue) — never
              ;;    set-cdr! on C-owned conses (Risk 3).
              (cond
               ((and (not (eq? event #nil))
                     (not (truthy? ((force %kboard-eq)
                                    kboard ((force %current-kboard))))))
                ((force %--kbd-enqueue-side-queue) kboard event)
                (if (truthy? ((force %--kbd-single-kboard-p)))
                    (loop)                     ; C `goto start'
                    (begin
                      ((force %set-current-kboard) kboard)
                      (values -2 used-mouse-menu))))
               (else
                ;; 6. batch-mode EOF kill (C :3187-3189).
                (when (and (truthy? (symbol-value 'noninteractive))
                           (integer? event)
                           (< event 0))
                  ((force %kill-emacs) 1 #nil))
                ;; 7. extra_keyboard_modifiers fold (C :3191-3203).
                (if (integer? event)
                    (let* ((extra (symbol-value 'extra-keyboard-modifiers))
                           (c (if (or (not (zero? (logand extra ctrl-modifier)))
                                      (and (< (logand extra #o177) #x20)
                                           (not (zero? (logand extra #o177)))))
                                  (make-ctrl-char event)
                                  event)))
                      (values (logior c (logand extra (lognot #xff7f)
                                                (lognot ctrl-modifier)))
                              used-mouse-menu))
                    (values event used-mouse-menu))))))))))

;;; --- read-decoded-event-from-main-queue ------------------------------

;; Reverse LST (a Scheme list or an elisp list — `#nil'-terminated) into
;; a proper Scheme list.  The real-decode shim returns an elisp list
;; (Fcons-built, terminated by `#nil', keyboard.c:5281-5293), while the
;; byte-accumulation / raw-text / flush paths build Scheme lists.  In
;; this runtime `(null? #nil)' is #t, so plain `reverse' happens to
;; accept both; the explicit `#nil' check keeps the contract robust
;; against either representation (review cr.org F1).
(define (reverse-elisp lst)
  (let loop ((l lst) (acc '()))
    (if (or (null? l) (eq? l #nil))
        acc
        (loop (cdr l) (cons (car l) acc)))))

;; Push all-but-first of EVENTS onto unread-command-events in reverse
;; order (so they replay forward) and return the first event together
;; with the threaded used-mouse-menu (C :3322-3325 walks `--n').  The
;; flag must survive the continue re-read, so it is passed explicitly,
;; never captured.
(define (emit-and-unread events used-mouse-menu)
  (for-each (lambda (x)
              (set-symbol-value! 'unread-command-events
                                 (cons x (symbol-value 'unread-command-events))))
            (reverse-elisp (cdr events)))
  (values (car events) used-mouse-menu))

(define (read-decoded-event-from-main-queue end-time-ptr local-tag
                                            prev-event)
  "Port of C read_decoded_event_from_main_queue (keyboard.c:3213-3323):
apply the selected frame's terminal keyboard-coding to tty input bytes,
accumulating an encoded sequence until the decode shim completes it
(incomplete → continue, up to MAX-ENCODED-BYTES → flush).  Non-byte
events short-circuit to emit-and-unread.  Returns
(values event used-mouse-menu)."
  ;; BYTES — accumulated raw fixnums in order; n = (length bytes).
  ;; USED-MOUSE-MENU is OR-accumulated across the re-reads to match C's
  ;; single *used_mouse_menu bool.
  (let loop ((bytes '())
             (used-mouse-menu #nil))
    (call-with-values
        (lambda () (read-event-from-main-queue end-time-ptr local-tag))
      (lambda (nextevt fresh-umm)
        (let ((umm (if (or (truthy? used-mouse-menu)
                           (truthy? fresh-umm))
                       #t #nil)))
          ;; 1. WINDOWSNT fast path — N/A on guilemacs (POSIX); the tty
          ;;    shims are #ifdef-gated and return nil on WINDOWSNT, so
          ;;    nothing special is needed.
          ;; 2. decode-needed gate (C :3241-3250).
          (if (not (and (truthy? ((force %--selected-frame-tty-p)))
                        (not (eq? prev-event #t))   ; prev_event != Qt
                        (truthy? ((force %--tty-keyboard-coding-requires-decoding-p)))))
              (values nextevt umm)
              ;; 3-6. accumulate + decode.
              (let ((meta-key ((force %--selected-frame-tty-meta-key))))
                ;; C :3256-3257 — only non-negative fixnums below the
                ;; threshold are encoded bytes (FIXNATP).
                (if (not (and (integer? nextevt)
                              (>= nextevt 0)
                              (< nextevt (if (= meta-key 1) #x80 #x100))))
                    ;; non-byte event: emit accumulated[0], unread the
                    ;; rest incl. nextevt (C falls through to
                    ;; `return events[0]' when FIXNATP fails).
                    (emit-and-unread (append bytes (list nextevt)) umm)
                    (let ((bytes* (append bytes (list nextevt)))
                          (n (+ (length bytes) 1)))
                      (if (truthy? ((force %--tty-keyboard-coding-raw-text-p)))
                          ;; raw-text: strip in Scheme, never incomplete
                          ;; (C :3262-3277).  meta_key==2 → no strip.
                          (emit-and-unread
                           (if (= meta-key 2)
                               bytes*
                               (map (lambda (c)
                                      (logior (logand c (lognot #x80))
                                              (if (and (= meta-key 3)
                                                       (< c #x100)
                                                       (not (zero? (logand c #x80))))
                                                  meta-modifier 0)))
                                    bytes*))
                           umm)
                          ;; real decode via the imp-1.4 shim (C
                          ;; :3278-3316).  The shim owns the meta_key<2
                          ;; high-bit strip AND the meta_key==3
                          ;; meta-modifier application — do not
                          ;; double-apply (brief §tty decode shim
                          ;; contract).
                          (let ((r ((force %--tty-decode-keyboard-bytes)
                                    (u8-list->bytevector bytes*))))
                            (if (eq? r #nil)
                                ;; incomplete — continue while n < 16,
                                ;; flush at n == 16 (Risk 5).
                                (if (< n MAX-ENCODED-BYTES)
                                    (loop bytes* umm)
                                    (emit-and-unread bytes* umm))
                                ;; decoded fixnum list → first + unread.
                                (emit-and-unread r umm)))))))))))))
