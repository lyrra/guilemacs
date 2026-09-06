;;; test-m25-imp4-tty-read.scm --- M25 imp-4 (emacs gobble) test corpus.
;;;
;;; Covers the M25 imp-4 cutover (brief.org M25): the post-guard body of
;;; src/keyboard.c tty_read_avail_input moved into (emacs gobble) as
;;; tty-read-avail-input!.  tty_read_avail_input is now a thin dispatcher
;;; that keeps the raw dead-terminal / terminal-type / term_initted /
;;; suspended-terminal guards and the GPM drain in C; four new
;;; single-purpose C shims serve the Scheme body: --tty-bytes-readable,
;;; --tty-read-nonblocking, --tty-top-frame, and
;;; --ie-ascii-keystroke-event.  This corpus exercises the moved
;;; guard/decode logic with the shims stubbed:
;;;
;;;   - guard chain: a held buffer, a full buffer, no readable bytes, a
;;;     FIONREAD error, a zero/error(-1)/EIO(-2) read all return the
;;;     right value and never reach the decode step;
;;;   - short read: when emacs_read returns fewer bytes than requested,
;;;     exactly that many bytes are decoded and the short count is the
;;;     return value;
;;;   - byte-decode fidelity: every meta-key / code / modifiers vector
;;;     from brief.org M25 imp-4, checked against the code+modifiers the
;;;     (stubbed) --ie-ascii-keystroke-event receives and the store count;
;;;   - quit-char batch-break: decode stops after the matching byte but
;;;     the returned nread is still the full batch count;
;;;   - cutover: tty-read-avail-input! is an exported procedure.
;;;
;;; gobble.scm references its C primitives through defelisp delays
;;; ((force %--...)), so these tests stub those delays by replacing them
;;; inside the (emacs gobble) module (module-set!), restoring after —
;;; the same stub mechanism test-m25-imp3-gobble-input.scm uses.  Every
;;; stub is restored in a dynamic-wind unwind, so nothing leaks into
;;; later corpora.
;;;
;;; Sourced by test/keyboard/test-m25-imp4-tty-read.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback from
;;; elisp.  See brief.org M25 imp-4.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))
(use-modules (srfi srfi-11))        ; let-values
(use-modules (emacs gobble))
(use-modules (emacs event-modifiers))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

;;; --- Stub helpers ----------------------------------------------------

(define gobble-mod (resolve-module '(emacs gobble)))

;; Replace the defelisp delay NAME in (emacs gobble) so that
;; (force NAME) yields PROC, restoring the original delay after THUNK.
(define (with-gobble-delay! name proc thunk)
  (let ((old (module-ref gobble-mod name)))
    (dynamic-wind
      (lambda () (module-set! gobble-mod name (delay proc)))
      thunk
      (lambda () (module-set! gobble-mod name old)))))

(define (with-many-delays! pairs thunk)
  (if (null? pairs)
      (thunk)
      (with-gobble-delay! (caar pairs) (cadar pairs)
        (lambda () (with-many-delays! (cdr pairs) thunk)))))

(define order '())
(define (record! x) (set! order (append order (list x))))
(define (reset-order!) (set! order '()))

;; Drop the (read n) bookkeeping records from `order`; decode/store
;; assertions only care about 'event and 'store records.
(define (decode-calls ord)
  (filter (lambda (x) (not (and (pair? x) (eq? (car x) 'read))))
          ord))

;; The tty-read-avail-input! decode path's standard stub set, driven by
;; an OVR alist of overrides (see run-read!):
;;   nr-stored    --kbd-buffer-nr-stored result (default 0)
;;   on-hold      --kbd-on-hold-p result (default #nil)
;;   avail        --tty-bytes-readable result (default = length of bytes)
;;   bytes        list of raw bytes the nonblocking read returns
;;   read-result  full result from --tty-read-nonblocking; defaults to
;;                (nread . bytevector-of-bytes)
;;   meta-key     --tty-meta-key result (default 0)
;;   quit         --quit-char result (default 7)
;; Each --ie-ascii-keystroke-event call records (event code mods); each
;; store records 'store.  run-read! returns (values return-value order).
(define (assq-ref ovr key)
  (let ((hit (assq key ovr)))
    (if hit (cdr hit) #f)))

(define (run-read! ovr)
  (define (get key default)
    (let ((v (assq-ref ovr key)))
      (if v v default)))
  (let* ((read-bytes (get 'bytes '()))
         (avail (get 'avail (length read-bytes))))
    (reset-order!)
    (let ((return-value
           (with-many-delays!
            (list
             (list '%--kbd-buffer-nr-stored
                   (lambda () (get 'nr-stored 0)))
             (list '%--kbd-on-hold-p
                   (lambda () (get 'on-hold #nil)))
             (list '%--tty-bytes-readable
                   (lambda (term) avail))
             (list '%--tty-read-nonblocking
                   (lambda (term n)
                     (record! (list 'read n))
                     (get 'read-result
                          (cons (length read-bytes)
                                (u8-list->bytevector read-bytes)))))
             (list '%--tty-meta-key
                   (lambda (term) (get 'meta-key 0)))
             (list '%--quit-char
                   (lambda () (get 'quit 7)))
             (list '%--tty-top-frame
                   (lambda (term) 'the-frame))
             (list '%--ie-ascii-keystroke-event
                   (lambda (code mods frame)
                     (record! (list 'event code mods)) 'ie))
             (list '%kbd-buffer-store-event!
                   (lambda (ie hold) (record! 'store) #nil)))
            (lambda ()
              (tty-read-avail-input! 'some-terminal)))))
      (values return-value order))))

;;; --- 1. Guard-chain early returns ------------------------------------
;;; Each guard path must return the documented value without calling the
;;; nonblocking read or the decode step (no 'read, no 'event, no 'store).

;; 1a: kbd on hold → 0, nothing read/stored.
(let-values (((ret ord) (run-read! '((on-hold . #t) (bytes . (65)) (avail . 1)))))
  (check "tty-read/on-hold-returns-0" 0 ret)
  (check "tty-read/on-hold-no-read-or-store" '() ord))

;; 1b: buffer full (buffer_free <= 0) → 0.  buffer_free = 4096 - nr - 1;
;; nr-stored 4095 leaves buffer_free 0.
(let-values (((ret ord) (run-read! '((nr-stored . 4095) (bytes . (65))))))
  (check "tty-read/buffer-full-returns-0" 0 ret)
  (check "tty-read/buffer-full-no-read-or-store" '() ord))

;; 1c: no bytes available (FIONREAD 0) → 0.
(let-values (((ret ord) (run-read! '((avail . 0) (bytes . ())))))
  (check "tty-read/no-bytes-returns-0" 0 ret)
  (check "tty-read/no-bytes-no-read-or-store" '() ord))

;; 1d: FIONREAD error (--tty-bytes-readable -2) → -2, no read.
(let-values (((ret ord) (run-read! '((avail . -2)))))
  (check "tty-read/fionread-error-returns--2" -2 ret)
  (check "tty-read/fionread-error-no-read-or-store" '() ord))

;; 1e: a zero-length read (nread 0) → 0, no decode.
(let-values (((ret ord) (run-read! '((avail . 3) (bytes . ())
                                     (read-result . (0 . #vu8()))))))
  (check "tty-read/zero-read-returns-0" 0 ret)
  (check "tty-read/zero-read-no-event" '() (decode-calls ord)))

;; 1f: a raw read error (nread -1, not EIO) → -1, no decode.
(let-values (((ret ord) (run-read! '((avail . 3) (bytes . ())
                                     (read-result . (-1 . #vu8()))))))
  (check "tty-read/raw-error-returns--1" -1 ret)
  (check "tty-read/raw-error-no-event" '() (decode-calls ord)))

;; 1g: an EIO read (--tty-read-nonblocking returns the bare -2, not a
;; pair) → -2, no decode.
(let-values (((ret ord) (run-read! '((avail . 3) (read-result . -2)))))
  (check "tty-read/eio-returns--2" -2 ret)
  (check "tty-read/eio-no-event" '() (decode-calls ord)))

;;; --- 2. Short read ------------------------------------------------
;;; emacs_read returns fewer bytes than requested (2 of the available 5);
;;; exactly 2 bytes are decoded/stored and the return value is the short
;;; count 2.
(let-values (((ret ord) (run-read! '((avail . 5) (bytes . (65 66))
                                     (meta-key . 0)))))
  (check "tty-read/short-read-decodes-read-count" 2 ret)
  (check "tty-read/short-read-two-events"
          '((event 65 0) store (event 66 0) store) (decode-calls ord)))

;;; --- 3. Byte-decode fidelity --------------------------------------
;;; The brief.org M25 imp-4 vectors: for raw byte b and meta-key m, the
;;; (stubbed) --ie-ascii-keystroke-event must receive the expected code
;;; and modifiers, exactly once, and the byte is stored once.
(define (decode-vector name b m expected-code expected-mods)
  (let-values (((ret ord)
                (run-read! (list (cons 'bytes (list b))
                                 (cons 'meta-key m)))))
    (check (string-append "tty-read/decode/" name) ret 1)
    (check (string-append "tty-read/decode/" name "/code-mods")
           (list (list 'event expected-code expected-mods) 'store)
           (decode-calls ord))))

;; b #x41 ('A'), meta-key 0 → code #x41, modifiers 0.
(decode-vector "A-meta0" #x41 0 #x41 0)
;; b #xC1, meta-key 1 → code #x41, modifiers meta-modifier (high bit set).
(decode-vector "C1-meta1" #xC1 1 #x41 meta-modifier)
;; b #xC1, meta-key 0 → code #x41, modifiers 0 (stripped, no meta flag —
;; meta-key must be exactly 1 to set the modifier).
(decode-vector "C1-meta0" #xC1 0 #x41 0)
;; b #xC1, meta-key 2 → code #xC1 (unstripped), modifiers 0.
(decode-vector "C1-meta2" #xC1 2 #xC1 0)

;;; --- 4. Quit-char batch-break --------------------------------------
;;; b #x87 with meta-key 0 strips to code 7 == quit-char (default C-g).
;;; The matching byte is stored, decode stops, and later bytes in the
;;; same batch (#x42) are dropped — but the returned nread is still the
;;; full batch count (3).
(let-values (((ret ord) (run-read! '((bytes . (#x41 #x87 #x42))
                                     (meta-key . 0) (quit . 7)))))
  (check "tty-read/quit-break-returns-full-batch" 3 ret)
  (check "tty-read/quit-break-drops-later-bytes"
          '((event 65 0) store (event 7 0) store) (decode-calls ord)))

;; A plain 'A' batch with no quit char decodes every byte and returns the
;; full count.
(let-values (((ret ord) (run-read! '((bytes . (#x41 #x42 #x43))
                                     (meta-key . 0)))))
  (check "tty-read/no-quit-decodes-all" 3 ret)
  (check "tty-read/no-quit-three-events"
          '((event 65 0) store (event 66 0) store (event 67 0) store)
          (decode-calls ord)))

;;; --- 5. Cutover wiring ----------------------------------------------
;;; tty_read_avail_input (C) must resolve the (emacs gobble) public ref
;;; tty-read-avail-input!.  Verify it is an exported procedure.
(check "gobble/exported-tty-read-avail-input!" #t
       (procedure? (module-ref (resolve-interface '(emacs gobble))
                               'tty-read-avail-input!)))
