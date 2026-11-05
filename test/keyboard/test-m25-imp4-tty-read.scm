;;; test-m25-imp4-tty-read.scm --- M25 imp-4 (emacs gobble) test corpus.
;;;
;;; Covers the M25 imp-4 cutover (brief.org M25): the post-guard body of
;;; src/keyboard.c tty_read_avail_input moved into (emacs gobble) as
;;; tty-read-avail-input!.  tty_read_avail_input is now a thin dispatcher
;;; that keeps the raw dead-terminal / terminal-type / term_initted /
;;; suspended-terminal guards and the GPM drain in C.  The two portable
;;; C leaves --tty-bytes-readable and --tty-read-nonblocking perform the
;;; TTY syscalls.  This corpus exercises the moved guard/decode logic
;;; with those bindings stubbed:
;;;
;;;   - guard chain: a held buffer, a full buffer, no readable bytes, a
;;;     FIONREAD error, a zero/error(-1)/EIO(-2) read all
;;;     return the right value and never reach the decode step;
;;;   - short read: when the read returns fewer bytes than requested,
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
;;; ((force %--...)). These tests replace the bindings inside the
;;; (emacs gobble) module (module-set!), restoring them in a dynamic-wind
;;; unwind — the same stub mechanism test-m25-imp3-gobble-input.scm uses.
;;; Nothing leaks into later corpora.
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

;; Bind the module-level defelisp delay NAME in (emacs gobble) to VAL,
;; restoring the original binding after THUNK.
(define (with-gobble-value! name val thunk)
  (let ((old (module-ref gobble-mod name)))
    (dynamic-wind
      (lambda () (module-set! gobble-mod name val))
      thunk
      (lambda () (module-set! gobble-mod name old)))))

(define (with-many-values! pairs thunk)
  (if (null? pairs)
      (thunk)
      (with-gobble-value! (caar pairs) (cdar pairs)
        (lambda () (with-many-values! (cdr pairs) thunk)))))

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
;;   bytes        list of raw bytes --tty-read-nonblocking returns
;;   read-result  full result from --tty-read-nonblocking; defaults to
;;                (nread . bytevector-of-bytes)
;;   meta-key     --tty-meta-key result (default 0)
;;   quit         --quit-char result (default 7)
;; Each --ie-ascii-keystroke-event call records (event code mods); each
;; store records 'store.  run-read! returns (values return-value order).
;; Both OS operations remain in the two C leaves. Scheme owns policy and
;; byte decoding.
;;
;; M63 imp-2: the body resolves the INPUT handle FIRST, so the 3 handle
;; leaves are stubbed too.  The fake terminal is a symbol, so the real
;; --tty-handle would raise a wrong-type error before the first check.
;; The stubs answer a positive identity (42), the BORROWED state (0) and
;; a clean open (0), and the body then runs the same guard/decode path as
;; before.  This corpus therefore tests the decode, not the handle.
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
           (with-many-values!
            (list
             ;; M63 imp-2: the handle stub set (resolve, state, open).
             (cons '%--tty-handle
                   (delay (lambda (term) (get 'handle-id 42))))
             (cons '%--m63-input-state
                   (delay (lambda (id) (get 'handle-state 0))))
             (cons '%--m63-input-open!
                   (delay (lambda (id) 0)))
             (cons '%--kbd-buffer-nr-stored
                   (delay (lambda () (get 'nr-stored 0))))
             (cons '%--kbd-on-hold-p
                   (delay (lambda () (get 'on-hold #nil))))
             (cons '%--tty-bytes-readable
                   (delay (lambda (term) avail)))
             (cons '%--tty-read-nonblocking
                   (delay (lambda (term n)
                     (record! (list 'read n))
                     (get 'read-result
                          (cons (length read-bytes)
                                (u8-list->bytevector read-bytes)))))
             (cons '%--tty-meta-key
                   (delay (lambda (term) (get 'meta-key 0))))
             (cons '%--quit-char
                   (delay (lambda () (get 'quit 7))))
             (cons '%--tty-top-frame
                   (delay (lambda (term) 'the-frame)))
             (cons '%--ie-ascii-keystroke-event
                   (delay (lambda (code mods frame)
                            (record! (list 'event code mods)) 'ie)))
             (cons '%kbd-buffer-store-event!
                   (delay (lambda (ie hold) (record! 'store) #nil))))
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

;; 1d: the C ioctl leaf reports its interactive failure as -2. Scheme
;; propagates it and does not attempt a read.
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
;; M63 imp-2 CORPUS REPAIR, not a behavior change: this last check form
;; was missing its close paren at HEAD, so the file did not read as a
;; whole file.
(check "gobble/exported-tty-read-avail-input!" #t
       (procedure? (module-ref (resolve-interface '(emacs gobble))
                               'tty-read-avail-input!))))
