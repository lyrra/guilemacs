(define-module (emacs this-command-keys)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:use-module ((emacs event-modifiers) #:select (modifier-bit))
  #:declarative? #t
  #:export (this-command-keys
            this-command-keys-vector
            this-single-command-keys
            this-single-command-raw-keys
            clear-this-command-keys
            set--this-command-keys
            ;; Migrated storage (from C):
            this-single-command-key-start-get
            this-single-command-key-start-set!
            init-this-command-keys-registrations))

;;; M5 — Read-side DEFUNs for the this-command-keys subsystem,
;;; ported from keyboard.c.  The vector storage (this_command_keys,
;;; raw_keybuf, indices) stays C-owned because the per-keystroke
;;; writer add_command_key is C and won't move until M5/M8 surface a
;;; Scheme caller.  The user-facing DEFUNs are pure readers (with
;;; one clear-side-effect, clear-this-command-keys) and ported
;;; cleanly.
;;;
;;; Skipped in M5: Finput_pending_p, Fdiscard_input, Fset__this_command_keys
;;; — each would force several new C subrs for marginal value (they
;;; touch kbd_buffer ring pointers, terminal I/O, or add_command_key).
;;; Revisit with M6/M7 if a Scheme caller emerges.
;;;
;;; See docs/keyboard.org §M5.  The C primitives wrapped here:
;;;   --this-command-keys, --this-command-key-count,
;;;   --raw-keybuf, --raw-keybuf-count,
;;;   --this-single-command-key-start,
;;;   --reset-this-command-keys, --set-this-command-key-count,
;;;   --clear-recent-keys-ring,
;;;   --make-event-array-from-vector (defined by M3).


;;;;
;;;; Storage migrated from C (was: static ptrdiff_t in keyboard.c).
;;;; The corresponding `--this-single-command-key-start' and
;;;; `--set-this-single-command-key-start' C DEFUNs are now thin
;;;; dispatch shims into these accessors.
;;;;

(define this-single-command-key-start 0)

(define (this-single-command-key-start-get)
  this-single-command-key-start)

(define (this-single-command-key-start-set! n)
  (set! this-single-command-key-start n)
  #nil)

;;;;
;;;; Read DEFUNs
;;;;

(define (this-command-keys)
  "Return the key sequence that invoked this command — a string or
vector.  Mirrors C Fthis_command_keys."
  (let ((v ((%c '--this-command-keys)))
        (n ((%c '--this-command-key-count))))
    ((%c '--make-event-array-from-vector) v 0 n)))

(define (this-command-keys-vector)
  "Return the key sequence as a vector.  Mirrors C
Fthis_command_keys_vector — including the Guile-Emacs string-
corruption defensive recovery: if this_command_keys has been
corrupted to a string by some prior GC/binding bug, reset it to a
fresh empty vector before reading."
  (let ((v ((%c '--this-command-keys))))
    (when (string? v)
      (format (current-error-port)
              "WARNING this-command-keys-vector: this_command_keys was corrupted to a string! Resetting to vector.~%")
      ((%c '--reset-this-command-keys))))
  (let ((v ((%c '--this-command-keys)))
        (n ((%c '--this-command-key-count))))
    ((%c '--make-event-array-from-vector) v 0 n)))

(define (this-single-command-keys)
  "Return the last single-command key sequence as a vector.
Mirrors C Fthis_single_command_keys."
  (let* ((v     ((%c '--this-command-keys)))
         (count ((%c '--this-command-key-count)))
         (start ((%c '--this-single-command-key-start)))
         (nkeys (- count start)))
    ((%c '--make-event-array-from-vector) v start (max 0 nkeys))))

(define (this-single-command-raw-keys)
  "Return the raw events read for this command (pre-translation).
Mirrors C Fthis_single_command_raw_keys."
  (let ((v ((%c '--raw-keybuf)))
        (n ((%c '--raw-keybuf-count))))
    ((%c '--make-event-array-from-vector) v 0 n)))

;;;;
;;;; Clear DEFUN
;;;;

(define (clear-this-command-keys . args)
  "Clear the this-command-keys vector.  Also clear the recent-keys
ring unless KEEP-RECORD is non-nil.  Mirrors C
Fclear_this_command_keys."
  (let ((keep-record (and (pair? args)
                          (let ((v (car args)))
                            (not (or (not v) (eq? v #nil)))))))
    ((%c '--set-this-command-key-count) 0)
    (unless keep-record
      ((%c '--clear-recent-keys-ring)))
    #nil))

;;;;
;;;; set--this-command-keys (internal: novice.el M-x dispatch)
;;;;

(define %meta-bit (modifier-bit 'meta))

(define (%normalize-char c)
  "If C is a byte-8 raw char, fold to its byte representation; else
return C unchanged.  Mirrors the CHAR_BYTE8_P / CHAR_TO_BYTE8 guard
that wraps each fetch_string_char_advance call in the C body."
  (let ((byte-8-p  (%c 'char-byte-8-p))
        (to-byte-8 (%c 'char-to-byte-8)))
    (if (and (not (eq? byte-8-p  #nil))
             (not (eq? (byte-8-p c) #nil)))
        (to-byte-8 c)
        c)))

(define (set--this-command-keys keys)
  "Set the vector returned by `this-command-keys' to be made up of the
characters of KEYS (a string).  Mirrors C Fset__this_command_keys —
internal use only (called from novice.el during M-x dispatch).

Preserves the 248 (\\370 = \"Meta-x\") kludge: when the first character
is 248, the inserted event is the integer (logior ?x meta-modifier)
rather than 248 itself."
  (unless ((%c 'stringp) keys)
    ((%c 'signal) 'wrong-type-argument (list 'stringp keys)))
  ((%c '--set-this-command-key-count) 0)
  ((%c '--set-this-single-command-key-start) 0)
  (let ((len ((%c 'length) keys))
        (aref (%c 'aref)))
    (when (> len 0)
      (let ((key0 (%normalize-char (aref keys 0))))
        (if (= key0 248)
            ((%c '--add-command-key) (logior (char->integer #\x) %meta-bit))
            ((%c '--add-command-key) key0)))
      (let loop ((i 1))
        (when (< i len)
          (let ((key-i (%normalize-char (aref keys i))))
            ((%c '--add-command-key) key-i)
            (loop (+ i 1)))))))
  #nil)

;;;;
;;;; Registration
;;;;

(define (init-this-command-keys-registrations)
  "Register the user-facing DEFUNs against their elisp symbols."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((this-command-keys            ,this-command-keys)
              (this-command-keys-vector     ,this-command-keys-vector)
              (this-single-command-keys     ,this-single-command-keys)
              (this-single-command-raw-keys ,this-single-command-raw-keys)
              (clear-this-command-keys      ,clear-this-command-keys)
              (set--this-command-keys       ,set--this-command-keys))))
