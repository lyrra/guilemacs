(define-module (emacs this-command-keys)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (this-command-keys
            this-command-keys-vector
            this-single-command-keys
            this-single-command-raw-keys
            clear-this-command-keys
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

(define (%c name) (symbol-function name))

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
;;;; Registration
;;;;

(define (init-this-command-keys-registrations)
  "Register the five user-facing DEFUNs against their elisp symbols."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((this-command-keys            ,this-command-keys)
              (this-command-keys-vector     ,this-command-keys-vector)
              (this-single-command-keys     ,this-single-command-keys)
              (this-single-command-raw-keys ,this-single-command-raw-keys)
              (clear-this-command-keys      ,clear-this-command-keys))))
