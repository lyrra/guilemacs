(define-module (emacs recent-keys)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (recent-keys
            lossage-size
            init-recent-keys-registrations))

;;; M3 — recent-keys / lossage-size ported from keyboard.c.
;;;
;;; The recent-keys ring stays C-owned in keyboard.c (recent_keys
;;; vector, recent_keys_index, total_keys, lossage_limit).  Updating
;;; the ring from C record_char remains the per-keystroke hot path.
;;; The two user-facing DEFUNs ported here only run on `M-x recent-keys'
;;; and `M-x lossage-size' — fine for an FFI hop.
;;;
;;; See docs/keyboard.org §M3.  The C primitives this module wraps
;;; live in src/keyboard.c with the `--' prefix:
;;;   --recent-keys-ring, --recent-keys-index, --total-keys,
;;;   --lossage-limit, --min-num-recent-keys, --max-num-recent-keys,
;;;   --update-recent-keys, --make-event-array-from-vector.

(define (%c name) (symbol-function name))

(define (%user-error msg)
  ;; Elisp `signal' isn't bound in Scheme top-level — go through the
  ;; elisp symbol table.  Same shape as `(user-error MSG)' from elisp.
  ((%c 'signal) 'user-error (list msg)))

;;;;
;;;; lossage-size
;;;;

(define (lossage-size . args)
  "Return or set the maximum number of keystrokes recorded.
If called with a non-nil ARG, set the limit and return it.
Mirrors C Flossage_size; signals user-error on invalid input."
  (let ((arg (and (pair? args) (car args))))
    (cond
     ((or (not arg) (eq? arg #nil))
      ((%c '--lossage-limit)))
     (else
      (unless (and (integer? arg) (>= arg 0))
        (%user-error "Value must be a positive integer"))
      (let* ((osize  ((%c '--lossage-limit)))
             (minsz  ((%c '--min-num-recent-keys)))
             (maxsz  ((%c '--max-num-recent-keys))))
        (cond
         ((= arg osize)
          osize)
         ((< arg minsz)
          (%user-error (format #f "Value must be >= ~a" minsz)))
         ((> arg maxsz)
          (%user-error (format #f "Value must be <= ~a" maxsz)))
         (else
          (let* ((total ((%c '--total-keys)))
                 (kept  (if (> arg osize) total (min arg total))))
            ((%c '--update-recent-keys) arg kept)
            ((%c '--lossage-limit))))))))))

;;;;
;;;; recent-keys
;;;;

(define (recent-keys . args)
  "Return vector of last few events, not counting those from keyboard
macros.  If INCLUDE-CMDS is non-nil, include commands run as pseudo-events
of the form (nil . COMMAND).  Mirrors C Frecent_keys."
  (let ((include-cmds (and (pair? args)
                           (let ((v (car args))) (not (or (not v) (eq? v #nil)))))))
    (let ((ring  ((%c '--recent-keys-ring)))
          (idx   ((%c '--recent-keys-index)))
          (total ((%c '--total-keys)))
          (limit ((%c '--lossage-limit))))
      (cond
       ((or (zero? total)
            (and include-cmds (< total limit)))
        ;; Short ring: extract the prefix directly.  Returns a string
        ;; if every event fits in a unibyte char, otherwise a vector.
        ((%c '--make-event-array-from-vector) ring 0 total))
       (else
        ;; Full ring: walk circularly starting from the oldest, filter
        ;; out (nil . CMD) pseudo-events unless include-cmds is set.
        (let* ((start (if (< total limit) 0 idx))
               (acc '())
               (acc
                (let loop ((i start) (acc acc) (first? #t))
                  (cond
                   ((and (not first?) (= i idx)) acc)
                   (else
                    (let* ((e (vector-ref ring i))
                           (keep? (or include-cmds
                                      (not (pair? e))
                                      (not (or (eq? (car e) #nil)
                                               (not (car e))))))
                           (acc (if keep? (cons e acc) acc))
                           (j (if (>= (+ i 1) limit) 0 (+ i 1))))
                      (loop j acc #f)))))))
          (list->vector (reverse acc))))))))

;;;;
;;;; Registration
;;;;

(define (init-recent-keys-registrations)
  "Register the user-facing DEFUNs against their elisp symbols."
  (for-each (lambda (sym-fun)
              (set-symbol-function! (car sym-fun) (cadr sym-fun)))
            `((recent-keys  ,recent-keys)
              (lossage-size ,lossage-size))))
