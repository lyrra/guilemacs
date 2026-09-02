(define-module (emacs echo)
  #:use-module (emacs elisp-ref)      ; %c
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (echo-keystrokes-p
            echo-add-key
            echo-dash
            echo-update
            echo-now
            echo-length
            echo-truncate
            init-echo-registrations))

;;; M18 imp-2 — Scheme echo bodies ported from src/keyboard.c.
;;;
;;; Ports echo_keystrokes_p, echo_add_key, echo_dash, echo_update,
;;; echo_now, echo_length, echo_truncate, plus the private
;;; echo-help-char-p (help_char_p's logic only — its C body stays
;;; active and untouched).  Coexistence-only: every C body keeps
;;; running; the imp-3 commit cuts over.  cancel_echoing and
;;; add_command_key stay C (Finding 6 default — the vector-growth loop
;;; is not ported in this commit).
;;;
;;; add-text-properties (resolved via %c, bound to the (emacs
;;; text-properties) implementation) is used for the hint's face
;;; property.  Conventions follow (emacs recent-keys): inline
;;; (%c 'foo) calls, a truthy? helper, elisp vars via symbol-value,
;;; #nil is elisp nil, and the kboard handle comes from
;;; (force %current-kboard).

(define %current-kboard (delay (%c 'current-kboard)))

(define (truthy? x)
  "Elisp truthiness: everything except #nil is true."
  (not (eq? x #nil)))

(define (%nilp x)
  "True iff X is elisp nil."
  (eq? x #nil))

;;;;
;;;; echo-keystrokes-p
;;;;

(define (echo-keystrokes-p)
  "Return #t if the user wants keystrokes echoed.
Port of C echo_keystrokes_p (src/keyboard.c:472-477): true when
`echo-keystrokes' is a float > 0.0 or a fixnum > 0, else false."
  (let ((v (symbol-value 'echo-keystrokes)))
    (cond
     ((and (number? v) (inexact? v)) (> v 0.0))
     ((integer? v) (> v 0))
     (else #f))))

;;;;
;;;; echo-help-char-p (private helper)
;;;;

(define (echo-help-char-p c)
  "Return #t if C should be recognized as the help character.
Port of C help_char_p's logic (src/keyboard.c:4424-4433): true if C is
EQ to `help-char' or a member of `help-event-list' (memq comparison,
eq?).  The C body itself is untouched."
  (or (eq? c (symbol-value 'help-char))
      (let loop ((tail (symbol-value 'help-event-list)))
        (cond
         ((not (pair? tail)) #f)
         ((eq? c (car tail)) #t)
         (else (loop (cdr tail)))))))

;;;;
;;;; echo-add-key
;;;;

(define (echo-add-key c)
  "Add C to the echo string without echoing it immediately.
Port of C echo_add_key (src/keyboard.c:484-533).  Appends the
description of event C to current-kboard's echo-string, prefixed by a
space separator when the prior echo-string is non-empty.  C may be a
character (pretty-printed via single-key-description) or a symbol
(whose name is printed); a composite event is normalized to its head.
When the prior echo-string was empty/nil and C is a help character,
append the fixed help hint with the `face . help-key-binding' text
property on the `?' and `C-q'."
  (let* ((kb          ((force %current-kboard)))
         (old-string  ((%c 'kboard-echo-string) kb))
         (sep         (if (and (string? old-string)
                               (> ((%c 'length) old-string) 0))
                          " " ""))
         ;; Composite events: use the head symbol/char.
         (head        (if (pair? c) (car c) c))
         (desc        (cond
                       ((integer? head)
                        ((%c 'single-key-description) head #t))
                       ((symbol? head)
                        (symbol-name head))
                       (else "")))
         (piece       ((%c 'concat) sep desc)))
    (when (and (or (not (string? old-string))
                   (= ((%c 'length) old-string) 0))
               (echo-help-char-p head))
      ;; 1:1 with the C AUTO_STRING/AUTO_LIST2 + two Fadd_text_properties
      ;; calls at keyboard.c:523-526: place the face on the hint's `?'
      ;; (offset 7-8) and `C-q' (offset 30-33).  add-text-properties on a
      ;; plain string returns a fresh string carrying the properties (it
      ;; does not mutate its argument), so capture that return value and
      ;; concatenate the wrapped string, not the original literal.
      (let ((hint ((%c 'add-text-properties)
                   7 8 (list 'face 'help-key-binding)
                   " (Type ? for further options, C-q for quick help)")))
        ((%c 'add-text-properties) 30 33 (list 'face 'help-key-binding) hint)
        (set! piece ((%c 'concat) piece hint))))
    ((%c 'set-kboard-echo-string) kb ((%c 'concat) old-string piece))))

;;;;
;;;; echo-dash
;;;;

(define (echo-dash)
  "Temporarily add a dash to the end of the echo string.
Port of C echo_dash (src/keyboard.c:540-586).  All four guard branches
early-return with no side effect; the success path appends `-' and
calls echo-now."
  (let* ((kb ((force %current-kboard)))
         (es ((%c 'kboard-echo-string) kb)))
    ;; Guard 1: not echoing at all.
    (unless (%nilp es)
      ;; Guard 2: not immediate-echo and empty string.
      (unless (and (%nilp ((%c '--current-kboard-immediate-echo-p)))
                   (= ((%c 'length) es) 0))
        ;; Guard 3: just printed a prompt (echo-prompt same length).
        (let ((prompt ((%c 'kboard-echo-prompt) kb)))
          (unless (and (string? prompt)
                       (= ((%c 'length) prompt) ((%c 'length) es)))
            ;; Guard 4: already has a dash or keystroke-help suffix.
            (unless (and (> ((%c 'length) es) 1)
                         (let* ((n    ((%c 'length) es))
                                (last ((%c 'aref) es (- n 1)))
                                (prev ((%c 'aref) es (- n 2))))
                           (or (and (= last (char->integer #\-))
                                    (not (= prev (char->integer #\space))))
                               (and (truthy? (symbol-value 'echo-keystrokes-help))
                                    (= last (char->integer #\)))
                                    (= prev (char->integer #\p))))))
              ;; Success: append a dash, then keystroke help if enabled.
              (let ((es2 ((%c 'concat) es "-")))
                ((%c 'set-kboard-echo-string) kb es2)
                (when (truthy? (symbol-value 'echo-keystrokes-help))
                  ((%c 'set-kboard-echo-string) kb
                   ((%c 'help--append-keystrokes-help) es2)))
                (echo-now)))))))))

;;;;
;;;; echo-update
;;;;

(define (echo-update)
  "Update the echo string for the current key sequence.
Port of C echo_update (src/keyboard.c:589-613).  When the current
kboard's immediate-echo is set, rebuild the echo-string from the
prompt/prefix and walk this-command-keys, echoing every key except
mouse-movement events, then call echo-now."
  (when (truthy? ((%c '--current-kboard-immediate-echo-p)))
    (let* ((kb     ((force %current-kboard)))
           (prompt ((%c 'kboard-echo-prompt) kb))
           (prefix ((%c 'internal-echo-keystrokes-prefix)))
           (v      ((%c '--this-command-keys)))
           (n      ((%c '--this-command-key-count))))
      ((%c 'set-kboard-echo-string) kb
       (cond ((%nilp prompt) prefix)
             ((%nilp prefix) prompt)
             (else ((%c 'concat) prompt prefix))))
      (let loop ((i 0))
        (when (< i n)
          (let ((c ((%c 'aref) v i)))
            ;; Mouse-movement events are not echoed.
            (unless (and (pair? c)
                         (eq? ((%c 'get) (car c) 'event-kind) 'mouse-movement))
              (echo-add-key c))
            (loop (+ i 1)))))
      (echo-now))))

;;;;
;;;; echo-now
;;;;

(define (echo-now)
  "Display the current echo string and begin echoing if not already.
Port of C echo_now (src/keyboard.c:619-642).  Sets immediate-echo and
echoes (via echo-update + echo-dash) only when not already echoing;
then flips the C `echoing' flag around a message3-nolog display, pins
the echo message-buffer/kboard, and throws to read-char when a quit is
pending.  The commented-out echo_keystrokes_p guard in the C source
is dead — not ported."
  (if (not (truthy? ((%c '--current-kboard-immediate-echo-p))))
      (begin
        ((%c '--set-current-kboard-immediate-echo) #t)
        (echo-update)
        ;; Put a dash at the end to invite the user to type more.
        (echo-dash)))
  ((%c '--set-echoing!) #t)
  ((%c '--message3-nolog) ((%c 'kboard-echo-string) ((force %current-kboard))))
  ((%c '--set-echoing!) #nil)
  ;; Record in what buffer we echoed, and from which kboard.
  ((%c '--rc-pin-echo-message-buffer-to-current))
  ((%c '--rc-pin-echo-kboard-to-current))
  (when (and (truthy? ((%c '--waiting-for-input-p)))
             (truthy? (symbol-value 'quit-flag)))
    ((%c '--quit-throw-to-read-char))))

;;;;
;;;; echo-length
;;;;

(define (echo-length)
  "Return the length (in characters) of the current echo string.
Port of C echo_length (src/keyboard.c:660-665).  0 when the echo
string is nil."
  (let ((es ((%c 'kboard-echo-string) ((force %current-kboard)))))
    (if (string? es) ((%c 'length) es) 0)))

;;;;
;;;; echo-truncate
;;;;

(define (echo-truncate nchars)
  "Truncate the current echo message to its first NCHARS chars.
Port of C echo_truncate (src/keyboard.c:672-680).  Always calls
`--truncate-echo-area' with NCHARS, whether or not the echo-string was
actually shortened."
  (let* ((kb ((force %current-kboard)))
         (es ((%c 'kboard-echo-string) kb)))
    (when (and (string? es) (> ((%c 'length) es) nchars))
      ((%c 'set-kboard-echo-string) kb ((%c 'substring) es 0 nchars)))
    ((%c '--truncate-echo-area) nchars)))

;;;;
;;;; Registration
;;;;

(define (init-echo-registrations)
  "Declare the local-only DEFVAR_* moved here from syms_of_keyboard."
  (for-each
   (lambda (spec)
     (proclaim-special! (car spec))
     (unless (symbol-default-bound? (car spec))
       (set-symbol-default-value! (car spec) (cadr spec))))
   `((echo-keystrokes-help ,#t))))
