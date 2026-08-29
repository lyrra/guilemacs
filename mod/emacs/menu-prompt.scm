(define-module (emacs menu-prompt)
  #:use-module (emacs elisp-ref)      ; %c
  #:use-module (emacs-elisp runtime)
  #:use-module (emacs recent-keys)    ; record-char
  #:declarative? #t
  #:export (record-menu-key
            read-menu-command
            read-char-x-menu-prompt))

;;; M20 imp-2 — Scheme menu-prompt bodies ported from src/keyboard.c.
;;;
;;; Ports record_menu_key (keyboard.c:4327-4346), read_menu_command
;;; (keyboard.c:2627-2648), and read_char_x_menu_prompt
;;; (keyboard.c:8659-8718).  Coexistence-only: every C body stays
;;; active and untouched; the imp-4 commit cuts over the call sites.
;;; read_key_sequence itself is NOT ported — it is reached only through
;;; the dedicated --rc-read-key-sequence-menu shim (keyboard.c), whose
;;; fixed flags match read_menu_command exactly (the existing
;;; --read-key-sequence-and-vector hardcodes fix_current_buffer and
;;; prevent_redisplay = false, which read_menu_command needs true for).
;;;
;;; used-mouse-menu is an out-param in C; the Scheme function returns it
;;; as a second value, the same convention read-char-entry uses for
;;; read_char's own used-mouse-menu flag.

(define record-char (@ (emacs recent-keys) record-char))

(define (%nilp x) (eq? x #nil))

;;;;
;;;; record-menu-key
;;;;

(define (record-menu-key c)
  "Record C as a key that came from a mouse menu: echo, record,
and count it.  Port of C record_menu_key (src/keyboard.c:4327-4346)."
  ((%c '--clear-message-1-0))
  (record-char c)
  ((%c '--rc-clear-echo-at-next-pause))
  ((%c '--add-command-key) c)
  ((%c '--echo-update))
  (set-symbol-value! 'last-input-event c)
  ((%c '--rc-inc-num-input-events))
  #nil)

;;;;
;;;; read-menu-command
;;;;

(define (read-menu-command)
  "Read one key sequence for menu navigation, with keystroke
echo suppressed.  Port of C read_menu_command
(src/keyboard.c:2627-2648)."
  (let* ((saved (symbol-value 'echo-keystrokes))
         (result
          (dynamic-wind
            (lambda () (set-symbol-value! 'echo-keystrokes 0))
            (lambda () ((%c '--rc-read-key-sequence-menu)))
            (lambda () (set-symbol-value! 'echo-keystrokes saved)))))
    (when (%nilp ((%c 'frame-live-p) ((%c 'selected-frame))))
      ((%c 'kill-emacs) #nil #nil))
    (if (or (equal? result -1)
            (and (vector? result) (= (vector-length result) 0)))
        #t
        ((%c '--read-key-sequence-cmd)))))

;;;;
;;;; read-char-x-menu-prompt
;;;;

(define (read-char-x-menu-prompt map prev-event)
  "Try an X/GTK popup menu for the next key.  Returns two values:
the event (or #nil/#t), and a boolean, true exactly when a menu
was displayed.  Port of C read_char_x_menu_prompt
(src/keyboard.c:8659-8718)."
  (cond
   ((%nilp (symbol-value 'menu-prompting))
    (values #nil #f))
   ((and (pair? prev-event)
         (not (memq (car prev-event) '(menu-bar tab-bar tool-bar))))
    (let* ((keymap ((%c '--get-keymap) map #nil #t))
           (raw ((%c '--x-popup-menu-1) prev-event keymap))
           (value
            (cond
             ((pair? raw)
              (record-menu-key (car raw))
              (let loop ((tem (cdr raw)))
                (when (pair? tem)
                  (record-menu-key (car tem))
                  (when (or (symbol? (car tem)) (integer? (car tem)))
                    ((%c 'setcar) tem (cons (car tem) 'disabled)))
                  (loop (cdr tem))))
              (set-symbol-value!
               'unread-command-events
               (append (cdr raw) (symbol-value 'unread-command-events)))
              (car raw))
             ((%nilp raw) #t)
             (else raw))))
      (values value #t)))
   (else (values #nil #f))))
