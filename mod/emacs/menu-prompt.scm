(define-module (emacs menu-prompt)
  #:use-module (emacs elisp-ref)      ; %c
  #:use-module (emacs-elisp runtime)
  #:use-module (emacs recent-keys)    ; record-char
  #:use-module (emacs menu-item-parse) ; parse-menu-item, item-properties, ...
  #:use-module (emacs read-char)      ; read-char-entry
  #:declarative? #t
  #:export (record-menu-key
            read-menu-command
            read-char-x-menu-prompt
            read-char-minibuf-menu-prompt
            init-menu-prompt-registrations))

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
;;;
;;; M20 imp-3 — adds read_char_minibuf_menu_prompt
;;; (src/keyboard.c:8720-8939) as read-char-minibuf-menu-prompt.
;;; Coexistence-only, same as imp-2: the C body stays active and
;;; untouched; --rc-read-char-minibuf-menu-prompt still calls it.
;;; imp-4 cuts over the call site.  This module now imports (emacs
;;; read-char) one-way (read-char does not import menu-prompt), so no
;;; load-order cycle yet; imp-4 must re-check when it points
;;; rc-prologue-echo-and-menu! back at this function.

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

;;;;
;;;; read-char-minibuf-menu-prompt
;;;;

;;; True when a read result means "page again" (the help char, or its
;;; unmodified Ctl() equivalent), per brief.org.  obj is the first value
;;; returned by read-char-entry.
(define (page-again? obj more-char)
  (and (integer? obj)
       (not (= obj -2))
       (or (eqv? obj more-char)
           (and (integer? more-char)
                (eqv? obj (logand more-char #o37))))))

;;; Advance past the element at (REST . IDX) within VECTOR, mirroring the
;;; tail of the C inner loop: at the end of a dense table wrap IDX back
;;; to -1 and advance REST, else step IDX or REST.  Returns two values.
(define (advance-scan rest idx vector)
  (cond
   ((and (>= idx 0) (>= (+ idx 1) ((%c 'length) vector)))
    (values ((%c 'cdr-safe) rest) -1))
   ((>= idx 0)
    (values rest (+ idx 1)))
   (else
    (values ((%c 'cdr-safe) rest) idx))))

;;; Build one line of prompt text by scanning the keymap from the current
;;; (REST . IDX)/VECTOR position.  Returns (values menu-strings rest idx
;;; vector notfirst nobindings); the position and nobindings survive for
;;; the next page, matching the C body's loop-carried state.
;;; Note: C's SREF (s, 0) reads a raw byte; ((%c 'aref) s 0) returns the
;;; same integer char code here (elisp aref on a string yields an
;;; integer, not a Guile character), so we compare integers directly.
(define (scan-line width map prompt-strings nlength
                   rest idx vector notfirst nobindings)
  (let loop ((menu-strings prompt-strings)
             (i nlength)
             (rest rest)
             (idx idx)
             (vector vector)
             (notfirst notfirst)
             (nobindings nobindings))
    (cond
     ((>= i width)
      (values menu-strings rest idx vector notfirst nobindings))
     ((%nilp rest)
      (if (or notfirst nobindings)
          (values menu-strings rest idx vector notfirst nobindings)
          ;; Nothing on the line yet and never bound: wrap to the start of
          ;; the map so this is the next page's first line, not a repeat.
          (loop menu-strings i map idx vector notfirst nobindings)))
     (else
      (let ((elt (if (>= idx 0) ((%c 'aref) vector idx)
                     ((%c 'car-safe) rest))))
        (cond
         ((and (< idx 0) ((%c 'vectorp) elt))
          ;; Found a dense table: advance past it, then scan its contents.
          (loop menu-strings i ((%c 'cdr-safe) rest) 0 elt notfirst nobindings))
         (else
          (let* ((event (if (< idx 0) ((%c 'car-safe) elt) idx))
                 (item (if (< idx 0) ((%c 'cdr-safe) elt) elt)))
            (if (and (integer? event) (= 1 (parse-menu-item item -1)))
                ;; It is a menu item — try to fit it on this line.
                (let* ((props (item-properties))
                       (s ((%c 'aref) props ITEM-PROPERTY-NAME))
                       (upcased ((%c 'upcase) event))
                       (downcased ((%c 'downcase) event))
                       (first-char ((%c 'aref) s 0))
                       (char-matches (or (= upcased first-char)
                                         (= downcased first-char)))
                       (desc (if char-matches #nil
                                 ((%c 'single-key-description) event #nil)))
                       (tem ((%c 'aref) props ITEM-PROPERTY-TYPE))
                       (s (if (or (eq? tem QCradio) (eq? tem QCtoggle))
                              (let ((selected ((%c 'aref) props ITEM-PROPERTY-SELECTED)))
                                ((%c 'concat)
                                 (if (eq? tem QCradio)
                                     (if (%nilp selected) "(*) " "( ) ")
                                     (if (%nilp selected) "[X] " "[ ] "))
                                 s))
                              s))
                       (required (+ (string-length s) i 2
                                    (if char-matches 0 (+ (string-length desc) 3)))))
                  (if (or (< required width) (not notfirst))
                      (let* ((menu-strings (if notfirst (cons ", " menu-strings) menu-strings))
                             (i (if notfirst (+ i 2) i))
                             (menu-strings
                              (if (not char-matches)
                                  (let ((tw (min (string-length desc) (- width i))))
                                    (cons " = " (cons (substring desc 0 tw) menu-strings)))
                                  menu-strings))
                             (i (if (not char-matches)
                                    (+ i 3 (min (string-length desc) (- width i)))
                                    i))
                             (thiswidth (min (string-length s) (- width i)))
                             (menu-strings (cons (substring s 0 thiswidth) menu-strings))
                             (i (+ i thiswidth)))
                        (call-with-values
                          (lambda () (advance-scan rest idx vector))
                          (lambda (rest2 idx2)
                            (loop menu-strings i rest2 idx2 vector #t #f))))
                      ;; No room: push "..." and end the line, saving the
                      ;; element for the next page (no advance).
                      (values (cons "..." menu-strings) rest idx vector
                              notfirst nobindings)))
                ;; Not a menu item — advance only.
                (call-with-values
                  (lambda () (advance-scan rest idx vector))
                  (lambda (rest2 idx2)
                    (loop menu-strings i rest2 idx2 vector notfirst nobindings))))))))))))

(define (read-char-minibuf-menu-prompt commandflag map)
  "Read a key from the minibuffer, showing one page of the menu MAP
at a time and paging on `menu-prompt-more-char'.  Returns the chosen
event.  Port of C read_char_minibuf_menu_prompt
(src/keyboard.c:8720-8939)."
  (if (%nilp (symbol-value 'menu-prompting))
      #nil
      (let* ((map ((%c '--get-keymap) map #nil #t))
             (name ((%c 'keymap-prompt) map)))
        (if (not (string? name))
            #nil
            (let* ((width (- ((%c 'frame-text-cols)) 4))
                   (nlength (+ (string-length name) 2))
                   (prompt-strings (list ": " name)))
              (let outer ((rest map) (idx -1) (vector #nil) (nobindings #t))
                (call-with-values
                  (lambda ()
                    (scan-line width map prompt-strings nlength
                               rest idx vector #f nobindings))
                  (lambda (menu-strings rest2 idx2 vector2 notfirst2 nobindings2)
                    ;; Display one page.
                    ((%c '--message3-nolog)
                     (apply (%c 'concat) (reverse menu-strings)))
                    ;; Suppress kbd-macro recording during the read so the
                    ;; help char is not recorded; restore even on signal or
                    ;; quit.  Take a fresh current-kboard smob before save
                    ;; and before restore — do not reuse one across the
                    ;; read-char-entry call (wrong-kboard path).
                    (let* ((kb ((%c 'current-kboard)))
                           (orig ((%c 'kboard-defining-kbd-macro) kb))
                           (obj (dynamic-wind
                                  (lambda ()
                                    ((%c 'set-kboard-defining-kbd-macro) kb #nil))
                                  (lambda ()
                                    (let read-loop ()
                                      (let ((o (call-with-values
                                                (lambda ()
                                                  (read-char-entry commandflag #nil #t #nil
                                                                   ((%c 'current-kboard))))
                                                (lambda (o _) o))))
                                        (if ((%c 'bufferp) o) (read-loop) o))))
                                  (lambda ()
                                    ((%c 'set-kboard-defining-kbd-macro)
                                     ((%c 'current-kboard)) orig)))))
                      (if (page-again? obj (symbol-value 'menu-prompt-more-char))
                          (outer rest2 idx2 vector2 nobindings2)
                          (begin
                            (let ((kb2 ((%c 'current-kboard))))
                              (if (not (%nilp ((%c 'kboard-defining-kbd-macro) kb2)))
                                  ((%c '--store-kbd-macro-char) obj)))
                            obj)))))))))))

;;;;
;;;; Registration
;;;;

(define (init-menu-prompt-registrations)
  "Declare the local-only DEFVAR_* moved here from syms_of_keyboard."
  (for-each
   (lambda (spec)
     (proclaim-special! (car spec))
     (unless (symbol-default-bound? (car spec))
       (set-symbol-default-value! (car spec) (cadr spec))))
   `((menu-prompting         ,#t)
     (menu-prompt-more-char  32))))
