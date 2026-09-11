(define-module (emacs menu-item-parse)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (parse-menu-item
            menu-item-eval-property
            item-properties
            ITEM-PROPERTY-ITEM ITEM-PROPERTY-NAME ITEM-PROPERTY-DEF
            ITEM-PROPERTY-MAP ITEM-PROPERTY-TYPE ITEM-PROPERTY-KEYEQ
            ITEM-PROPERTY-SELECTED ITEM-PROPERTY-HELP
            ITEM-PROPERTY-ENABLE ITEM-PROPERTY-MAX
            ;; Keyword literals shared with tab-bar-items
            QCenable QCvisible QChelp QCfilter QCbutton
            QCtoggle QCradio
            ;; Separator predicate shared with tab-bar-items and
            ;; tool-bar-items.
            menu-separator-names menu-separator-name?
            ;; Shared with (emacs help-echo) — M16 imp-2 (brief.org).
            help-echo-substitute-command-keys
            init-menu-item-parse-registrations))

;;; M10 imp-1.3 — complete Scheme parse-menu-item port.
;;; Coexists with C parse_menu_item (keyboard.c:8836+), which is
;;; untouched until imp-1.4 cuts it over to SCM_CALL_2.

;;; --- imp-1.2 infrastructure -------------------------------------------

(defelisp %--menu-item-eval-property --menu-item-eval-property)
(defelisp %--item-properties-vector --item-properties-vector)

;;; Slot indexes — must match enum item_property_idx in keyboard.h:294-318.
(define ITEM-PROPERTY-ITEM      0)
(define ITEM-PROPERTY-NAME      1)
(define ITEM-PROPERTY-DEF       2)
(define ITEM-PROPERTY-MAP       3)
(define ITEM-PROPERTY-TYPE      4)
(define ITEM-PROPERTY-KEYEQ     5)
(define ITEM-PROPERTY-SELECTED  6)
(define ITEM-PROPERTY-HELP      7)
(define ITEM-PROPERTY-ENABLE    8)
(define ITEM-PROPERTY-MAX       ITEM-PROPERTY-ENABLE)

;;; Signal-safe eval for menu-item property forms (:enable, :visible, etc.).
;;; Errors → nil (matches C safe_call behavior).  Quit signals re-raise.
(define (menu-item-eval-property sexpr)
  ((force %--menu-item-eval-property) sexpr))

;;; Return the staticpro'd item_properties vector (lazy-inited).
;;; Scheme reads/writes via elisp aref / aset (item_properties is an
;;; elisp vector, not a Guile vector, so vector-ref / vector-set! don't work).
(define (item-properties)
  ((force %--item-properties-vector)))

;;; Port of C menu_separator_name_p (keyboard.c:8575).  Returns #t if
;;; LABEL is a recognized menu separator name.  Matches:
;;;   1. Exactly 4+ chars: "--" followed by a separator-name suffix
;;;      (space, no-line, single-line, double-line, single-dashed-line,
;;;       double-dashed-line, shadow-etched-in, shadow-etched-out,
;;;       shadow-etched-in-dash, shadow-etched-out-dash)
;;;   2. Any string consisting solely of dashes ("--", "---", etc.)
;;;
;;; C copy at keyboard.c:8575 stays for native GUI callers.
;;; (androidmenu.c, w32menu.c and haikumenu.c belonged to dropped
;;; platforms; gtkutil.c and xdisp.c remain.)
(define menu-separator-names
  '("space" "no-line" "single-line" "double-line"
    "single-dashed-line" "double-dashed-line"
    "shadow-etched-in" "shadow-etched-out"
    "shadow-etched-in-dash" "shadow-etched-out-dash"))

(define (menu-separator-name? label)
  (and (string? label)
       (let ((len (string-length label)))
         (cond
          ;; Case 1: "--SUFFIX" format (>=4 chars, starts with "--",
          ;; 3rd char not '-', and SUFFIX matches a known name)
          ((and (>= len 4)
                (char=? (string-ref label 0) #\-)
                (char=? (string-ref label 1) #\-)
                (not (char=? (string-ref label 2) #\-)))
           (let ((suffix (substring label 2)))
             (let loop ((rest menu-separator-names))
               (and (pair? rest)
                    (or (string=? suffix (car rest))
                        (loop (cdr rest)))))))
          ;; Case 2: all dashes
          (else
           (let loop ((i 0))
             (if (= i len)
                 (> len 0)         ; at least one dash
                 (and (char=? (string-ref label i) #\-)
                      (loop (1+ i))))))))))

;;; --- imp-1.3: Elisp DEFUN references ----------------------------------

(defelisp %get                    get)
;; Bind %concat2 to elisp `concat' (variadic), not the C-only
;; `concat2' helper — the latter is not registered as a DEFUN, so
;; defelisp would silently resolve it to #nil and application would
;; crash with "Wrong type to apply: #nil" the first time redisplay
;; hits the keyeq branch (see feedback_c_helper_scheme_proc_trap.md).
(defelisp %concat2                concat)
(defelisp %get-text-property      get-text-property)
(defelisp %substitute-command-keys substitute-command-keys)
(defelisp %key-binding            key-binding)
(defelisp %where-is-internal      where-is-internal)
(defelisp %key-description        key-description)
(defelisp %funcall                funcall)
(defelisp %list                   list)
(defelisp %aref                  aref)
(defelisp %aset                  aset)
(defelisp %vectorp               vectorp)
(defelisp %functionp              functionp)
(defelisp %--get-keymap           --get-keymap)

;;; --- Keyword symbols (elisp colon-symbols) ----------------------------
;;; These match C DEFSYMs: QCenable, QCvisible, QChelp, QCfilter,
;;; QCbutton, QCkeys, QCkey_sequence, QCtoggle, QCradio.
;;; Elisp colon-symbols (:enable etc.) cross the FFI as Guile keywords
;;; (#:enable), not Guile symbols.  Use keyword syntax so eq? works.

(define QCenable       #:enable)
(define QCvisible      #:visible)
(define QChelp         #:help)
(define QCfilter       #:filter)
(define QCbutton       #:button)
(define QCkeys         #:keys)
(define QCkey-sequence #:key-sequence)
(define QCtoggle       #:toggle)
(define QCradio        #:radio)

;;; --- Helpers ----------------------------------------------------------

;;; Inline of C's help_echo_substitute_command_keys (keyboard.c:2768).
;;; If HELP is a non-empty string whose first char has a non-nil
;;; help-echo-inhibit-substitution text property, return HELP as-is;
;;; otherwise run substitute-command-keys on it.
(define (help-echo-substitute-command-keys help)
  (if (and (string? help)
           (> (string-length help) 0)
           (not (eq? #nil
                     ((force %get-text-property)
                      0 'help-echo-inhibit-substitution help))))
      help
      ((force %substitute-command-keys) help)))

;;; Read the dynamic variable enable-disabled-menus-and-buttons.
;;; C side: DEFVAR_LISP at keyboard.c:15160.
(define (enable-disabled-menus-and-buttons)
  (symbol-value 'enable-disabled-menus-and-buttons))

;;; --- parse-menu-item --------------------------------------------------

;;; Port of C parse_menu_item (keyboard.c:8836–9119, ~278 lines).
;;; Returns 1 (keep item) or 0 (skip item).
;;; Side effect: mutates the shared (item-properties) vector.
;;;
;;; Signature: (parse-menu-item item inmenubar) → 0 or 1
;;;   inmenubar > 0 → menu-bar top level
;;;   inmenubar < 0 → keyboard menu
;;;   inmenubar = 0 → submenu

(define (parse-menu-item item inmenubar)
  ;; Use call/cc so early returns can jump straight to the exit value.
  (call/cc
   (lambda (return)
     ;; Must be a cons — otherwise not a menu item at all.
     (unless (pair? item)
       (return 0))

     (let* ((props ((force %--item-properties-vector)))
            (filter #nil)
            (keyhint #nil)
            (def #nil)
            (tem #nil)
            (item-string #nil)
            (start #nil))

       ;; Reset optional slots to nil (DEF through MAX); set ENABLE to t.
       (do ((i ITEM-PROPERTY-DEF (1+ i)))
           ((> i ITEM-PROPERTY-MAX))
         ((force %aset) props i #nil))
       ((force %aset) props ITEM-PROPERTY-ENABLE #t)

       ;; GC-anchor: save item in slot 0 before we start destructuring.
       ((force %aset) props ITEM-PROPERTY-ITEM item)

       (set! item-string (car item))
       (set! start item)
       (set! item (cdr item))

       (cond
        ;; --- Old format: car is a string ---------------------------------
        ((string? item-string)
         ((force %aset) props ITEM-PROPERTY-NAME item-string)

         ;; Maybe a help string.
         (when (and (pair? item) (string? (car item)))
           ((force %aset) props ITEM-PROPERTY-HELP
                        (help-echo-substitute-command-keys (car item)))
           (set! start item)
           (set! item (cdr item)))

         ;; Maybe an obsolete key-binding cache:
         ;; (nil . "...") or ([...] . "...") — skip it.
         (when (and (pair? item)
                    (pair? (car item))
                    (let ((caar (car (car item))))
                      (or (eq? caar #nil)
                          (not (eq? #nil ((force %vectorp) caar))))))
           (set! item (cdr item)))

         ;; Real definition.
         ((force %aset) props ITEM-PROPERTY-DEF item)

         ;; Old-format enable property: symbol's menu-enable property.
         (when (symbol? item)
           (set! tem ((force %get) item 'menu-enable))
           (if (not (eq? #nil (enable-disabled-menus-and-buttons)))
               ((force %aset) props ITEM-PROPERTY-ENABLE #t)
               (unless (eq? tem #nil)
                 ((force %aset) props ITEM-PROPERTY-ENABLE tem)))))

        ;; --- New format: car is menu-item symbol -------------------------
        ((and (eq? item-string 'menu-item) (pair? item))
         ((force %aset) props ITEM-PROPERTY-NAME (car item))
         (set! start (cdr item))
         (if (pair? start)
             (begin
               ;; Real binding.
               ((force %aset) props ITEM-PROPERTY-DEF (car start))
               (set! item (cdr start))

               ;; Obsolete cache list with key equivalences.
               (when (and (pair? item) (pair? (car item)))
                 (set! item (cdr item)))

               ;; Parse keyword properties via plist walk.
               ;; C uses FOR_EACH_TAIL with manual advance — we
               ;; mirror that: key = car(lst), advance past key,
               ;; val = car(rest), then advance past val.
               (let plist-loop ((lst item))
                 ;; Guard: both key AND value must be present — matches
                 ;; C's FOR_EACH_TAIL + manual advance + CONSP check.
                 ;; A lone key (e.g. (:enable)) terminates the loop
                 ;; naturally; post-format processing continues.
                 (when (and (pair? lst) (pair? (cdr lst)))
                   (let ((key (car lst))
                         (val (cadr lst))
                         (rest (cdr lst)))      ; (value . remaining-plist)
                     (cond
                      ((eq? key QCenable)
                       (if (not (eq? #nil (enable-disabled-menus-and-buttons)))
                           ((force %aset) props ITEM-PROPERTY-ENABLE #t)
                           ((force %aset) props ITEM-PROPERTY-ENABLE val)))
                      ((eq? key QCvisible)
                       ;; Visible property eval'd to nil → skip item.
                       (when (eq? #nil (menu-item-eval-property val))
                         (return 0)))
                      ((eq? key QChelp)
                       (let ((help val))
                         (when (string? help)
                           (set! help (help-echo-substitute-command-keys help)))
                         ((force %aset) props ITEM-PROPERTY-HELP help)))
                      ((eq? key QCfilter)
                       (set! filter rest))     ; store the cons cell (value . next)
                      ((eq? key QCkey-sequence)
                       (when (or (symbol? val) (string? val) (vector? val))
                         (set! keyhint rest))) ; GC-protect: store cons cell
                      ((eq? key QCkeys)
                       (cond
                        (((force %functionp) val)
                         ((force %aset) props ITEM-PROPERTY-KEYEQ
                                      ((force %funcall) val)))
                        ((or (pair? val) (string? val))
                         ((force %aset) props ITEM-PROPERTY-KEYEQ val))))
                      ((eq? key QCbutton)
                       (when (pair? val)
                         (let ((type (car val)))
                           (when (or (eq? type QCtoggle) (eq? type QCradio))
                             ((force %aset) props ITEM-PROPERTY-SELECTED (cdr val))
                             ((force %aset) props ITEM-PROPERTY-TYPE type))))))
                     (plist-loop (cdr rest))))))
             ;; No real binding — skip unless inmenubar or non-nil start.
             (when (or (not (zero? inmenubar)) (not (eq? #nil start)))
               (return 0))))

        ;; --- Neither old nor new format — not a menu item ----------------
        (else
         (return 0)))

       ;; --- Post-format: evaluate item_string if not already a string ----
       (set! item-string ((force %aref) props ITEM-PROPERTY-NAME))
       (unless (string? item-string)
         (set! item-string (menu-item-eval-property item-string))
         (unless (string? item-string)
           (return 0))
         ((force %aset) props ITEM-PROPERTY-NAME item-string))

       ;; --- Apply :filter if present -------------------------------------
       (set! def ((force %aref) props ITEM-PROPERTY-DEF))
       (unless (eq? filter #nil)
         (set! def (menu-item-eval-property
                    ((force %list) (car filter)
                     ((force %list) 'quote def))))
         ((force %aset) props ITEM-PROPERTY-DEF def))

       ;; --- Enable / disable ---------------------------------------------
       (set! tem ((force %aref) props ITEM-PROPERTY-ENABLE))
       (unless (eq? tem #t)
         (set! tem (menu-item-eval-property tem))
         (when (and (not (zero? inmenubar)) (eq? tem #nil))
           (return 0))           ; disabled in menu bar → skip
         ((force %aset) props ITEM-PROPERTY-ENABLE tem))

       ;; --- No definition → unselectable text (OK in submenu only) -------
       (when (eq? def #nil)
         (return (if (zero? inmenubar) 1 0)))

       ;; --- Subkeymap detection ------------------------------------------
       (set! def ((force %aref) props ITEM-PROPERTY-DEF))
       (set! tem ((force %--get-keymap) def #nil #t))
       (when (pair? tem)
         ((force %aset) props ITEM-PROPERTY-MAP tem)
         ((force %aset) props ITEM-PROPERTY-DEF tem)
         (return 1))

       ;; --- Menu bar top level → done (no key-eq display) ----------------
       (when (> inmenubar 0)
         (return 1))

       ;; --- Key-binding display for commands -----------------------------
       (let ((keyeq ((force %aref) props ITEM-PROPERTY-KEYEQ)))
         (if (and (string? keyeq) (not (pair? keyhint)))
             ;; Simple case: :keys gave a string, no :key-sequence hint.
             (set! keyeq ((force %concat2) "  "
                          ((force %substitute-command-keys) keyeq)))
             (let ((prefix keyeq)
                   (keys #nil))
               (if (pair? prefix)
                   (begin
                     (set! def (car prefix))
                     (set! prefix (cdr prefix)))
                   (set! def ((force %aref) props ITEM-PROPERTY-DEF)))

               ;; Check :key-sequence hint.
               (when (and (pair? keyhint)
                          (not (eq? (car keyhint) #nil)))
                 (set! keys (car keyhint))
                 (set! tem ((force %key-binding) keys #nil #nil #nil))
                 (when (or (eq? tem #nil)
                           (and (not (eq? tem def))
                                (not (and (symbol? def)
                                          (eq? tem (symbol-function def))))))
                   (set! keys #nil)))

               (when (eq? keys #nil)
                 (set! keys ((force %where-is-internal) def #nil #t #nil #nil)))

               (if (not (eq? keys #nil))
                   (begin
                     (set! tem ((force %key-description) keys #nil))
                     (when (pair? prefix)
                       (when (string? (car prefix))
                         (set! tem ((force %concat2) (car prefix) tem)))
                       (when (string? (cdr prefix))
                         (set! tem ((force %concat2) tem (cdr prefix)))))
                     (set! keyeq ((force %concat2) "  " tem)))
                   (set! keyeq #nil))))
         ((force %aset) props ITEM-PROPERTY-KEYEQ keyeq))

       ;; --- Radio / toggle button selected state -------------------------
       (set! tem ((force %aref) props ITEM-PROPERTY-SELECTED))
       (unless (eq? tem #nil)
         ((force %aset) props ITEM-PROPERTY-SELECTED
                      (menu-item-eval-property tem)))

       1))))

;;;;
;;;; Registration
;;;;

(define (init-menu-item-parse-registrations)
  "Declare the local-only DEFVAR_* moved here from syms_of_keyboard."
  (for-each
   (lambda (spec)
     (proclaim-special! (car spec))
     (unless (symbol-default-bound? (car spec))
       (set-symbol-default-value! (car spec) (cadr spec))))
   `((enable-disabled-menus-and-buttons ,#nil))))
