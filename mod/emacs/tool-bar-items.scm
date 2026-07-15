(define-module (emacs tool-bar-items)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs menu-item-parse)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (tool-bar-items
            parse-tool-bar-item
            process-tool-bar-item
            TOOL-BAR-ITEM-KEY
            TOOL-BAR-ITEM-ENABLED-P
            TOOL-BAR-ITEM-SELECTED-P
            TOOL-BAR-ITEM-CAPTION
            TOOL-BAR-ITEM-IMAGES
            TOOL-BAR-ITEM-BINDING
            TOOL-BAR-ITEM-TYPE
            TOOL-BAR-ITEM-HELP
            TOOL-BAR-ITEM-RTL-IMAGE
            TOOL-BAR-ITEM-LABEL
            TOOL-BAR-ITEM-VERT-ONLY
            TOOL-BAR-ITEM-WRAP
            TOOL-BAR-ITEM-NSLOTS))

;;; M10 imp-3 — Scheme port of tool_bar_items.
;;; C tool_bar_items in keyboard.c will become a SCM_CALL_1 shim into this
;;; module.  Static vectors (tool_bar_items_vector,
;;; tool_bar_item_properties, ntool_bar_items) still live in C and are
;;; mutated via the imp-3.1 DEFUNs; staticpro keeps them GC-safe.
;;;
;;; Decomposition mirrors the three C functions:
;;;   parse-tool-bar-item   — fill tool_bar_item_properties vector (→ 0/1)
;;;   process-tool-bar-item — callback for map-keymap (side-effecting)
;;;   tool-bar-items        — main entry (→ (cons vector nitems))
;;;
;;; Slot constants match enum tool_bar_item_idx (dispextern.h:3410-3454).

;;; --- Slot constants ----------------------------------------------------

(define TOOL-BAR-ITEM-KEY         0)
(define TOOL-BAR-ITEM-ENABLED-P   1)
(define TOOL-BAR-ITEM-SELECTED-P  2)
(define TOOL-BAR-ITEM-CAPTION     3)
(define TOOL-BAR-ITEM-IMAGES      4)
(define TOOL-BAR-ITEM-BINDING     5)
(define TOOL-BAR-ITEM-TYPE        6)
(define TOOL-BAR-ITEM-HELP        7)
(define TOOL-BAR-ITEM-RTL-IMAGE   8)
(define TOOL-BAR-ITEM-LABEL       9)
(define TOOL-BAR-ITEM-VERT-ONLY  10)
(define TOOL-BAR-ITEM-WRAP       11)
(define TOOL-BAR-ITEM-NSLOTS     12)

;;; --- imp-3.1 infrastructure DEFUNs ------------------------------------

(defelisp %--tool-bar-items-vector          --tool-bar-items-vector)
(defelisp %--set-tool-bar-items-vector      --set-tool-bar-items-vector)
(defelisp %--tool-bar-item-properties-vector --tool-bar-item-properties-vector)
(defelisp %--tool-bar-items-count           --tool-bar-items-count)
(defelisp %--set-tool-bar-items-count       --set-tool-bar-items-count)
(defelisp %--larger-vector                  --larger-vector)

;;; --- Elisp bridge references (all are DEFUNs or DEFVARs) --------------

(defelisp %aref              aref)
(defelisp %aset              aset)
(defelisp %list              list)
(defelisp %functionp         functionp)
(defelisp %lookup-key        lookup-key)
(defelisp %map-keymap        map-keymap)
(defelisp %keymapp           keymapp)
(defelisp %current-active-maps current-active-maps)
(defelisp %symbol-value      symbol-value)
(defelisp %set               set)
(defelisp %length            length)
(defelisp %vectorp           vectorp)
(defelisp %upcase-initials   upcase-initials)
(defelisp %where-is-internal  where-is-internal)
(defelisp %key-description    key-description)
(defelisp %concat             concat)

;;; --- Reused from (emacs menu-item-parse) ------------------------------
;;; menu-item-eval-property — the safe-eval helper (authoritative in that module).
;;; QCenable, QCvisible, QChelp, QCfilter, QCbutton, QCtoggle, QCradio
;;;   — keyword literals imported from menu-item-parse's #:export set.
;;;
;;; Additional keywords used by tool-bar items:
(define QClabel      #:label)
(define QCimage      #:image)
(define QCrtl        #:rtl)
(define QCvert-only  #:vert-only)
(define QCwrap       #:wrap)

;;; --- Helpers ----------------------------------------------------------

;;; Menu-item eval property — re-export via alias for local clarity.
(define menu-item-eval-property
  (@ (emacs menu-item-parse) menu-item-eval-property))

;;; Read the dynamic variable enable-disabled-menus-and-buttons.
;;; DEFVAR_LISP at keyboard.c:15160.
(define (enable-disabled-menus-and-buttons)
  ((force %symbol-value) 'enable-disabled-menus-and-buttons))

;;; Port of C menu_separator_name_p (keyboard.c:8512-8530).
;;; Returns #t if LABEL is a recognized menu separator name.
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

;;; Tool bar item properties vector accessor.  Returns the shared
;;; tool_bar_item_properties scratch vector (GC-protected by C staticpro).
(define (tool-bar-item-properties)
  ((force %--tool-bar-item-properties-vector)))

;;; Read tool_bar_max_label_size (DEFVAR_INT in keyboard.c).
(define (tool-bar-max-label-size)
  ((force %symbol-value) 'tool-bar-max-label-size))

;;; --- parse-tool-bar-item -----------------------------------------------
;;; Port of C parse_tool_bar_item (keyboard.c:9183-9450, ~268 lines).
;;; Returns 1 (valid item) or 0 (skip item).
;;; Side effect: fills the shared tool_bar_item_properties vector.
;;;
;;; Extended from parse-tab-bar-item with:
;;;   :image, :rtl, :label, :vert-only, :wrap, :type
;;;   Label auto-generation from caption/key
;;;   Help keybinding lookup

(define (parse-tool-bar-item item key)
  (call/cc
   (lambda (return)
     ;; Rule out non-conses.
     (unless (pair? item)
       (return 0))

     (let* ((props (tool-bar-item-properties))
            (filter #nil)
            (caption #nil)
            (have-label #f)
            (is-wrap #f))

       ;; Reset all slots to nil.
       (do ((i 0 (1+ i)))
           ((>= i TOOL-BAR-ITEM-NSLOTS))
         ((force %aset) props i #nil))

       ;; String car → wrap in list.
       (if (string? (car item))
           (set! item ((force %list) (car item)))
           (begin
             (unless (and (eq? (car item) 'menu-item)
                          (pair? (cdr item)))
               (return 0))
             (set! item (cdr item))))

       ;; Set defaults.
       ((force %aset) props TOOL-BAR-ITEM-KEY key)
       ((force %aset) props TOOL-BAR-ITEM-ENABLED-P #t)

       ;; Capture caption.
       (set! caption (car item))
       (if (string? caption)
           ((force %aset) props TOOL-BAR-ITEM-CAPTION caption)
           (begin
             (set! caption (menu-item-eval-property caption))
             (unless (string? caption)
               (return 0))
             ((force %aset) props TOOL-BAR-ITEM-CAPTION caption)))

       ;; Advance past caption.
       (set! item (cdr item))

       ;; If nothing after caption — separator item?
       (unless (pair? item)
         (if (menu-separator-name? caption)
             (begin
               ((force %aset) props TOOL-BAR-ITEM-TYPE #t)
               ((force %aset) props TOOL-BAR-ITEM-ENABLED-P #nil)
               ((force %aset) props TOOL-BAR-ITEM-SELECTED-P #nil)
               ((force %aset) props TOOL-BAR-ITEM-CAPTION #nil)
               ;; imp-3.2: Separator IMAGES slot — C sets
               ;; TOOL_BAR_ITEM_IMAGES from
               ;; menu_item_eval_property(Vtool_bar_separator_image_expression).
               ((force %aset) props TOOL-BAR-ITEM-IMAGES
                (menu-item-eval-property
                 ((force %symbol-value) 'tool-bar-separator-image-expression)))
               (return 1))
             (return 0)))

       ;; Store binding.
       ((force %aset) props TOOL-BAR-ITEM-BINDING (car item))
       (set! item (cdr item))

       ;; Ignore cached key-binding list.
       (when (and (pair? item) (pair? (car item)))
         (set! item (cdr item)))

       ;; Process keyword properties via plist walk.
       (let* ((tortoise item)
              (tick #f))
         (let plist-loop ((lst item))
           (when (and (pair? lst) (pair? (cdr lst)))
             (set! tick (not tick))
             (when tick
               (set! tortoise (cdr tortoise))
               (when (eq? lst tortoise)
                 (return 0)))
             (let ((ikey (car lst))
                   (value (cadr lst))
                   (rest (cdr lst)))
               (cond
                ((eq? ikey QCenable)
                 (if (not (eq? #nil (enable-disabled-menus-and-buttons)))
                     ((force %aset) props TOOL-BAR-ITEM-ENABLED-P #t)
                     ((force %aset) props TOOL-BAR-ITEM-ENABLED-P value)))
                ((eq? ikey QCvisible)
                 (when (eq? #nil (menu-item-eval-property value))
                   (return 0)))
                ((eq? ikey QChelp)
                 ((force %aset) props TOOL-BAR-ITEM-HELP value))
                ((eq? ikey QCfilter)
                 (set! filter value))
                ((eq? ikey QCbutton)
                 (when (pair? value)
                   (let ((type (car value))
                         (selected (cdr value)))
                     (when (or (eq? type QCtoggle) (eq? type QCradio))
                       ((force %aset) props TOOL-BAR-ITEM-SELECTED-P selected)
                       ((force %aset) props TOOL-BAR-ITEM-TYPE type)))))
                ((eq? ikey QCvert-only)
                 ((force %aset) props TOOL-BAR-ITEM-VERT-ONLY value))
                ((eq? ikey QClabel)
                 ((force %aset) props TOOL-BAR-ITEM-LABEL
                  (if (string? value) value "!!?GARBLED ITEM?!!"))
                 (set! have-label #t))
                ((eq? ikey QCimage)
                 (let ((img value))
                   (when (or (pair? img)
                             (and (not (eq? #nil ((force %vectorp) img)))
                                  (= ((force %length) img) 4)))
                     ((force %aset) props TOOL-BAR-ITEM-IMAGES img))))
                ((eq? ikey QCrtl)
                 ((force %aset) props TOOL-BAR-ITEM-RTL-IMAGE value))
                ((eq? ikey QCwrap)
                 ((force %aset) props TOOL-BAR-ITEM-WRAP value)
                 (unless (eq? #nil value)
                   (set! is-wrap #t))))
               (plist-loop (cdr rest))))))

       ;; Label auto-generation (when no :label was specified).
       (unless have-label
         (let* ((tkey  ((force %aref) props TOOL-BAR-ITEM-KEY))
                (tcapt ((force %aref) props TOOL-BAR-ITEM-CAPTION))
                (label-str (if (symbol? tkey) (symbol->string tkey) ""))
                (capt-str  (if (string? tcapt) tcapt ""))
                (max-lbl (tool-bar-max-label-size)))
           (let ((caption-len (string-length capt-str)))
             (if (and (> caption-len 0) (<= caption-len max-lbl))
                 (begin
                   ;; Strip trailing dots from caption.
                   (let loop ((idx (string-length capt-str)))
                     (if (and (> idx 0)
                              (char=? (string-ref capt-str (- idx 1)) #\.))
                         (loop (- idx 1))
                         (set! capt-str (substring capt-str 0 idx))))
                   (set! label-str capt-str))
                 (when (> (string-length label-str) 0)
                   ;; Replace dashes with spaces.
                   (set! label-str
                     (list->string
                      (map (lambda (c) (if (char=? c #\-) #\space c))
                           (string->list label-str)))))))
           (let ((new-lbl ((force %upcase-initials) label-str)))
             (if (<= (string-length new-lbl) max-lbl)
                 ((force %aset) props TOOL-BAR-ITEM-LABEL new-lbl)
                 ((force %aset) props TOOL-BAR-ITEM-LABEL "")))))

       ;; Post-format: apply :filter.
       (unless (eq? filter #nil)
         ((force %aset) props TOOL-BAR-ITEM-BINDING
          (menu-item-eval-property
           ((force %list) filter
            ((force %list) 'quote
             ((force %aref) props TOOL-BAR-ITEM-BINDING))))))

       ;; If binding is a keymap, give up.
       (when (not (eq? #nil
                       ((force %keymapp)
                        ((force %aref) props TOOL-BAR-ITEM-BINDING))))
         (return 0))

       ;; imp-3.2: Help augmentation with keybinding (C order:
       ;; after keymapp check, before enable-eval).  Appends
       ;; "  (KEY-DESC)" to HELP slot so tooltips show the shortcut.
       (let* ((binding ((force %aref) props TOOL-BAR-ITEM-BINDING))
              (keys    ((force %where-is-internal) binding #nil #t #nil #nil)))
         (unless (eq? keys #nil)
           (let* ((orig ((force %aref) props TOOL-BAR-ITEM-HELP))
                  (orig (if (eq? orig #nil)
                            ((force %aref) props TOOL-BAR-ITEM-CAPTION)
                            orig))
                  (desc ((force %key-description) keys #nil)))
             ((force %aset) props TOOL-BAR-ITEM-HELP
              ((force %concat) orig "  (" desc ")")))))

       ;; If wrap item, disable it.
       (when is-wrap
         ((force %aset) props TOOL-BAR-ITEM-ENABLED-P #nil))

       ;; Enable / disable evaluation.
       (let ((en ((force %aref) props TOOL-BAR-ITEM-ENABLED-P)))
         (unless (eq? en #t)
           ((force %aset) props TOOL-BAR-ITEM-ENABLED-P
            (menu-item-eval-property en))))

       ;; Radio / toggle selected state evaluation.
       (let ((sel ((force %aref) props TOOL-BAR-ITEM-SELECTED-P)))
         (unless (eq? sel #nil)
           ((force %aset) props TOOL-BAR-ITEM-SELECTED-P
            (menu-item-eval-property sel))))

       1))))

;;; --- append-tool-bar-item! ---------------------------------------------
;;; Port of C append_tool_bar_item (keyboard.c:9475-9490).
;;; Copies TOOL_BAR_ITEM_NSLOTS slots from tool_bar_item_properties onto
;;; the end of tool_bar_items_vector, growing it if needed.

(define (append-tool-bar-item!)
  (let* ((vec   ((force %--tool-bar-items-vector)))
         (cnt   ((force %--tool-bar-items-count)))
         (props (tool-bar-item-properties))
         (incr  (- cnt (- ((force %length) vec) TOOL-BAR-ITEM-NSLOTS))))

    ;; Enlarge vector if necessary.
    (when (> incr 0)
      (set! vec ((force %--larger-vector) vec incr -1))
      ((force %--set-tool-bar-items-vector) vec))

    ;; Copy NSLOTS slots from props into vec[cnt..cnt+NSLOTS-1].
    (do ((j 0 (1+ j)))
        ((>= j TOOL-BAR-ITEM-NSLOTS))
      ((force %aset) vec (+ cnt j) ((force %aref) props j)))

    ((force %--set-tool-bar-items-count) (+ cnt TOOL-BAR-ITEM-NSLOTS))))

;;; --- process-tool-bar-item ---------------------------------------------
;;; Port of C process_tool_bar_item (keyboard.c:9092-9118).
;;; Callback for map-keymap.  KEY is the event, DEF is the binding.
;;;
;;; If DEF == 'undefined: splice out the prior item with matching KEY
;;;   from tool_bar_items_vector.
;;; Else: parse the item; if valid, append it.

(define (process-tool-bar-item key def)
  (if (eq? def 'undefined)
      ;; Remove the matching prior item.
      (let* ((vec ((force %--tool-bar-items-vector)))
             (cnt ((force %--tool-bar-items-count)))
             (nslots TOOL-BAR-ITEM-NSLOTS))
        ;; Linear scan by NSLOTS strides.
        (let loop ((i 0))
          (when (< i cnt)
            (if (eq? key ((force %aref) vec (+ i TOOL-BAR-ITEM-KEY)))
                (begin
                  ;; Shift tail down by NSLOTS (memmove equivalent).
                  (when (> cnt (+ i nslots))
                    (do ((j (+ i nslots) (1+ j)))
                        ((>= j cnt))
                      ((force %aset) vec (- j nslots) ((force %aref) vec j))))
                  ((force %--set-tool-bar-items-count) (- cnt nslots)))
                (loop (+ i nslots))))))
      ;; Normal item: parse then append.
      (when (= 1 (parse-tool-bar-item def key))
        (append-tool-bar-item!))))

;;; --- tool-bar-items ----------------------------------------------------
;;; Port of C tool_bar_items (keyboard.c:9004-9083, ~81 lines).
;;; Returns (cons vector nitems).
;;;
;;; REUSE — an existing vector to reuse (or nil for fresh allocation).

(define (tool-bar-items reuse)
  ;; 1. Initialize the items vector (mirror init_tool_bar_items).
  ;;    The getter lazy-inits to 64 slots on first call.
  ((force %--tool-bar-items-vector))              ; ensure lazy-init
  (if (not (eq? #nil ((force %vectorp) reuse)))
      ((force %--set-tool-bar-items-vector) reuse))
  ((force %--set-tool-bar-items-count) 0)

  ;; 2. Inhibit quit around the map-keymap walk.  C uses plain
  ;;    save/restore (redisplay treats quit as fatal, so bypass on
  ;;    error is acceptable there).  Scheme wraps in dynamic-wind so
  ;;    an error or non-local exit during the walk still restores
  ;;    inhibit-quit to its prior value.
  (let ((oquit ((force %symbol-value) 'inhibit-quit)))
    (dynamic-wind
      (lambda ()
        ((force %set) 'inhibit-quit #t))
      (lambda ()
        ;; 3. Build list of keymaps via current-active-maps (olp=t mirrors
        ;;    the C logic of respecting overriding-local-map and
        ;;    overriding-terminal-local-map).
        (let ((maps ((force %current-active-maps) #t #nil)))
          ;; 4. Process maps in REVERSE order (global first, local last).
          ;;    For each map, look up the [tool-bar] prefix; if it's a keymap,
          ;;    iterate its bindings with process-tool-bar-item.
          (do ((lst (reverse maps) (cdr lst)))
              ((null? lst))
            (let ((keymap (car lst)))
              (unless (eq? keymap #nil)
                (let ((binding ((force %lookup-key) keymap #(tool-bar))))
                  (when (not (eq? #nil ((force %keymapp) binding)))
                    ((force %map-keymap) process-tool-bar-item binding))))))))
      ;; 5. Restore inhibit-quit.
      (lambda ()
        ((force %set) 'inhibit-quit oquit))))

  ;; 6. Compute nitems and return.
  (let* ((cnt ((force %--tool-bar-items-count)))
         (nitems (/ cnt TOOL-BAR-ITEM-NSLOTS))
         (vec ((force %--tool-bar-items-vector))))
    (cons vec nitems)))
