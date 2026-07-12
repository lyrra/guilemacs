(define-module (emacs tab-bar-items)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs menu-item-parse)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (tab-bar-items
            parse-tab-bar-item
            process-tab-bar-item
            TAB-BAR-ITEM-KEY
            TAB-BAR-ITEM-ENABLED-P
            TAB-BAR-ITEM-SELECTED-P
            TAB-BAR-ITEM-CAPTION
            TAB-BAR-ITEM-BINDING
            TAB-BAR-ITEM-HELP
            TAB-BAR-ITEM-NSLOTS))

;;; M10 imp-2.2/2.3 — Scheme port of tab_bar_items.
;;; C tab_bar_items in keyboard.c is now a SCM_CALL_1 shim into this
;;; module (see imp-2.3).  Static vectors (tab_bar_items_vector,
;;; tab_bar_item_properties, ntab_bar_items) still live in C and are
;;; mutated via the imp-2.1 DEFUNs; staticpro keeps them GC-safe.
;;;
;;; Decomposition mirrors the three C functions:
;;;   parse-tab-bar-item   — fill tab_bar_item_properties vector (→ 0/1)
;;;   process-tab-bar-item — callback for map-keymap (side-effecting)
;;;   tab-bar-items        — main entry (→ (cons vector nitems))
;;;
;;; Slot constants match enum tab_bar_item_idx (dispextern.h:3366-3387).

;;; --- Slot constants ----------------------------------------------------

(define TAB-BAR-ITEM-KEY         0)
(define TAB-BAR-ITEM-ENABLED-P   1)
(define TAB-BAR-ITEM-SELECTED-P  2)
(define TAB-BAR-ITEM-CAPTION     3)
(define TAB-BAR-ITEM-BINDING     4)
(define TAB-BAR-ITEM-HELP        5)
(define TAB-BAR-ITEM-NSLOTS      6)

;;; --- imp-2.1 infrastructure DEFUNs ------------------------------------

(defelisp %--tab-bar-items-vector        --tab-bar-items-vector)
(defelisp %--set-tab-bar-items-vector    --set-tab-bar-items-vector)
(defelisp %--tab-bar-item-properties-vector --tab-bar-item-properties-vector)
(defelisp %--tab-bar-items-count         --tab-bar-items-count)
(defelisp %--set-tab-bar-items-count     --set-tab-bar-items-count)
(defelisp %--larger-vector               --larger-vector)

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
(defelisp %length           length)
(defelisp %vectorp          vectorp)

;;; --- Reused from (emacs menu-item-parse) ------------------------------
;;; menu-item-eval-property — the safe-eval helper (authoritative in that module).
;;; QCenable, QCvisible, QChelp, QCfilter, QCbutton, QCtoggle, QCradio
;;;   — keyword literals imported from menu-item-parse's #:export set.
;;;
;;; Additional keywords used by tab-bar items:
(define QClabel  #:label)
(define QCimage  #:image)

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
;;; Matches:
;;;   1. Exactly 4 chars: "--" followed by a separator-name suffix
;;;      (space, no-line, single-line, double-line, single-dashed-line,
;;;       double-dashed-line, shadow-etched-in, shadow-etched-out,
;;;       shadow-etched-in-dash, shadow-etched-out-dash)
;;;   2. Any string consisting solely of dashes ("--", "---", etc.)
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

;;; Tab bar item properties vector accessor.  Returns the shared
;;; tab_bar_item_properties scratch vector (GC-protected by C staticpro).
(define (tab-bar-item-properties)
  ((force %--tab-bar-item-properties-vector)))

;;; --- parse-tab-bar-item ------------------------------------------------
;;; Port of C parse_tab_bar_item (keyboard.c:9139–9277, ~139 lines).
;;; Returns 1 (valid item) or 0 (skip item).
;;; Side effect: fills the shared tab_bar_item_properties vector.
;;;
;;; Simpler than parse_menu_item: no old-format branch, no keyeq
;;; resolution, no keymap-as-def path (keymap binding → return 0).

(define (parse-tab-bar-item item key)
  (call/cc
   (lambda (return)
     ;; Rule out non-conses.
     (unless (pair? item)
       (return 0))

     (let* ((props (tab-bar-item-properties))
            (filter #nil)
            (caption #nil))

       ;; Reset all slots to nil.
       (do ((i 0 (1+ i)))
           ((>= i TAB-BAR-ITEM-NSLOTS))
         ((force %aset) props i #nil))

       ;; String car → wrap in list (matches C: if STRINGP head, item=list1(car)).
       ;; Handles old-style separators like ("--"), ("--space"), etc.
       (if (string? (car item))
           (set! item ((force %list) (car item)))
           (begin
             ;; New-format: (menu-item CAPTION BINDING PROPS...)
             (unless (and (eq? (car item) 'menu-item)
                          (pair? (cdr item)))
               (return 0))
             (set! item (cdr item))))

       ;; Set defaults.
       ((force %aset) props TAB-BAR-ITEM-KEY key)
       ((force %aset) props TAB-BAR-ITEM-ENABLED-P #t)

       ;; Capture caption.
       (set! caption (car item))
       (if (string? caption)
           ((force %aset) props TAB-BAR-ITEM-CAPTION caption)
           (begin
             (set! caption (menu-item-eval-property caption))
             (unless (string? caption)
               (return 0))
             ((force %aset) props TAB-BAR-ITEM-CAPTION caption)))

       ;; Advance past caption.
       (set! item (cdr item))

       ;; If nothing after caption — separator item?
       (unless (pair? item)
         (if (menu-separator-name? caption)
             (begin
               ((force %aset) props TAB-BAR-ITEM-ENABLED-P #nil)
               ((force %aset) props TAB-BAR-ITEM-SELECTED-P #nil)
               ((force %aset) props TAB-BAR-ITEM-CAPTION #nil)
               (return 1))
             (return 0)))

       ;; Store binding.
       ((force %aset) props TAB-BAR-ITEM-BINDING (car item))
       (set! item (cdr item))

       ;; Ignore cached key-binding list, if any:
       ;; (CACHED-BINDING . rest) where CACHED-BINDING is a cons.
       (when (and (pair? item) (pair? (car item)))
         (set! item (cdr item)))

       ;; Process keyword properties via plist walk with cycle detection
       ;; (mirrors C's FOR_EACH_TAIL tortoise/hare guard).
       (let* ((tortoise item)
              (tick #f))
         (let plist-loop ((lst item))
           (when (and (pair? lst) (pair? (cdr lst)))
             ;; Cycle check: advance tortoise every other step.
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
                 ;; :enable FORM
                 (if (not (eq? #nil (enable-disabled-menus-and-buttons)))
                     ((force %aset) props TAB-BAR-ITEM-ENABLED-P #t)
                     ((force %aset) props TAB-BAR-ITEM-ENABLED-P value)))
                ((eq? ikey QCvisible)
                 ;; :visible FORM — eval to nil → skip item
                 (when (eq? #nil (menu-item-eval-property value))
                   (return 0)))
                ((eq? ikey QChelp)
                 ;; :help HELP-STRING
                 ((force %aset) props TAB-BAR-ITEM-HELP value))
                ((eq? ikey QCfilter)
                 ;; :filter FUNCTION
                 (set! filter value))
                ((eq? ikey QCbutton)
                 ;; :button (TYPE . SELECTED)
                 (when (pair? value)
                   (let ((type (car value))
                         (selected (cdr value)))
                     (when (or (eq? type QCtoggle) (eq? type QCradio))
                       ((force %aset) props TAB-BAR-ITEM-SELECTED-P selected)))))
                ;; :image and :label pass through silently (consumed during
                ;; display, not during parsing).
                )
               (plist-loop (cdr rest))))))

       ;; Post-format: apply :filter.
       (unless (eq? filter #nil)
         ((force %aset) props TAB-BAR-ITEM-BINDING
          (menu-item-eval-property
           ((force %list) filter
            ((force %list) 'quote
             ((force %aref) props TAB-BAR-ITEM-BINDING))))))

       ;; If binding is a keymap, give up.
       (when (not (eq? #nil
                       ((force %keymapp)
                        ((force %aref) props TAB-BAR-ITEM-BINDING))))
         (return 0))

       ;; Enable / disable evaluation.
       (let ((en ((force %aref) props TAB-BAR-ITEM-ENABLED-P)))
         (unless (eq? en #t)
           ((force %aset) props TAB-BAR-ITEM-ENABLED-P
            (menu-item-eval-property en))))

       ;; Radio / toggle selected state evaluation.
       (let ((sel ((force %aref) props TAB-BAR-ITEM-SELECTED-P)))
         (unless (eq? sel #nil)
           ((force %aset) props TAB-BAR-ITEM-SELECTED-P
            (menu-item-eval-property sel))))

       1))))

;;; --- append-tab-bar-item! ----------------------------------------------
;;; Port of C append_tab_bar_item (keyboard.c:9301-9318).
;;; Copies TAB_BAR_ITEM_NSLOTS slots from tab_bar_item_properties onto
;;; the end of tab_bar_items_vector, growing it if needed.

(define (append-tab-bar-item!)
  (let* ((vec   ((force %--tab-bar-items-vector)))
         (cnt   ((force %--tab-bar-items-count)))
         (props (tab-bar-item-properties))
         (incr  (- cnt (- ((force %length) vec) TAB-BAR-ITEM-NSLOTS))))

    ;; Enlarge vector if necessary.
    (when (> incr 0)
      (set! vec ((force %--larger-vector) vec incr -1))
      ((force %--set-tab-bar-items-vector) vec))

    ;; Copy NSLOTS slots from props into vec[cnt..cnt+NSLOTS-1].
    (do ((j 0 (1+ j)))
        ((>= j TAB-BAR-ITEM-NSLOTS))
      ((force %aset) vec (+ cnt j) ((force %aref) props j)))

    ((force %--set-tab-bar-items-count) (+ cnt TAB-BAR-ITEM-NSLOTS))))

;;; --- process-tab-bar-item ----------------------------------------------
;;; Port of C process_tab_bar_item (keyboard.c:9052-9083).
;;; Callback for map-keymap.  KEY is the event, DEF is the binding.
;;;
;;; If DEF == 'undefined: splice out the prior item with matching KEY
;;;   from tab_bar_items_vector.
;;; Else: parse the item; if valid, append it.

(define (process-tab-bar-item key def)
  (if (eq? def 'undefined)
      ;; Remove the matching prior item.
      (let* ((vec ((force %--tab-bar-items-vector)))
             (cnt ((force %--tab-bar-items-count)))
             (nslots TAB-BAR-ITEM-NSLOTS))
        ;; Linear scan by NSLOTS strides.
        (let loop ((i 0))
          (when (< i cnt)
            (if (eq? key ((force %aref) vec (+ i TAB-BAR-ITEM-KEY)))
                (begin
                  ;; Shift tail down by NSLOTS (memmove equivalent).
                  (when (> cnt (+ i nslots))
                    (do ((j (+ i nslots) (1+ j)))
                        ((>= j cnt))
                      ((force %aset) vec (- j nslots) ((force %aref) vec j))))
                  ((force %--set-tab-bar-items-count) (- cnt nslots)))
                (loop (+ i nslots))))))
      ;; Normal item: parse then append.
      (when (= 1 (parse-tab-bar-item def key))
        (append-tab-bar-item!))))

;;; --- tab-bar-items -----------------------------------------------------
;;; Port of C tab_bar_items (keyboard.c:8966-9045, ~81 lines).
;;; Returns (cons vector nitems).
;;;
;;; REUSE — an existing vector to reuse (or nil for fresh allocation).

(define (tab-bar-items reuse)
  ;; 1. Initialize the items vector (mirror init_tab_bar_items).
  ;;    The getter lazy-inits to 64 slots on first call.
  ((force %--tab-bar-items-vector))              ; ensure lazy-init
  (if (not (eq? #nil ((force %vectorp) reuse)))
      ((force %--set-tab-bar-items-vector) reuse))
  ((force %--set-tab-bar-items-count) 0)

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
          ;;    For each map, look up the [tab-bar] prefix; if it's a keymap,
          ;;    iterate its bindings with process-tab-bar-item.
          (do ((lst (reverse maps) (cdr lst)))
              ((null? lst))
            (let ((keymap (car lst)))
              (unless (eq? keymap #nil)
                (let ((binding ((force %lookup-key) keymap #(tab-bar))))
                  (when (not (eq? #nil ((force %keymapp) binding)))
                    ((force %map-keymap) process-tab-bar-item binding))))))))
      ;; 5. Restore inhibit-quit.
      (lambda ()
        ((force %set) 'inhibit-quit oquit))))

  ;; 6. Compute nitems and return.
  (let* ((cnt ((force %--tab-bar-items-count)))
         (nitems (/ cnt TAB-BAR-ITEM-NSLOTS))
         (vec ((force %--tab-bar-items-vector))))
    (cons vec nitems)))
