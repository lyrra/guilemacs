(define-module (emacs menu-bar-items)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs menu-item-parse)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (menu-bar-items
            process-menu-bar-item
            final-items-rotate!
            MENU-BAR-ITEM-KEY
            MENU-BAR-ITEM-STRING
            MENU-BAR-ITEM-DEF
            MENU-BAR-ITEM-HPOS
            MENU-BAR-ITEM-NSLOTS))

;;; M10 imp-4.3 — Scheme port of menu_bar_items driver + callback.
;;; C menu_bar_items at keyboard.c:8594 still runs; this module coexists
;;; alongside it.  The inner callback (menu_bar_item / process-menu-bar-item)
;;; is now a full port of C menu_bar_item (keyboard.c:8744-8816).
;;;
;;; Decomposition:
;;;   process-menu-bar-item — full port (undefined splice, dedup, parse, append)
;;;   menu-bar-items         — main entry (→ vector)
;;;
;;; Slot constants match the C menu_bar_items layout:
;;;   index 0 = KEY     (the event symbol)
;;;   index 1 = STRING  (the menu item name)
;;;   index 2 = DEF     (the binding)
;;;   index 3 = HPOS    (horizontal position hint)

;;; --- Slot constants ----------------------------------------------------

(define MENU-BAR-ITEM-KEY     0)
(define MENU-BAR-ITEM-STRING  1)
(define MENU-BAR-ITEM-DEF     2)
(define MENU-BAR-ITEM-HPOS    3)
(define MENU-BAR-ITEM-NSLOTS  4)

;;; --- imp-4.1 infrastructure DEFUNs ------------------------------------

(defelisp %--menu-bar-items-vector      --menu-bar-items-vector)
(defelisp %--set-menu-bar-items-vector  --set-menu-bar-items-vector)
(defelisp %--menu-bar-items-index       --menu-bar-items-index)
(defelisp %--set-menu-bar-items-index   --set-menu-bar-items-index)
(defelisp %--menu-bar-one-keymap-changed-items
          --menu-bar-one-keymap-changed-items)
(defelisp %--set-menu-bar-one-keymap-changed-items
          --set-menu-bar-one-keymap-changed-items)
(defelisp %--larger-vector              --larger-vector)

;;; --- Elisp bridge references (all are DEFUNs or DEFVARs) --------------

(defelisp %aref              aref)
(defelisp %aset              aset)
(defelisp %list              list)
(defelisp %lookup-key        lookup-key)
(defelisp %keymapp           keymapp)
(defelisp %current-active-maps current-active-maps)
(defelisp %symbol-value      symbol-value)
(defelisp %set               set)
(defelisp %length            length)
(defelisp %vectorp           vectorp)
(defelisp %memq              memq)
(defelisp %car               car)
(defelisp %cons              cons)
(defelisp %--map-keymap-canonical --map-keymap-canonical)

;;; --- Reused from (emacs menu-item-parse) ------------------------------
;;; menu-item-eval-property — the safe-eval helper (authoritative in that module).
;;; parse-menu-item — the shared parser (imp-1.3).
;;; item-properties — the shared 9-slot vector parse-menu-item writes into.
;;; ITEM-PROPERTY-DEF, ITEM-PROPERTY-NAME — slot indices (2 and 1).
;;; Imported via @ so the FFI trap is caught by the build, not at runtime.

(define menu-item-eval-property
  (@ (emacs menu-item-parse) menu-item-eval-property))

(define parse-menu-item
  (@ (emacs menu-item-parse) parse-menu-item))

(define item-properties
  (@ (emacs menu-item-parse) item-properties))

(define ITEM-PROPERTY-DEF
  (@ (emacs menu-item-parse) ITEM-PROPERTY-DEF))

(define ITEM-PROPERTY-NAME
  (@ (emacs menu-item-parse) ITEM-PROPERTY-NAME))

;;; --- process-menu-bar-item ---------------------------------------------
;;; Port of C menu_bar_item (keyboard.c:8744-8816).
;;; Callback for --map-keymap-canonical.  KEY is the event, DEF is the binding.
;;;
;;; Steps:
;;;   1. If DEF == 'undefined: splice out the prior item with matching KEY.
;;;   2. Dedup: skip if KEY already processed for this keymap (memq).
;;;   3. Cons KEY onto dedup list BEFORE parsing (so a non-menu-item still hides).
;;;   4. Parse via parse-menu-item(def, 1); return if not a menu item.
;;;   5. Read parsed DEF back from item-properties[ITEM-PROPERTY-DEF].
;;;   6. Scan for existing item with this KEY — if found, merge map list;
;;;      otherwise append new 4-tuple (KEY, NAME, (list DEF), HPOS=0).

(define (process-menu-bar-item key def)
  (let* ((vec     ((force %--menu-bar-items-vector)))
         (idx-g   (force %--menu-bar-items-index))
         (idx     (idx-g))
         (changed ((force %--menu-bar-one-keymap-changed-items))))

    ;; 1. Handle undefined: if DEF is 'undefined, splice out any prior
    ;;    item with matching KEY.  NB: does NOT return — falls through
    ;;    to the dedup check below (matches C menu_bar_item).
    (when (eq? def 'undefined)
      (let loop ((i 0))
        (when (< i idx)
          (if (eq? key ((force %aref) vec (+ i MENU-BAR-ITEM-KEY)))
              (begin
                ;; Shift tail down by 4 slots (forward copy is safe
                ;; since dest i < source i+4).
                (when (> idx (+ i 4))
                  (do ((j i (1+ j)))
                      ((>= j (- idx 4)))
                    ((force %aset) vec j
                     ((force %aref) vec (+ j 4)))))
                ((force %--set-menu-bar-items-index) (- idx 4)))
              (loop (+ i 4))))))

    ;; 2. Dedup / nil guard: if KEY has already contributed from this
    ;;    keymap, or DEF is nil, return immediately (C returns here).
    ;;    Re-read idx+vec in case the undefined splice mutated them.
    (set! idx ((force %--menu-bar-items-index)))
    (set! vec ((force %--menu-bar-items-vector)))
    (unless (or (not (eq? #nil ((force %memq) key changed)))
                (eq? #nil def))

      ;; 3. Cons KEY onto the dedup list BEFORE parsing.  This ensures
      ;;    that even a non-menu-item hides subsequent duplicates.
      ((force %--set-menu-bar-one-keymap-changed-items)
       ((force %cons) key changed))

      ;; 4. Parse the item.  inmenubar=1 for menu-bar context (enables
      ;;    keyeq resolution).  Returns 0 (not a menu item) or 1 (ok).
      (when (= 1 (parse-menu-item def 1))

        ;; 5. Read parsed values from the shared item_properties vector.
        (let* ((props      (item-properties))
               (parsed-def ((force %aref) props ITEM-PROPERTY-DEF))
               (parsed-name ((force %aref) props ITEM-PROPERTY-NAME)))

          ;; Re-read state (may have been resized by earlier items).
          (set! vec ((force %--menu-bar-items-vector)))
          (set! idx ((force %--menu-bar-items-index)))

          ;; 6. Scan for existing item with this KEY (stride-4).
          (let loop ((i 0))
            (cond
             ((>= i idx)
              ;; Not found — append new 4-tuple at end.
              (when (> (+ i 4) ((force %length) vec))
                (set! vec ((force %--larger-vector) vec 4 -1))
                ((force %--set-menu-bar-items-vector) vec))
              ((force %aset) vec (+ i MENU-BAR-ITEM-KEY)    key)
              ((force %aset) vec (+ i MENU-BAR-ITEM-STRING) parsed-name)
              ;; list1(parsed-def) — the map list starts with one element.
              ((force %aset) vec (+ i MENU-BAR-ITEM-DEF)
               ((force %list) parsed-def))
              ((force %aset) vec (+ i MENU-BAR-ITEM-HPOS)   0)
              ((force %--set-menu-bar-items-index) (+ i 4)))
             ((eq? key ((force %aref) vec (+ i MENU-BAR-ITEM-KEY)))
              ;; Found — merge parsed-def into the map list at slot i+2.
              ;; If both existing car and parsed-def are keymaps, keep
              ;; the old list; otherwise start fresh with just parsed-def.
              (let* ((old    ((force %aref) vec (+ i MENU-BAR-ITEM-DEF)))
                     (both-keymaps?
                      (and (not (eq? #nil ((force %keymapp) parsed-def)))
                           (not (eq? #nil ((force %keymapp)
                                           ((force %car) old))))))
                     (merged ((force %cons) parsed-def
                              (if both-keymaps? old #nil))))
                ((force %aset) vec (+ i MENU-BAR-ITEM-DEF) merged)))
             (else
              (loop (+ i 4))))))))))

;;; --- final-items-rotate! -----------------------------------------------
;;; Port of C final-items pass (keyboard.c:8639-8667).
;;; For each symbol in Vmenu_bar_final_items, scan the items vector for
;;; a matching KEY slot and rotate that 4-tuple to the end.

(define (final-items-rotate! vec idx)
  (for-each
   (lambda (sym)
     (let loop ((i 0))
       (when (< i idx)
         (if (eq? sym ((force %aref) vec (+ i MENU-BAR-ITEM-KEY)))
             (begin
               ;; Save the 4 slots at position i.
               (let ((t0 ((force %aref) vec (+ i 0)))
                     (t1 ((force %aref) vec (+ i 1)))
                     (t2 ((force %aref) vec (+ i 2)))
                     (t3 ((force %aref) vec (+ i 3))))
                 ;; Forward copy: shift [i+4 .. idx-1] down by 4.
                 (when (> idx (+ i 4))
                   (do ((j i (1+ j)))
                       ((>= j (- idx 4)))
                     ((force %aset) vec j
                      ((force %aref) vec (+ j 4)))))
                 ;; Place saved tuple at the end.
                 ((force %aset) vec (- idx 4) t0)
                 ((force %aset) vec (- idx 3) t1)
                 ((force %aset) vec (- idx 2) t2)
                 ((force %aset) vec (- idx 1) t3)))
             (loop (+ i 4))))))
   ((force %symbol-value) 'menu-bar-final-items)))

;;; --- menu-bar-items ----------------------------------------------------
;;; Port of C menu_bar_items (keyboard.c:8594-8686, ~93 lines).
;;; Returns the items vector (no nitems — downstream counts by scanning
;;; for the sentinel nil-tuple).
;;;
;;; OLD — an existing vector to reuse (or nil for fresh allocation).

(define (menu-bar-items old)
  ;; 1. Initialize the items vector (mirror C lines 8617-8625).
  ;;    The getter lazy-inits to 24 slots on first call.
  ((force %--menu-bar-items-vector))             ; ensure lazy-init
  (if (not (eq? #nil ((force %vectorp) old)))
      ((force %--set-menu-bar-items-vector) old))
  ((force %--set-menu-bar-items-index) 0)

  ;; 2. Inhibit quit around the keymap walk.  C uses plain save/restore
  ;;    (redisplay treats quit as fatal, so bypass on error is acceptable).
  ;;    Scheme wraps in dynamic-wind so non-local exits still restore.
  (let ((oquit ((force %symbol-value) 'inhibit-quit)))
    (dynamic-wind
      (lambda ()
        ((force %set) 'inhibit-quit #t))
      (lambda ()
        ;; 3. Build list of keymaps via current-active-maps (olp=t mirrors
        ;;    the C logic of respecting overriding-local-map and
        ;;    overriding-terminal-local-map).  Same shortcut as tab/tool-bar.
        (let ((maps ((force %current-active-maps) #t #nil)))
          ;; 4. Process maps in REVERSE order (global first, local last).
          ;;    For each map, look up the [menu-bar] prefix; if it's a keymap,
          ;;    iterate its bindings with map-keymap-canonical.
          (do ((lst (reverse maps) (cdr lst)))
              ((null? lst))
            (let ((keymap (car lst)))
              (unless (eq? keymap #nil)
                (let ((binding ((force %lookup-key) keymap #(menu-bar))))
                  (when (not (eq? #nil ((force %keymapp) binding)))
                    ;; Reset dedup list before each per-map walk
                    ;; (mirrors C:8677).
                    ((force %--set-menu-bar-one-keymap-changed-items) #nil)
                    ((force %--map-keymap-canonical)
                     process-menu-bar-item
                     binding))))))))
      ;; 5. Restore inhibit-quit.
      (lambda ()
        ((force %set) 'inhibit-quit oquit))))

  ;; 6. Final-items pass: rotate specified items to the end.
  (let* ((idx ((force %--menu-bar-items-index)))
         (vec ((force %--menu-bar-items-vector))))
    (final-items-rotate! vec idx)

    ;; 7. Sentinel append: store (#nil #nil #nil #nil) at the tail.
    ;;    Grow vector if needed.
    (when (> (+ idx 4) ((force %length) vec))
      (set! vec ((force %--larger-vector) vec 4 -1))
      ((force %--set-menu-bar-items-vector) vec))
    ((force %aset) vec (+ idx 0) #nil)
    ((force %aset) vec (+ idx 1) #nil)
    ((force %aset) vec (+ idx 2) #nil)
    ((force %aset) vec (+ idx 3) #nil)
    ((force %--set-menu-bar-items-index) (+ idx 4))

    ;; 8. Return the vector (no nitems — unlike tab/tool-bar).
    vec))
