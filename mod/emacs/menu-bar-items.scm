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

;;; M10 imp-4.1 — Scheme port of the outer menu_bar_items driver.
;;; C menu_bar_items at keyboard.c:8594 still runs; this module coexists
;;; alongside it.  The inner callback (menu_bar_item / process-menu-bar-item)
;;; is a stub for now — imp-4.3 fills it in.
;;;
;;; Decomposition:
;;;   process-menu-bar-item — stub for now (throws unimplemented)
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
(defelisp %--map-keymap-canonical --map-keymap-canonical)

;;; --- Reused from (emacs menu-item-parse) ------------------------------
;;; menu-item-eval-property — the safe-eval helper (authoritative in that module).
;;; Imported now so the FFI trap is caught by the build, not at runtime.

(define menu-item-eval-property
  (@ (emacs menu-item-parse) menu-item-eval-property))

;;; --- process-menu-bar-item (stub — imp-4.3 fills this in) --------------
;;; Port of C menu_bar_item (keyboard.c:8741+).
;;; Callback for --map-keymap-canonical.  KEY is the event, DEF is the binding.
;;;
;;; The real implementation will:
;;;   1. Parse the item via parse-menu-item.
;;;   2. Compute HPOS (the horizontal display position).
;;;   3. Append to menu_bar_items_vector (or merge with existing item).
;;; For now, this stub throws — the C menu_bar_item callback still runs
;;; via the C menu_bar_items path.

(define (process-menu-bar-item key def)
  ;; imp-4.1 stub — real implementation lands in imp-4.3.  Must be a
  ;; no-op (not an error): menu-bar-items is called end-to-end by the
  ;; test suite, and any real [menu-bar] keymap in current-active-maps
  ;; (global-map has one after loadup) drives this callback via
  ;; --map-keymap-canonical.  A throw would abort startup.
  #nil)

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
