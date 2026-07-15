;;; test-tool-bar-items.scm --- M10 imp-3 test corpus for tool-bar-items
;;;
;;; Sourced by test/keyboard/test-tool-bar-items.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch stdout.

(use-modules (emacs tool-bar-items))

;;; Access tool_bar_item_properties slot N via infrastructure DEFUNs.
(define (prop-slot n)
  ((symbol-function 'aref)
   ((symbol-function '--tool-bar-item-properties-vector))
   n))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

;;; --- Slot constants ----------------------------------------------------

(check "slot-key"         0 TOOL-BAR-ITEM-KEY)
(check "slot-enabled-p"   1 TOOL-BAR-ITEM-ENABLED-P)
(check "slot-selected-p"  2 TOOL-BAR-ITEM-SELECTED-P)
(check "slot-caption"     3 TOOL-BAR-ITEM-CAPTION)
(check "slot-images"      4 TOOL-BAR-ITEM-IMAGES)
(check "slot-binding"     5 TOOL-BAR-ITEM-BINDING)
(check "slot-type"        6 TOOL-BAR-ITEM-TYPE)
(check "slot-help"        7 TOOL-BAR-ITEM-HELP)
(check "slot-rtl-image"   8 TOOL-BAR-ITEM-RTL-IMAGE)
(check "slot-label"       9 TOOL-BAR-ITEM-LABEL)
(check "slot-vert-only"  10 TOOL-BAR-ITEM-VERT-ONLY)
(check "slot-wrap"       11 TOOL-BAR-ITEM-WRAP)
(check "slot-nslots"     12 TOOL-BAR-ITEM-NSLOTS)

;;; --- parse-tool-bar-item -----------------------------------------------

;; Test 1: Non-cons → 0
(let ((result (parse-tool-bar-item 'not-a-list 'key-x)))
  (check "non-cons-returns-0" 0 result))

;; Test 2: Old-style separator: ("--dashes") → valid separator
(let ((result (parse-tool-bar-item (list "--") 'sep-key)))
  (check "separator-dashes-returns-1" 1 result))

;; Test 3: Old-style named separator: ("--space") → valid
(let ((result (parse-tool-bar-item (list "--space") 'sep-key)))
  (check "separator-named-returns-1" 1 result)
  (check "separator-caption-nil" #nil (prop-slot TOOL-BAR-ITEM-CAPTION))
  (check "separator-enabled-nil" #nil (prop-slot TOOL-BAR-ITEM-ENABLED-P))
  (check "separator-type-t" #t (prop-slot TOOL-BAR-ITEM-TYPE)))

;; Test 4: String caption without rest, non-separator → 0
(let ((result (parse-tool-bar-item (list (symbol-name 'Foo)) 'key-foo)))
  (check "string-only-non-sep-returns-0" 0 result))

;; Test 5: New format with :visible nil → skip
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'MyItem)
                    'my-cmd #:visible #nil) 'key-vis)))
  (check "visible-nil-skips" 0 result))

;; Test 6: New format, basic valid item
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'MyItem)
                    'my-cmd) 'key-basic)))
  (check "basic-item-returns-1" 1 result)
  (check "basic-caption-set" (symbol-name 'MyItem)
         (prop-slot TOOL-BAR-ITEM-CAPTION))
  (check "basic-binding-set" 'my-cmd
         (prop-slot TOOL-BAR-ITEM-BINDING))
  (check "basic-enabled-default-t" #t
         (prop-slot TOOL-BAR-ITEM-ENABLED-P)))

;; Test 7: New format with :enable nil
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'Disabled)
                    'some-cmd #:enable #nil) 'key-dis)))
  (check "enable-nil-stored" 1 result))

;; Test 8: New format with :help string
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'HelpItem)
                    'help-cmd #:help (symbol-name 'Help-text)) 'key-help)))
  (check "help-string-stored" 1 result)
  (check "help-value" (symbol-name 'Help-text)
         (prop-slot TOOL-BAR-ITEM-HELP)))

;; Test 9: New format with :button toggle — selected state
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'ToggleItem)
                    'toggle-cmd #:button (cons #:toggle #t)) 'key-tog)))
  (check "toggle-selected" 1 result)
  (check "toggle-selected-t" #t (prop-slot TOOL-BAR-ITEM-SELECTED-P))
  (check "toggle-type-toggle" #:toggle (prop-slot TOOL-BAR-ITEM-TYPE)))

;; Test 10: :label property
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'LblItem)
                    'lbl-cmd #:label (symbol-name 'MyLabel)) 'key-lbl)))
  (check "label-stored" 1 result)
  (check "label-value" (symbol-name 'MyLabel)
         (prop-slot TOOL-BAR-ITEM-LABEL)))

;; Test 11: :vert-only property
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'VertItem)
                    'vert-cmd #:vert-only #t) 'key-vert)))
  (check "vert-only-stored" 1 result)
  (check "vert-only-value" #t (prop-slot TOOL-BAR-ITEM-VERT-ONLY)))

;; Test 12: :image property (single image spec list)
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'ImgItem)
                    'img-cmd #:image (list 'image)) 'key-img)))
  (check "image-stored" 1 result)
  (check "image-value" (list 'image) (prop-slot TOOL-BAR-ITEM-IMAGES)))

;; Test 13: :rtl property
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'RtlItem)
                    'rtl-cmd #:rtl (symbol-name 'rtl-icon.png)) 'key-rtl)))
  (check "rtl-stored" 1 result)
  (check "rtl-value" (symbol-name 'rtl-icon.png)
         (prop-slot TOOL-BAR-ITEM-RTL-IMAGE)))

;; Test 14: :wrap property
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'WrapItem)
                    'wrap-cmd #:wrap #t) 'key-wrap)))
  (check "wrap-stored" 1 result)
  (check "wrap-value" #t (prop-slot TOOL-BAR-ITEM-WRAP))
  ;; Wrap items should be disabled
  (check "wrap-disabled" #nil (prop-slot TOOL-BAR-ITEM-ENABLED-P)))

;; Test 15: :filter transforms binding
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'FilterItem)
                    'raw-cmd #:filter 'identity) 'key-filt)))
  (check "filter-applied" 1 result)
  (check "filter-binding" 'raw-cmd (prop-slot TOOL-BAR-ITEM-BINDING)))

;; Test 16: Keymap binding → should give up (return 0)
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'KeymapItem)
                    (list 'keymap (cons '?f 'find-file))) 'key-km)))
  (check "keymap-def-returns-0" 0 result))

;; Test 17: Label auto-generation from caption
(let ((result (parse-tool-bar-item
              (list 'menu-item (symbol-name 'AutoLabel)
                    'auto-cmd) 'key-auto)))
  (check "auto-label-returns-1" 1 result)
  ;; Label should be derived from caption, upcased
  (let ((label (prop-slot TOOL-BAR-ITEM-LABEL)))
    (check "auto-label-nonempty" #t (> (string-length label) 0))))

;;; --- process-tool-bar-item and append-tool-bar-item! -------------------

;; Setup: get the shared vector into a known state
(let ((count-before ((symbol-function '--tool-bar-items-count))))
  ;; Add a simple item via process-tool-bar-item
  (process-tool-bar-item 'added-key
    (list 'menu-item (symbol-name 'Added) 'added-cmd))
  (let ((count-after ((symbol-function '--tool-bar-items-count))))
    (check "process-add-increments-count"
           (+ count-before TOOL-BAR-ITEM-NSLOTS)
           count-after)))

;;; --- tool-bar-items end-to-end ----------------------------------------

;; tool-bar-items with fresh allocation (reuse = nil)
(let ((result (tool-bar-items #nil)))
  (let ((vec (car result))
        (nitems (cdr result)))
    (check "tool-bar-items-returns-vector" #t
           (not (eq? #nil ((symbol-function 'vectorp) vec))))
    (check "tool-bar-items-nitems-nonnegative" #t
           (>= nitems 0))))

;;; --- append-tool-bar-item! resizing -----------------------------------

;; Force a resize by adding many items.
((symbol-function '--set-tool-bar-items-count) 0)
(let ((initial-len ((symbol-function 'length)
                    ((symbol-function '--tool-bar-items-vector)))))
  ;; Add enough items to exceed 64 slots
  (do ((i 0 (1+ i)))
      ((>= i 20))
    (process-tool-bar-item
     (string->symbol (string-append "bulk-key-" (number->string i)))
     (list 'menu-item (string-append "Bulk" (number->string i))
           'bulk-cmd)))
  (let* ((new-len ((symbol-function 'length)
                   ((symbol-function '--tool-bar-items-vector))))
         (count ((symbol-function '--tool-bar-items-count))))
    (check "bulk-count-correct" (* 20 TOOL-BAR-ITEM-NSLOTS) count)
    ;; Vector should have grown beyond initial 64
    (check "vector-resized" #t (> new-len initial-len))))

;;; --- process-tool-bar-item: undefined removal -------------------------

;; Clear state first
((symbol-function '--set-tool-bar-items-count) 0)

;; Add two items
(process-tool-bar-item 'item-a
  (list 'menu-item (symbol-name 'ItemA) 'cmd-a))
(process-tool-bar-item 'item-b
  (list 'menu-item (symbol-name 'ItemB) 'cmd-b))

(let ((count-two ((symbol-function '--tool-bar-items-count))))
  (check "two-items-added" (* 2 TOOL-BAR-ITEM-NSLOTS) count-two)

  ;; Remove item-a via undefined
  (process-tool-bar-item 'item-a 'undefined)
  (let ((count-after-removal ((symbol-function '--tool-bar-items-count))))
    (check "remove-item-a" (* 1 TOOL-BAR-ITEM-NSLOTS) count-after-removal)

    ;; Verify remaining item is item-b
    (let ((vec ((symbol-function '--tool-bar-items-vector))))
      (check "remaining-is-item-b" 'item-b
             ((symbol-function 'aref) vec TOOL-BAR-ITEM-KEY)))))

;; Cleanup
((symbol-function '--set-tool-bar-items-count) 0)

;;; --- imp-3 round-trip gates -------------------------------------------
;;; Round-trip tests: build keymaps in elisp, feed through the full
;;; pipeline (map-keymap → process-tool-bar-item), read back vector
;;; and count directly via the imp-3.1 DEFUNs.
;;;
;;; We read the vector/count directly rather than calling tool-bar-items,
;;; which would rebuild from current-active-maps and discard our manual
;;; keymap walk.
;;;
;;; Traps:
;;;   - Elisp colon-symbols cross FFI as Guile keywords (#:enable, not ':enable)
;;;   - Use aref/aset for elisp vectors (Guile vector-ref doesn't work)
;;;   - Use #nil for elisp nil, not '() (they are distinct across FFI)

(let ((make-km    (symbol-function 'make-sparse-keymap))
      (define-k   (symbol-function 'define-key))
      (lookup-k   (symbol-function 'lookup-key))
      (keymapp-f  (symbol-function 'keymapp))
      (map-km     (symbol-function 'map-keymap))
      (aref-f     (symbol-function 'aref))
      (get-vec    (symbol-function '--tool-bar-items-vector))
      (get-cnt    (symbol-function '--tool-bar-items-count))
      (set-cnt    (symbol-function '--set-tool-bar-items-count))
      (vectorp-f  (symbol-function 'vectorp)))

  ;; --- RT1: Single item round-trip ---
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k inner (vector 'test-item)
              (list 'menu-item "TestItem" 'test-cmd #:help "Test help"))
    (define-k outer (vector 'tool-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tool-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tool-bar-item binding))
      (let* ((vec (get-vec))
             (cnt (/ (get-cnt) TOOL-BAR-ITEM-NSLOTS)))
        (check "rt1-single-count" 1 cnt)
        (check "rt1-caption" "TestItem"
               (aref-f vec TOOL-BAR-ITEM-CAPTION))
        (check "rt1-binding" 'test-cmd
               (aref-f vec TOOL-BAR-ITEM-BINDING))
        (check "rt1-help" "Test help"
               (aref-f vec TOOL-BAR-ITEM-HELP)))))

  ;; --- RT2: Two items, verify both present ---
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k inner (vector 'item1)
              (list 'menu-item "Item1" 'cmd1))
    (define-k inner (vector 'item2)
              (list 'menu-item "Item2" 'cmd2))
    (define-k outer (vector 'tool-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tool-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tool-bar-item binding))
      (let* ((vec (get-vec))
             (cnt (/ (get-cnt) TOOL-BAR-ITEM-NSLOTS)))
        (check "rt2-two-items-count" 2 cnt)
        (let ((caps (list (aref-f vec TOOL-BAR-ITEM-CAPTION)
                          (aref-f vec (+ TOOL-BAR-ITEM-NSLOTS
                                         TOOL-BAR-ITEM-CAPTION))))
              (binds (list (aref-f vec TOOL-BAR-ITEM-BINDING)
                           (aref-f vec (+ TOOL-BAR-ITEM-NSLOTS
                                          TOOL-BAR-ITEM-BINDING)))))
          (check "rt2-both-captions" '(#t #t)
                 (list (or (equal? "Item1" (car caps))
                           (equal? "Item1" (cadr caps)))
                       (or (equal? "Item2" (car caps))
                           (equal? "Item2" (cadr caps)))))
          (check "rt2-both-bindings" '(#t #t)
                 (list (or (equal? 'cmd1 (car binds))
                           (equal? 'cmd1 (cadr binds)))
                       (or (equal? 'cmd2 (car binds))
                           (equal? 'cmd2 (cadr binds)))))))))

  ;; --- RT3: :visible nil skips item ---
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k inner (vector 'always)
              (list 'menu-item "Always" 'always-cmd))
    (define-k inner (vector 'hidden)
              (list 'menu-item "Hidden" 'hidden-cmd #:visible #nil))
    (define-k outer (vector 'tool-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tool-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tool-bar-item binding))
      (let ((cnt (/ (get-cnt) TOOL-BAR-ITEM-NSLOTS)))
        (check "rt3-visible-filter-count" 1 cnt))))

  ;; --- RT4: Tool-bar-specific :image + :label round-trip ---
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k inner (vector 'img-item)
              (list 'menu-item "ImgItem" 'img-cmd
                    #:image (list 'image)
                    #:label "MyLabel"
                    #:vert-only #t))
    (define-k outer (vector 'tool-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tool-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tool-bar-item binding))
      (let* ((vec (get-vec))
             (cnt (/ (get-cnt) TOOL-BAR-ITEM-NSLOTS)))
        (check "rt4-img-item-count" 1 cnt)
        (check "rt4-image" (list 'image) (aref-f vec TOOL-BAR-ITEM-IMAGES))
        (check "rt4-label" "MyLabel" (aref-f vec TOOL-BAR-ITEM-LABEL))
        (check "rt4-vert-only" #t (aref-f vec TOOL-BAR-ITEM-VERT-ONLY)))))

  ;; --- RT5: Separator item ---
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k inner (vector 'sep) (list "--" ))
    (define-k outer (vector 'tool-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tool-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tool-bar-item binding))
      (let* ((vec (get-vec))
             (cnt (/ (get-cnt) TOOL-BAR-ITEM-NSLOTS)))
        (check "rt5-separator-count" 1 cnt)
        (check "rt5-sep-type-t" #t (aref-f vec TOOL-BAR-ITEM-TYPE))
        (check "rt5-sep-enabled-nil" #nil
               (aref-f vec TOOL-BAR-ITEM-ENABLED-P))
        (check "rt5-sep-caption-nil" #nil
               (aref-f vec TOOL-BAR-ITEM-CAPTION)))))

  ;; --- RT6: Empty keymap returns zero items ---
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k outer (vector 'tool-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tool-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tool-bar-item binding))
      (let* ((vec (get-vec))
             (cnt (/ (get-cnt) TOOL-BAR-ITEM-NSLOTS)))
        (check "rt6-empty-keymap-count" 0 cnt)
        (check "rt6-empty-returns-vector" #t
               (not (eq? #nil (vectorp-f vec)))))))

  ;; --- RT7: tool-bar-items returns proper cons shape ---
  (let* ((result (tool-bar-items #nil))
         (vec    (car result))
         (nitems (cdr result)))
    (check "rt7-cons-car-vectorp" #t (not (eq? #nil (vectorp-f vec))))
    (check "rt7-cons-cdr-fixnump" #t (integer? nitems))
    (check "rt7-cons-cdr-nonnegative" #t (>= nitems 0)))

  ;; --- imp-3.2: Separator IMAGES slot ---
  ;; Verifies that parse-tool-bar-item fills TOOL-BAR-ITEM-IMAGES
  ;; from tool-bar-separator-image-expression for separator items.
  (let* ((sym-val   (symbol-function 'symbol-value))
         (old-img   (sym-val 'tool-bar-separator-image-expression))
         ;; Use a quoted form that menu-item-eval-property can
         ;; evaluate safely: '(sep-test-image) → (sep-test-image).
         (test-img  (list 'quote '(sep-test-image))))
    ;; Set a known separator image expression.
    ((symbol-function 'set) 'tool-bar-separator-image-expression test-img)
    ;; Parse a separator — parse-tool-bar-item mutates the shared
    ;; properties vector, so read the IMAGES slot directly.
    (let ((result (parse-tool-bar-item (list "--") 'imp32-sep-key)))
      ;; The evaluated result should be (sep-test-image) — the
      ;; unquoted form of what we set.
      (check "imp32-separator-images" '(sep-test-image)
             ((symbol-function 'aref)
              ((symbol-function '--tool-bar-item-properties-vector))
              TOOL-BAR-ITEM-IMAGES)))
    ;; Restore original value.
    ((symbol-function 'set) 'tool-bar-separator-image-expression old-img))

  ;; --- imp-3.2: Help augmentation with keybinding ---
  ;; Verifies that parse-tool-bar-item appends "  (KEY-DESC)" to
  ;; the HELP slot when the binding has a key in current-global-map.
  (let* ((global-map  (symbol-function 'current-global-map))
         (define-k    (symbol-function 'define-key))
         (lookup-k    (symbol-function 'lookup-key))
         (f12-vec     (vector 'f12))
         ;; Save the old binding for [f12] so we can restore it.
         (old-binding (lookup-k (global-map) f12-vec)))
    (define-k (global-map) f12-vec 'imp32-test-cmd)
    ;; Parse an item whose binding is imp32-test-cmd, with a known
    ;; help string.
    (let ((result (parse-tool-bar-item
                   (list 'menu-item "Imp32Help"
                         'imp32-test-cmd #:help "Do the thing")
                   'imp32-help-key)))
      (check "imp32-help-augment-returns-1" 1 result)
      (let ((help-slot
             ((symbol-function 'aref)
              ((symbol-function '--tool-bar-item-properties-vector))
              TOOL-BAR-ITEM-HELP)))
        ;; HELP should be "Do the thing  (<f12>)" — the original help
        ;; with the keybinding appended.
        (check "imp32-help-has-key-suffix" #t
               (and (string? help-slot)
                    (> (string-length help-slot)
                       (string-length "Do the thing"))))))
    ;; Restore the old binding (or undefine if there was none).
    (if (eq? old-binding #nil)
        (define-k (global-map) f12-vec 'undefined)
        (define-k (global-map) f12-vec old-binding))))