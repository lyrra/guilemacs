;;; test-tab-bar-items.scm --- M10 imp-2.2 test corpus for tab-bar-items
;;;
;;; Sourced by test/keyboard/test-tab-bar-items.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch stdout.

(use-modules (emacs tab-bar-items))

;;; Access tab_bar_item_properties slot N via module's public API.
(define (prop-slot n)
  ((symbol-function 'aref)
   ((symbol-function '--tab-bar-item-properties-vector))
   n))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

;;; --- Slot constants ----------------------------------------------------

(check "slot-key"        0 TAB-BAR-ITEM-KEY)
(check "slot-enabled-p"  1 TAB-BAR-ITEM-ENABLED-P)
(check "slot-selected-p" 2 TAB-BAR-ITEM-SELECTED-P)
(check "slot-caption"    3 TAB-BAR-ITEM-CAPTION)
(check "slot-binding"    4 TAB-BAR-ITEM-BINDING)
(check "slot-help"       5 TAB-BAR-ITEM-HELP)
(check "slot-nslots"     6 TAB-BAR-ITEM-NSLOTS)

;;; --- parse-tab-bar-item ------------------------------------------------

;; Test 1: Non-cons → 0
(let ((result (parse-tab-bar-item 'not-a-list 'key-x)))
  (check "non-cons-returns-0" 0 result))

;; Test 2: Old-style separator: ("--dashes") → valid separator
(let ((result (parse-tab-bar-item (list "--") 'sep-key)))
  (check "separator-dashes-returns-1" 1 result))

;; Test 3: Old-style named separator: ("--space") → valid
(let ((result (parse-tab-bar-item (list "--space") 'sep-key)))
  (check "separator-named-returns-1" 1 result)
  (check "separator-caption-nil" #nil (prop-slot TAB-BAR-ITEM-CAPTION))
  (check "separator-enabled-nil" #nil (prop-slot TAB-BAR-ITEM-ENABLED-P)))

;; Test 4: String caption without rest → separator, caption set
(let ((result (parse-tab-bar-item (list (symbol-name 'Tab)) 'key-tab)))
  (check "string-only-non-sep-returns-0" 0 result))

;; Test 5: New format with :visible nil → skip
(let ((result (parse-tab-bar-item
              (list 'menu-item (symbol-name 'MyTab)
                    'my-cmd #:visible #nil) 'key-vis)))
  (check "visible-nil-skips" 0 result))

;; Test 6: New format, basic valid item
(let ((result (parse-tab-bar-item
              (list 'menu-item (symbol-name 'MyTab)
                    'my-cmd) 'key-basic)))
  (check "basic-item-returns-1" 1 result)
  (check "basic-caption-set" (symbol-name 'MyTab)
         (prop-slot TAB-BAR-ITEM-CAPTION))
  (check "basic-binding-set" 'my-cmd
         (prop-slot TAB-BAR-ITEM-BINDING))
  (check "basic-enabled-default-t" #t
         (prop-slot TAB-BAR-ITEM-ENABLED-P)))

;; Test 7: New format with :enable nil
(let ((result (parse-tab-bar-item
              (list 'menu-item (symbol-name 'Disabled)
                    'some-cmd #:enable #nil) 'key-dis)))
  ;; :enable #nil is stored as-is; it gets evaluated later.
  ;; menu-item-eval-property of #nil → #nil, so enabled becomes nil.
  (check "enable-nil-stored" 1 result))

;; Test 8: New format with :help string
(let ((result (parse-tab-bar-item
              (list 'menu-item (symbol-name 'HelpTab)
                    'help-cmd #:help (symbol-name 'Help-text)) 'key-help)))
  (check "help-string-stored" 1 result)
  (check "help-value" (symbol-name 'Help-text)
         (prop-slot TAB-BAR-ITEM-HELP)))

;; Test 9: New format with :button toggle — selected state
(let ((result (parse-tab-bar-item
              (list 'menu-item (symbol-name 'ToggleTab)
                    'toggle-cmd #:button (cons #:toggle #t)) 'key-tog)))
  (check "toggle-selected" 1 result)
  (check "toggle-selected-t" #t (prop-slot TAB-BAR-ITEM-SELECTED-P)))

;; Test 10: New format with :filter
(let ((result (parse-tab-bar-item
              (list 'menu-item (symbol-name 'FilterTab)
                    'raw-cmd #:filter 'identity) 'key-filt)))
  (check "filter-applied" 1 result)
  ;; identity filter: (identity '(raw-cmd)) → (raw-cmd)
  ;; But after eval, the binding should be 'raw-cmd.
  ;; Actually menu-item-eval-property evaluates the form,
  ;; and (identity '(raw-cmd)) = (raw-cmd).
  ;; So binding should be raw-cmd.
  (check "filter-binding" 'raw-cmd (prop-slot TAB-BAR-ITEM-BINDING)))

;; Test 11: Malformed plist — lone :enable with no value
(let ((result (parse-tab-bar-item
              (list 'menu-item (symbol-name 'Test)
                    'cmd #:enable) 'key-mal)))
  (check "malformed-plist-returns-1" 1 result))

;; Test 12: Keymap binding → should give up (return 0)
(let ((result (parse-tab-bar-item
              (list 'menu-item (symbol-name 'KeymapTab)
                    (list 'keymap (cons '?f 'find-file))) 'key-km)))
  (check "keymap-def-returns-0" 0 result))

;;; --- process-tab-bar-item and append-tab-bar-item! --------------------

;; Setup: get the shared vector into a known state
;; First, call tab-bar-items with #nil reuse to init the vector
(let ((count-before ((symbol-function '--tab-bar-items-count))))
  ;; Add a simple item via process-tab-bar-item
  (process-tab-bar-item 'added-key
    (list 'menu-item (symbol-name 'Added) 'added-cmd))
  (let ((count-after ((symbol-function '--tab-bar-items-count))))
    (check "process-add-increments-count"
           (+ count-before TAB-BAR-ITEM-NSLOTS)
           count-after)))

;;; --- tab-bar-items end-to-end -----------------------------------------

;; tab-bar-items with fresh allocation (reuse = nil)
(let ((result (tab-bar-items #nil)))
  (let ((vec (car result))
        (nitems (cdr result)))
    (check "tab-bar-items-returns-vector" #t
           (not (eq? #nil ((symbol-function 'vectorp) vec))))
    (check "tab-bar-items-nitems-nonnegative" #t
           (>= nitems 0))))

;;; --- append-tab-bar-item! resizing ------------------------------------

;; Force a resize by adding many items.  Reset count first so this test
;; doesn't inherit items left over from the tab-bar-items map-keymap walk.
((symbol-function '--set-tab-bar-items-count) 0)
(let ((initial-len ((symbol-function 'length)
                    ((symbol-function '--tab-bar-items-vector)))))
  ;; Add enough items to exceed 64 slots
  (do ((i 0 (1+ i)))
      ((>= i 20))
    (process-tab-bar-item
     (string->symbol (string-append "bulk-key-" (number->string i)))
     (list 'menu-item (string-append "Bulk" (number->string i))
           'bulk-cmd)))
  (let* ((new-len ((symbol-function 'length)
                   ((symbol-function '--tab-bar-items-vector))))
         (count ((symbol-function '--tab-bar-items-count))))
    (check "bulk-count-correct" (* 20 TAB-BAR-ITEM-NSLOTS) count)
    ;; Vector should have grown beyond initial 64
    (check "vector-resized" #t (> new-len initial-len))))

;;; --- process-tab-bar-item: undefined removal --------------------------

;; Clear state first
((symbol-function '--set-tab-bar-items-count) 0)

;; Add two items
(process-tab-bar-item 'item-a
  (list 'menu-item (symbol-name 'ItemA) 'cmd-a))
(process-tab-bar-item 'item-b
  (list 'menu-item (symbol-name 'ItemB) 'cmd-b))

(let ((count-two ((symbol-function '--tab-bar-items-count))))
  (check "two-items-added" (* 2 TAB-BAR-ITEM-NSLOTS) count-two)

  ;; Remove item-a via undefined
  (process-tab-bar-item 'item-a 'undefined)
  (let ((count-after-removal ((symbol-function '--tab-bar-items-count))))
    (check "remove-item-a" (* 1 TAB-BAR-ITEM-NSLOTS) count-after-removal)

    ;; Verify remaining item is item-b
    (let ((vec ((symbol-function '--tab-bar-items-vector))))
      (check "remaining-is-item-b" 'item-b
             ((symbol-function 'aref) vec TAB-BAR-ITEM-KEY)))))

;; Cleanup
((symbol-function '--set-tab-bar-items-count) 0)

;;; --- imp-2.4 round-trip gate -------------------------------------------
;;; Round-trip tests: build keymaps in elisp, feed through the full
;;; pipeline (map-keymap → process-tab-bar-item), read back vector
;;; and count directly via the imp-2.1 DEFUNs.
;;;
;;; We read the vector/count directly rather than calling tab-bar-items,
;;; which would rebuild from current-active-maps and discard our manual
;;; keymap walk.
;;;
;;; Traps (same as imp-1.3):
;;;   - Elisp colon-symbols cross FFI as Guile keywords (#:enable, not ':enable)
;;;   - Use aref/aset for elisp vectors (Guile vector-ref doesn't work)
;;;   - Use #nil for elisp nil, not '() (they are distinct across FFI)
;;;   - Vinhibit_quit: FIX-20260710-guilemacs — should use dynamic-wind,
;;;     currently plain save/restore (see tab-bar-items.scm for rationale)

(let ((make-km    (symbol-function 'make-sparse-keymap))
      (define-k   (symbol-function 'define-key))
      (lookup-k   (symbol-function 'lookup-key))
      (keymapp-f  (symbol-function 'keymapp))
      (map-km     (symbol-function 'map-keymap))
      (aref-f     (symbol-function 'aref))
      (get-vec    (symbol-function '--tab-bar-items-vector))
      (get-cnt    (symbol-function '--tab-bar-items-count))
      (set-cnt    (symbol-function '--set-tab-bar-items-count))
      (vectorp-f  (symbol-function 'vectorp)))

  ;; --- RT1: Single item round-trip ---
  ;; Build a keymap with one tab-bar entry, walk it, verify vector.
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k inner (vector 'test-item)
              (list 'menu-item "TestItem" 'test-cmd #:help "Test help"))
    (define-k outer (vector 'tab-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tab-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tab-bar-item binding))
      (let* ((vec (get-vec))
             (cnt (/ (get-cnt) TAB-BAR-ITEM-NSLOTS)))
        (check "roundtrip-single-count" 1 cnt)
        (check "roundtrip-caption" "TestItem"
               (aref-f vec TAB-BAR-ITEM-CAPTION))
        (check "roundtrip-binding" 'test-cmd
               (aref-f vec TAB-BAR-ITEM-BINDING))
        (check "roundtrip-help" "Test help"
               (aref-f vec TAB-BAR-ITEM-HELP)))))

  ;; --- RT2: Two items, verify both present (order-independent) ---
  ;; map-keymap may iterate bindings in reverse-key or definition
  ;; order; we only assert that both items ended up in the vector.
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k inner (vector 'item1)
              (list 'menu-item "Item1" 'cmd1))
    (define-k inner (vector 'item2)
              (list 'menu-item "Item2" 'cmd2))
    (define-k outer (vector 'tab-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tab-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tab-bar-item binding))
      (let* ((vec (get-vec))
             (cnt (/ (get-cnt) TAB-BAR-ITEM-NSLOTS)))
        (check "roundtrip-two-items-count" 2 cnt)
        ;; Collect captions from both slots and verify as a set.
        (let ((caps (list (aref-f vec TAB-BAR-ITEM-CAPTION)
                          (aref-f vec (+ TAB-BAR-ITEM-NSLOTS
                                         TAB-BAR-ITEM-CAPTION))))
              (binds (list (aref-f vec TAB-BAR-ITEM-BINDING)
                           (aref-f vec (+ TAB-BAR-ITEM-NSLOTS
                                          TAB-BAR-ITEM-BINDING)))))
          (check "roundtrip-both-captions" '(#t #t)
                 (list (or (equal? "Item1" (car caps))
                           (equal? "Item1" (cadr caps)))
                       (or (equal? "Item2" (car caps))
                           (equal? "Item2" (cadr caps)))))
          (check "roundtrip-both-bindings" '(#t #t)
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
    (define-k outer (vector 'tab-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tab-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tab-bar-item binding))
      (let ((cnt (/ (get-cnt) TAB-BAR-ITEM-NSLOTS)))
        (check "roundtrip-visible-filter-count" 1 cnt))))

  ;; --- RT4: Separator item survives ---
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k inner (vector 'sep)
              (list "--" ))  ;; old-style separator
    (define-k outer (vector 'tab-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tab-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tab-bar-item binding))
      (let* ((vec (get-vec))
             (cnt (/ (get-cnt) TAB-BAR-ITEM-NSLOTS)))
        (check "roundtrip-separator-count" 1 cnt)
        (check "roundtrip-sep-enabled-nil" #nil
               (aref-f vec TAB-BAR-ITEM-ENABLED-P))
        (check "roundtrip-sep-caption-nil" #nil
               (aref-f vec TAB-BAR-ITEM-CAPTION)))))

  ;; --- RT5: :enable nil stored, evaluated later ---
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k inner (vector 'disabled-item)
              (list 'menu-item "Disabled" 'disabled-cmd #:enable #nil))
    (define-k outer (vector 'tab-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tab-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tab-bar-item binding))
      (let* ((vec (get-vec))
             (cnt (/ (get-cnt) TAB-BAR-ITEM-NSLOTS)))
        (check "roundtrip-enable-nil-count" 1 cnt)
        (check "roundtrip-enable-is-nil" #nil
               (aref-f vec TAB-BAR-ITEM-ENABLED-P)))))

  ;; --- RT6: :filter transforms binding ---
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k inner (vector 'filtered)
              (list 'menu-item "Filtered" 'raw #:filter 'identity))
    (define-k outer (vector 'tab-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tab-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tab-bar-item binding))
      (let* ((vec (get-vec))
             (cnt (/ (get-cnt) TAB-BAR-ITEM-NSLOTS)))
        (check "roundtrip-filter-count" 1 cnt)
        (check "roundtrip-filter-binding" 'raw
               (aref-f vec TAB-BAR-ITEM-BINDING)))))

  ;; --- RT7: Return shape is proper (cons vector fixnum) ---
  ;; This one DOES call tab-bar-items to verify the public API shape.
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k inner (vector 'shape-test)
              (list 'menu-item "Shape" 'shape-cmd))
    (define-k outer (vector 'tab-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tab-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tab-bar-item binding))
      ;; After manual walk, verify the vector/count are consistent
      ;; and that tab-bar-items returns a proper cons shape from
      ;; current-active-maps (which may or may not include our item).
      (let* ((result (tab-bar-items #nil))
             (vec    (car result))
             (nitems (cdr result)))
        (check "roundtrip-cons-car-vectorp" #t
               (not (eq? #nil (vectorp-f vec))))
        (check "roundtrip-cons-cdr-fixnump" #t
               (integer? nitems))
        (check "roundtrip-cons-cdr-positive" #t
               (>= nitems 0)))))

  ;; --- RT8: Empty keymap returns zero items ---
  (let* ((inner (make-km))
         (outer (make-km)))
    (define-k outer (vector 'tab-bar) inner)
    (set-cnt 0)
    (let ((binding (lookup-k outer #(tab-bar))))
      (when (not (eq? #nil (keymapp-f binding)))
        (map-km process-tab-bar-item binding))
      (let* ((vec (get-vec))
             (cnt (/ (get-cnt) TAB-BAR-ITEM-NSLOTS)))
        (check "roundtrip-empty-keymap-count" 0 cnt)
        (check "roundtrip-empty-returns-vector" #t
               (not (eq? #nil (vectorp-f vec))))))))
