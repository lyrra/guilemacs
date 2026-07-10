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
