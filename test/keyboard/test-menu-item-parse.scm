;;; test-menu-item-parse.scm --- M10 imp-1.3 test corpus for parse-menu-item
;;;
;;; Sourced by test/keyboard/test-menu-item-parse.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch stdout.

(use-modules (emacs menu-item-parse))

;;; Access item_properties slot N via the module's public API.
(define (slot n)
  ((symbol-function 'aref) (item-properties) n))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

;; Test 1: Old format, string car with symbol def
(let ((result (parse-menu-item (cons (symbol-name 'File) 'my-cmd) 1)))
  (check "old-format-result" 1 result)
  (check "old-format-name" "File" (slot ITEM-PROPERTY-NAME)))

;; Test 2: New format with :visible nil → skip
(let ((result (parse-menu-item (list 'menu-item (symbol-name 'Save)
                                     'save-buffer #:visible #nil) 1)))
  (check "visible-nil-skips" 0 result))

;; Test 3: New format with :enable and :help
;; Use #t (elisp t, already verified eq?-identical to Qt).
;; Plain `t` is an unbound Guile variable, not elisp t.
(let ((result (parse-menu-item (list 'menu-item (symbol-name 'Save)
                                     'save-buffer #:enable #t
                                     #:help (symbol-name 'Save-buffer)) 1)))
  (check "enable+help-returns-1" 1 result))

;; Test 4: Malformed plist — lone :enable with no value (Bug 1 test)
(let ((result (parse-menu-item (list 'menu-item (symbol-name 'Test)
                                     'cmd #:enable) 1)))
  (check "malformed-plist-returns-1" 1 result))

;; Test 5: Keymap def → returns MAP set
(let ((result (parse-menu-item (list 'menu-item (symbol-name 'File)
                                     (list 'keymap (cons '?f 'find-file))) 1)))
  (check "keymap-def-returns-1" 1 result)
  (check "map-set-eq-def" (slot ITEM-PROPERTY-DEF) (slot ITEM-PROPERTY-MAP)))
