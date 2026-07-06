(define-module (emacs menu-item-parse)
  #:use-module (emacs elisp-ref)
  #:use-module (emacs-elisp runtime)
  #:declarative? #t
  #:export (menu-item-eval-property
            item-properties
            ITEM-PROPERTY-ITEM ITEM-PROPERTY-NAME ITEM-PROPERTY-DEF
            ITEM-PROPERTY-MAP ITEM-PROPERTY-TYPE ITEM-PROPERTY-KEYEQ
            ITEM-PROPERTY-SELECTED ITEM-PROPERTY-HELP
            ITEM-PROPERTY-ENABLE ITEM-PROPERTY-MAX))

;;; M10 imp-1.2 — infrastructure for the parse-menu-item Scheme port.
;;; Exposes the C menu_item_eval_property helper and the shared
;;; item_properties vector to Scheme, matching M9's imp-8.1 pattern
;;; (thin C DEFUNs; Scheme owns the logic in imp-1.3+).

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
;;; Scheme reads/writes via stock vector-ref / vector-set!.
(define (item-properties)
  ((force %--item-properties-vector)))
