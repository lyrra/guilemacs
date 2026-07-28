;;; test-menu-bar-items.scm --- M10 imp-4.1 test corpus for menu-bar-items
;;;
;;; Sourced by test/keyboard/test-menu-bar-items.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch stdout.
;;;
;;; Since process-menu-bar-item is a stub (throws "unimplemented in
;;; imp-4.1"), we cannot do a full map-keymap round-trip.  Instead we
;;; test:
;;;   1. Slot constants
;;;   2. Infrastructure DEFUNs getter/setter round-trip
;;;   3. menu-bar-items on empty keymaps → sentinel-only vector
;;;   4. Manual vector manipulation (simulating a single item)
;;;   5. final-items-rotate! reordering

(use-modules (emacs menu-bar-items))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

;;; --- Slot constants ----------------------------------------------------

(check "slot-key"    0 MENU-BAR-ITEM-KEY)
(check "slot-string" 1 MENU-BAR-ITEM-STRING)
(check "slot-def"    2 MENU-BAR-ITEM-DEF)
(check "slot-hpos"   3 MENU-BAR-ITEM-HPOS)
(check "slot-nslots" 4 MENU-BAR-ITEM-NSLOTS)

;;; --- Infrastructure DEFUNs round-trip ----------------------------------

;; --menu-bar-items-vector: lazy-init to 24 slots, set, get back.
(let* ((vec-getter (symbol-function '--menu-bar-items-vector))
       (vec-setter (symbol-function '--set-menu-bar-items-vector))
       (aref-f     (symbol-function 'aref))
       (aset-f     (symbol-function 'aset))
       (length-f   (symbol-function 'length))
       ;; Get the existing vector (lazy-inits if nil).
       (v1 (vec-getter)))
  (check "vec-getter-returns-vector" #t
         (not (eq? #nil ((symbol-function 'vectorp) v1))))
  (check "vec-lazy-init-24-slots" 24 (length-f v1))
  ;; Write a known value into slot 0 and verify round-trip.
  (aset-f v1 0 'roundtrip-marker)
  (vec-setter v1)
  (let ((v2 (vec-getter)))
    (check "vec-get-after-set" 'roundtrip-marker (aref-f v2 0))
    (check "vec-identity" v1 v2)))

;; --menu-bar-items-index: set, get back.
(let* ((idx-getter (symbol-function '--menu-bar-items-index))
       (idx-setter (symbol-function '--set-menu-bar-items-index)))
  (idx-setter 42)
  (check "idx-get-after-set" 42 (idx-getter))
  (idx-setter 0)
  (check "idx-reset-to-zero" 0 (idx-getter)))

;;; --- menu-bar-items on empty keymaps -----------------------------------
;;; With no [menu-bar] keymap binding in current-active-maps, the walk
;;; produces zero items.  We still get the sentinel appended (4 nils)
;;; and the vector returned directly (no nitems — unlike tab/tool-bar).

(let* ((mb-items     menu-bar-items)
       (aref-f       (symbol-function 'aref))
       (length-f     (symbol-function 'length))
       (vectorp-f    (symbol-function 'vectorp))
       (idx-getter   (symbol-function '--menu-bar-items-index))
       (vec-getter   (symbol-function '--menu-bar-items-vector))
       ;; Call menu-bar-items with nil to force fresh allocation.
       (result (mb-items #nil)))

  ;; menu-bar-items returns a vector directly (not a cons).
  (check "empty-returns-vector" #t (not (eq? #nil (vectorp-f result))))
  ;; The index should be 4 (sentinel appended).
  (check "empty-index-is-4" 4 (idx-getter))
  ;; The first 4 slots should all be nil (the sentinel).
  (check "empty-slot-0-nil" #nil (aref-f result 0))
  (check "empty-slot-1-nil" #nil (aref-f result 1))
  (check "empty-slot-2-nil" #nil (aref-f result 2))
  (check "empty-slot-3-nil" #nil (aref-f result 3)))

;;; --- Manual single-item setup ------------------------------------------
;;; Simulate what the inner callback would do: ASET 4 values, bump index
;;; by 4, then read back and verify.

(let* ((aset-f       (symbol-function 'aset))
       (aref-f       (symbol-function 'aref))
       (length-f     (symbol-function 'length))
       (vec-getter   (symbol-function '--menu-bar-items-vector))
       (vec-setter   (symbol-function '--set-menu-bar-items-vector))
       (idx-getter   (symbol-function '--menu-bar-items-index))
       (idx-setter   (symbol-function '--set-menu-bar-items-index))
       (larger-vec   (symbol-function '--larger-vector))
       (vectorp-f    (symbol-function 'vectorp)))

  ;; Start fresh.
  (vec-getter)                           ; ensure lazy-init
  (idx-setter 0)

  ;; Simulate process-menu-bar-item appending one item.
  (let* ((vec (vec-getter))
         (idx 0))
    ;; Grow if needed (won't be needed for 4 slots in a 24-slot vector).
    (when (> (+ idx 4) (length-f vec))
      (set! vec (larger-vec vec 4 -1))
      (vec-setter vec))
    ;; Write item: KEY=foo, STRING="Foo", DEF=foo-cmd, HPOS=nil.
    (aset-f vec (+ idx MENU-BAR-ITEM-KEY)    'foo)
    (aset-f vec (+ idx MENU-BAR-ITEM-STRING) "Foo")
    (aset-f vec (+ idx MENU-BAR-ITEM-DEF)    'foo-cmd)
    (aset-f vec (+ idx MENU-BAR-ITEM-HPOS)   3)
    (idx-setter (+ idx 4)))

  ;; Now append the sentinel (4 nils).
  (let* ((vec (vec-getter))
         (idx (idx-getter)))
    (when (> (+ idx 4) (length-f vec))
      (set! vec (larger-vec vec 4 -1))
      (vec-setter vec))
    (aset-f vec (+ idx 0) #nil)
    (aset-f vec (+ idx 1) #nil)
    (aset-f vec (+ idx 2) #nil)
    (aset-f vec (+ idx 3) #nil)
    (idx-setter (+ idx 4)))

  ;; Verify: index = 8, item at slots 0-3, sentinel at 4-7.
  (check "single-idx-is-8" 8 (idx-getter))
  (let ((v (vec-getter)))
    (check "single-key"     'foo     (aref-f v 0))
    (check "single-string"  "Foo"    (aref-f v 1))
    (check "single-def"     'foo-cmd (aref-f v 2))
    (check "single-hpos"    3        (aref-f v 3))
    (check "single-sentinel-0" #nil  (aref-f v 4))
    (check "single-sentinel-1" #nil  (aref-f v 5))
    (check "single-sentinel-2" #nil  (aref-f v 6))
    (check "single-sentinel-3" #nil  (aref-f v 7))))

;;; --- final-items-rotate! -----------------------------------------------
;;; Set up 2 items (8 slots), put item-b in menu-bar-final-items,
;;; call final-items-rotate!, verify item-b moved to the tail.

(let* ((aset-f       (symbol-function 'aset))
       (aref-f       (symbol-function 'aref))
       (length-f     (symbol-function 'length))
       (vec-getter   (symbol-function '--menu-bar-items-vector))
       (vec-setter   (symbol-function '--set-menu-bar-items-vector))
       (idx-getter   (symbol-function '--menu-bar-items-index))
       (idx-setter   (symbol-function '--set-menu-bar-items-index))
       (sym-val      (symbol-function 'symbol-value))
       (set-f        (symbol-function 'set))
       (larger-vec   (symbol-function '--larger-vector)))

  ;; Reset state.
  (vec-getter)
  (idx-setter 0)

  ;; Save old value of menu-bar-final-items.
  (let ((old-final-items (sym-val 'menu-bar-final-items))
        (vec (vec-getter)))

    ;; Set up 2 items manually at slots 0-3 and 4-7.
    ;; Item A: KEY=item-a, STRING="Item A", DEF=cmd-a, HPOS=1
    (aset-f vec (+ 0 MENU-BAR-ITEM-KEY)    'item-a)
    (aset-f vec (+ 0 MENU-BAR-ITEM-STRING) "Item A")
    (aset-f vec (+ 0 MENU-BAR-ITEM-DEF)    'cmd-a)
    (aset-f vec (+ 0 MENU-BAR-ITEM-HPOS)   1)
    ;; Item B: KEY=item-b, STRING="Item B", DEF=cmd-b, HPOS=2
    (aset-f vec (+ 4 MENU-BAR-ITEM-KEY)    'item-b)
    (aset-f vec (+ 4 MENU-BAR-ITEM-STRING) "Item B")
    (aset-f vec (+ 4 MENU-BAR-ITEM-DEF)    'cmd-b)
    (aset-f vec (+ 4 MENU-BAR-ITEM-HPOS)   2)

    ;; Set index to 8 (2 items × 4 slots).
    (idx-setter 8)

    ;; Verify initial state: item-a at 0-3, item-b at 4-7.
    (check "rotate-before-key-a" 'item-a (aref-f vec (+ 0 MENU-BAR-ITEM-KEY)))
    (check "rotate-before-key-b" 'item-b (aref-f vec (+ 4 MENU-BAR-ITEM-KEY)))

    ;; Put item-b in menu-bar-final-items — this tells the rotator to
    ;; move it to the end.
    (set-f 'menu-bar-final-items '(item-b))

    ;; Call final-items-rotate! with the current index.
    (final-items-rotate! vec (idx-getter))

    ;; After rotation, item-b should be at slots 0-3 (moved to what was
    ;; the end before any shift) and item-a should be at 4-7.
    ;; Actually the rotation moves item-b FROM its current position TO
    ;; the end: item-a shifts left into slots 0-3, item-b goes to 4-7.
    (check "rotate-after-key-at-0" 'item-a (aref-f vec (+ 0 MENU-BAR-ITEM-KEY)))
    (check "rotate-after-key-at-4" 'item-b (aref-f vec (+ 4 MENU-BAR-ITEM-KEY)))

    ;; Restore old value.
    (set-f 'menu-bar-final-items old-final-items)))

;;; --- final-items-rotate! with three items ------------------------------
;;; Set up 3 items, put item-c (last) in final-items — no-op.
;;; Put item-a (first) in final-items — rotates to end.

(let* ((aset-f       (symbol-function 'aset))
       (aref-f       (symbol-function 'aref))
       (vec-getter   (symbol-function '--menu-bar-items-vector))
       (idx-setter   (symbol-function '--set-menu-bar-items-index))
       (sym-val      (symbol-function 'symbol-value))
       (set-f        (symbol-function 'set)))

  ;; Reset state and save old value.
  (let ((old-final-items (sym-val 'menu-bar-final-items))
        (vec (vec-getter)))

    ;; Set up 3 items at slots 0-3, 4-7, 8-11.
    (aset-f vec (+ 0 MENU-BAR-ITEM-KEY) 'a) (aset-f vec (+ 0 MENU-BAR-ITEM-STRING) "A")
    (aset-f vec (+ 0 MENU-BAR-ITEM-DEF) 'ca) (aset-f vec (+ 0 MENU-BAR-ITEM-HPOS) 1)
    (aset-f vec (+ 4 MENU-BAR-ITEM-KEY) 'b) (aset-f vec (+ 4 MENU-BAR-ITEM-STRING) "B")
    (aset-f vec (+ 4 MENU-BAR-ITEM-DEF) 'cb) (aset-f vec (+ 4 MENU-BAR-ITEM-HPOS) 2)
    (aset-f vec (+ 8 MENU-BAR-ITEM-KEY) 'c) (aset-f vec (+ 8 MENU-BAR-ITEM-STRING) "C")
    (aset-f vec (+ 8 MENU-BAR-ITEM-DEF) 'cc) (aset-f vec (+ 8 MENU-BAR-ITEM-HPOS) 3)
    (idx-setter 12)

    ;; Test 1: put 'c (last item) in final-items → no-op (already at end).
    (set-f 'menu-bar-final-items '(c))
    (final-items-rotate! vec 12)
    (check "rotate3-c-first-pos" 'a (aref-f vec (+ 0 MENU-BAR-ITEM-KEY)))
    (check "rotate3-c-mid-pos"   'b (aref-f vec (+ 4 MENU-BAR-ITEM-KEY)))
    (check "rotate3-c-last-pos"  'c (aref-f vec (+ 8 MENU-BAR-ITEM-KEY)))

    ;; Test 2: put 'a (first item) in final-items → move to end.
    ;; Result should be: b, c, a.
    (set-f 'menu-bar-final-items '(a))
    (final-items-rotate! vec 12)
    (check "rotate3-a-new-first" 'b (aref-f vec (+ 0 MENU-BAR-ITEM-KEY)))
    (check "rotate3-a-new-mid"   'c (aref-f vec (+ 4 MENU-BAR-ITEM-KEY)))
    (check "rotate3-a-new-last"  'a (aref-f vec (+ 8 MENU-BAR-ITEM-KEY)))

    ;; Test 3: put 'b in final-items on the reordered [b,c,a] vector.
    ;; Result should be: c, a, b.
    (set-f 'menu-bar-final-items '(b))
    (final-items-rotate! vec 12)
    (check "rotate3-b-new-first" 'c (aref-f vec (+ 0 MENU-BAR-ITEM-KEY)))
    (check "rotate3-b-new-mid"   'a (aref-f vec (+ 4 MENU-BAR-ITEM-KEY)))
    (check "rotate3-b-new-last"  'b (aref-f vec (+ 8 MENU-BAR-ITEM-KEY)))

    ;; Restore.
    (set-f 'menu-bar-final-items old-final-items)))
