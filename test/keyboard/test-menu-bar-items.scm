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

;;; --- menu-bar-items end-to-end (live env) ------------------------------
;;; With the callback ported (imp-4.3), a bare-batch startup DOES have a
;;; populated [menu-bar] keymap in global-map (File, Edit, Options, …
;;; from loadup).  The walk parses them and appends the sentinel.  We
;;; can't assert exact contents (loadup evolves), but we can assert the
;;; invariants: vector returned, index is a positive multiple of 4, and
;;; the last 4 slots are the sentinel (all nil).

(let* ((mb-items   menu-bar-items)
       (aref-f     (symbol-function 'aref))
       (vectorp-f  (symbol-function 'vectorp))
       (idx-getter (symbol-function '--menu-bar-items-index))
       (result     (mb-items #nil))
       (idx        (idx-getter)))
  (check "walk-returns-vector"      #t (not (eq? #nil (vectorp-f result))))
  (check "walk-index-positive"      #t (> idx 0))
  (check "walk-index-multiple-of-4" 0 (modulo idx 4))
  ;; Sentinel occupies slots (idx-4) .. (idx-1).
  (check "walk-sentinel-key"    #nil (aref-f result (- idx 4)))
  (check "walk-sentinel-string" #nil (aref-f result (- idx 3)))
  (check "walk-sentinel-def"    #nil (aref-f result (- idx 2)))
  (check "walk-sentinel-hpos"   #nil (aref-f result (- idx 1))))

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

;;; --- process-menu-bar-item round-trip ----------------------------------
;;; Drive the callback directly with synthetic (menu-item …) forms and
;;; verify vector state.  Each sub-test calls `reset!' first, which zeros
;;; the index and clears the per-map dedup list — the state the outer
;;; walk establishes before each map-keymap-canonical call.

(let* ((aref-f       (symbol-function 'aref))
       (vec-getter   (symbol-function '--menu-bar-items-vector))
       (idx-getter   (symbol-function '--menu-bar-items-index))
       (idx-setter   (symbol-function '--set-menu-bar-items-index))
       (dedup-setter (symbol-function '--set-menu-bar-one-keymap-changed-items))
       (car-f        (symbol-function 'car))
       (cdr-f        (symbol-function 'cdr))
       (make-km      (symbol-function 'make-sparse-keymap))
       (reset!       (lambda () (idx-setter 0) (dedup-setter #nil))))

  ;; --- RT1: single item appended ---------------------------------------
  (reset!)
  (process-menu-bar-item 'k1 (list 'menu-item "One" 'cmd1))
  (let ((v (vec-getter)))
    (check "rt1-index-is-4" 4 (idx-getter))
    (check "rt1-key"        'k1   (aref-f v MENU-BAR-ITEM-KEY))
    (check "rt1-string"     "One" (aref-f v MENU-BAR-ITEM-STRING))
    ;; DEF slot is an elisp list of one element: (cmd1).
    (check "rt1-map-car"    'cmd1 (car-f (aref-f v MENU-BAR-ITEM-DEF)))
    (check "rt1-map-cdr"    #nil  (cdr-f (aref-f v MENU-BAR-ITEM-DEF)))
    (check "rt1-hpos"       0     (aref-f v MENU-BAR-ITEM-HPOS)))

  ;; --- RT2: nil def is dropped -----------------------------------------
  (reset!)
  (process-menu-bar-item 'k2 #nil)
  (check "rt2-nil-def-no-add" 0 (idx-getter))

  ;; --- RT3: dedup guard within one map ---------------------------------
  ;; Second call for the same KEY (with dedup list unchanged) is
  ;; suppressed — index stays at 4, first STRING wins.
  (reset!)
  (process-menu-bar-item 'k3 (list 'menu-item "First"  'cmdA))
  (process-menu-bar-item 'k3 (list 'menu-item "Second" 'cmdB))
  (let ((v (vec-getter)))
    (check "rt3-dedup-index"  4       (idx-getter))
    (check "rt3-dedup-string" "First" (aref-f v MENU-BAR-ITEM-STRING))
    (check "rt3-dedup-car"    'cmdA   (car-f (aref-f v MENU-BAR-ITEM-DEF))))

  ;; --- RT4: same key across maps, non-keymap defs → replace map list --
  ;; Simulate a map boundary by clearing the dedup list between calls.
  ;; Neither cmd is a keymap, so C:8813 gives (cons new nil).
  (reset!)
  (process-menu-bar-item 'k4 (list 'menu-item "First"  'cmdA))
  (dedup-setter #nil)
  (process-menu-bar-item 'k4 (list 'menu-item "Second" 'cmdB))
  (let* ((v (vec-getter))
         (m (aref-f v MENU-BAR-ITEM-DEF)))
    (check "rt4-merge-index" 4    (idx-getter))
    (check "rt4-merge-car"   'cmdB (car-f m))
    (check "rt4-merge-cdr"   #nil  (cdr-f m)))

  ;; --- RT5: same key across maps, both keymap defs → chain --------------
  ;; Both DEFs are keymaps, so C:8813 gives (cons new old) — the old
  ;; map list is preserved and extended.
  (reset!)
  (let ((km1 (make-km))
        (km2 (make-km)))
    (process-menu-bar-item 'k5 (list 'menu-item "First"  km1))
    (dedup-setter #nil)
    (process-menu-bar-item 'k5 (list 'menu-item "Second" km2))
    (let* ((v (vec-getter))
           (m (aref-f v MENU-BAR-ITEM-DEF)))
      (check "rt5-chain-index" 4  (idx-getter))
      ;; m should be (km2 km1) — km2 consed onto the existing (km1) list.
      (check "rt5-chain-car"    km2  (car-f m))
      (check "rt5-chain-cadr"   km1  (car-f (cdr-f m)))
      (check "rt5-chain-cddr"   #nil (cdr-f (cdr-f m)))))

  ;; --- RT6: 'undefined splices out prior item -------------------------
  ;; Add two items, then a third call with def='undefined for the first
  ;; key.  The item shifts down; only the second item remains.
  (reset!)
  (process-menu-bar-item 'k6a (list 'menu-item "A" 'cmdA))
  (process-menu-bar-item 'k6b (list 'menu-item "B" 'cmdB))
  ;; Clear dedup so k6a can be re-processed with 'undefined.
  (dedup-setter #nil)
  (process-menu-bar-item 'k6a 'undefined)
  (let ((v (vec-getter)))
    (check "rt6-undef-index" 4 (idx-getter))
    ;; The surviving item (k6b) shifted from slots 4-7 down to 0-3.
    (check "rt6-undef-remaining-key"    'k6b  (aref-f v MENU-BAR-ITEM-KEY))
    (check "rt6-undef-remaining-string" "B"   (aref-f v MENU-BAR-ITEM-STRING))
    (check "rt6-undef-remaining-car"    'cmdB (car-f (aref-f v MENU-BAR-ITEM-DEF)))))

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
