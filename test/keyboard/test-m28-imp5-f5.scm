;;; test-m28-imp5-f5.scm --- M28 imp-5, family 5: reclaim the dead
;;; --button-down-location pair; --menu- / --x- / --tool- / --tab- /
;;; --button- stay-C audit.
;;;
;;; brief.org (M28 imp-5 family 5) walks the 33 family-5 DEFUNs
;;; (read side 23: --menu- 9, --x- 4, --tool- 3, --tab- 3, --button- 4;
;;; plus 10 --set-* write companions).  Exactly two are reclaimable, on
;;; the zero-caller rule:
;;;
;;;   --button-down-location      (whole-vector getter)
;;;   --set-button-down-location  (whole-vector setter)
;;;
;;; =grep -rn 'button-down-location' src mod test= finds no user of the
;;; whole-vector getter or setter: mod/emacs/lispy-event.scm reaches the
;;; C static button_down_location only through
;;; %--button-down-location-aref / -aset /
;;; %--ensure-button-down-location-size.  So both DEFUNs are deleted; the
;;; C static and its aref/aset/ensure-size path stay.
;;;
;;; The other 31 shims read or write raw C state (the x_y_to_hpos_vpos /
;;; pixel_to_glyph_coords geometry subroutines, the xterm.c
;;; selection-request subroutines, x_popup_menu_1,
;;; menu_item_eval_property, the staticpro'd menu/tab/tool items vectors,
;;; and the menu_bar_touch_id / button_down_time / button_down_location
;;; cells), so they stay C.  Decisions and reasons: docs/kb.org "M28
;;; imp-5 family-5 --menu- / --x- / --tool- / --tab- / --button- decision
;;; audit".
;;;
;;; This corpus pins both sides of that decision:
;;;
;;;   - the two deleted DEFUNs read back as nil (C subr gone);
;;;   - the retained aref / aset / ensure-size path still works;
;;;   - (emacs lispy-event) still binds the aref/aset aliases and does
;;;     not bind a whole-vector getter;
;;;   - the 31 stay-C shims still register (symbol-function non-nil).
;;;
;;; Same harness as test-m28-imp5-f4.scm: Sourced by the .el wrapper via
;;; eval-scheme; accumulates (NAME STATUS) pairs into test-results.

(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (%sym name)
  (symbol-function name))

(define (no-error? thunk)
  (catch #t
    (lambda () (thunk) #t)
    (lambda (key . args) (list 'error key args))))

;;; --- 1. The two reclaimed DEFUNs are gone ----------------------------
;;; A removed C DEFUN stops being registered, so symbol-function is nil
;;; (mirrors test-m28-imp5-f4.scm §1).
(report "imp5/f5/no-defun/--button-down-location"
        (if (eq? (%sym '--button-down-location) #nil)
            'PASS
            (list 'FAIL 'still-bound '--button-down-location)))
(report "imp5/f5/no-defun/--set-button-down-location"
        (if (eq? (%sym '--set-button-down-location) #nil)
            'PASS
            (list 'FAIL 'still-bound '--set-button-down-location)))

;;; --- 2. The retained aref / aset / ensure-size path still works ------
;;; The C static button_down_location (and its 5-slot init) stays; only
;;; the whole-vector getter/setter went.  The three retained DEFUNs must
;;; resolve, grow the vector, and round-trip a value through a grown slot.
(let ((ensure (%sym '--ensure-button-down-location-size))
      (aref   (%sym '--button-down-location-aref))
      (aset   (%sym '--button-down-location-aset)))
  (report "imp5/f5/button/stay-c-path-present"
          (if (and (procedure? ensure) (procedure? aref) (procedure? aset))
              'PASS
              (list 'FAIL 'missing-procedure
                    'ensure (procedure? ensure)
                    'aref (procedure? aref)
                    'aset (procedure? aset))))
  ;; Grow by ONE slot past the default 5 (index 5): the vector is a
  ;; shared C static and larger_vector can only grow, so the size change
  ;; is permanent — there is no shrink accessor (the whole-vector setter
  ;; was reclaimed).  Index 5 is the first slot above the 0..4 range
  ;; mouse bookkeeping uses, so the growth does not disturb other
  ;; corpora.  The new slot reads back nil.
  (no-error? (lambda () (ensure 5)))
  (report "imp5/f5/button/ensure-grow-aref-nil"
          (let ((r (no-error? (lambda () (aref 5)))))
            (if (eq? r #t)
                (if (eq? (aref 5) #nil)
                    'PASS
                    (list 'FAIL 'expected #nil 'got (aref 5)))
                (list 'FAIL 'errored r))))
  ;; ASET then AREF round-trips a value through the same slot.
  (report "imp5/f5/button/aset-aref-roundtrip"
          (let ((r (no-error? (lambda () (aset 5 42)))))
            (if (eq? r #t)
                (if (eq? (aref 5) 42)
                    'PASS
                    (list 'FAIL 'expected 42 'got (aref 5)))
                (list 'FAIL 'errored r))))
  ;; Restore the slot value; the vector size (6) stays — see the note
  ;; above.  The value is what other corpora could observe, not the size.
  (no-error? (lambda () (aset 5 #nil))))

;;; --- 3. (emacs lispy-event) still binds the retained aliases ---------
;;; The module must load, keep the aref/aset aliases the reclaim left in
;;; place, and must NOT bind a whole-vector getter alias.
(define ev (false-if-exception (resolve-module '(emacs lispy-event) #:ensure #t)))
(if ev
    (begin
      (report "imp5/f5/module/lispy-event/loadable" 'PASS)
      (report "imp5/f5/module/lispy-event/binds-aref"
              (if (module-variable ev '%--button-down-location-aref)
                  'PASS
                  (list 'FAIL 'missing '%--button-down-location-aref)))
      (report "imp5/f5/module/lispy-event/binds-aset"
              (if (module-variable ev '%--button-down-location-aset)
                  'PASS
                  (list 'FAIL 'missing '%--button-down-location-aset)))
      (report "imp5/f5/module/lispy-event/no-whole-vector-getter"
              (if (module-variable ev '%--button-down-location)
                  (list 'FAIL 'still-bound '%--button-down-location)
                  'PASS)))
    (report "imp5/f5/module/lispy-event/loadable"
            (list 'FAIL 'not-loadable '(emacs lispy-event))))

;;; --- 4. All 31 stay-C shims still register ---------------------------
;;; A stay-C DEFUN stays registered, so symbol-function is non-nil.
(define %stay-c
  '("--menu-bar-hpos-vpos"
    "--menu-bar-hpos-vpos-raw"
    "--menu-pixel-to-glyph-coords"
    "--menu-bar-touch-id"
    "--set-menu-bar-touch-id"
    "--menu-bar-touch-consume-p"
    "--menu-bar-items-vector"
    "--set-menu-bar-items-vector"
    "--menu-bar-items-index"
    "--set-menu-bar-items-index"
    "--menu-bar-one-keymap-changed-items"
    "--set-menu-bar-one-keymap-changed-items"
    "--menu-item-eval-property"
    "--x-detect-pending-selection-requests"
    "--x-handle-pending-selection-requests"
    "--x-popup-menu-1"
    "--x-display-forces-interrupt-p"
    "--tool-bar-items-vector"
    "--set-tool-bar-items-vector"
    "--tool-bar-item-properties-vector"
    "--tool-bar-items-count"
    "--set-tool-bar-items-count"
    "--tab-bar-items-vector"
    "--set-tab-bar-items-vector"
    "--tab-bar-item-properties-vector"
    "--tab-bar-items-count"
    "--set-tab-bar-items-count"
    "--button-down-time"
    "--set-button-down-time"
    "--button-down-location-aref"
    "--button-down-location-aset"))

(for-each
 (lambda (name)
   (let ((sym (intern name)))
     (report (string-append "imp5/f5/stay-c/" name)
             (if (not (eq? (%sym sym) #nil))
                 'PASS
                 (list 'FAIL 'missing sym)))))
 %stay-c)
