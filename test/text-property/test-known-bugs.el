;;; test-known-bugs.el --- Tests for known text property bugs (XFAIL)
;;;
;;; These tests document known bugs in the text property system.
;;; They are marked as expected failures (XFAIL) so the test suite
;;; passes while documenting the bugs exist.
;;;
;;; When a bug is fixed, the test will report XPASS (unexpected pass).
;;; At that point, remove the test-expect-fail and update BUGS-DISCOVERED.md.

(test-begin "known-bugs")

;;; ============================================================
;;; Bug #1: remove-text-properties Loop Bug
;;;
;;; When remove-text-properties is called in a loop to process
;;; multiple regions, the FIRST region's properties are not removed.
;;; Subsequent regions work correctly.
;;;
;;; See BUGS-DISCOVERED.md for full details.
;;; ============================================================

(test-expect-fail 1)
(with-temp-buffer
  (insert "text1 text2")
  (put-text-property 1 6 'face 'bold)
  (put-text-property 1 6 'invisible t)
  (put-text-property 7 12 'face 'bold)
  (put-text-property 7 12 'invisible t)

  ;; Remove invisible from all bold text regions via loop
  (let ((pos 1))
    (while (setq pos (text-property-any pos (point-max) 'face 'bold (current-buffer)))
      (let ((start pos)
            (end pos))
        (while (and (< end (point-max))
                   (eq (get-text-property end 'face) 'bold))
          (setq end (1+ end)))
        (remove-text-properties start end '(invisible nil) (current-buffer))
        (setq pos end))))

  ;; First region should have invisible removed (BUG: it doesn't)
  (test-nil "known-bugs/remove-props-loop-first-region"
            (get-text-property 2 'invisible)))

;; Verify second region DOES work (not an XFAIL)
(with-temp-buffer
  (insert "text1 text2")
  (put-text-property 1 6 'face 'bold)
  (put-text-property 1 6 'invisible t)
  (put-text-property 7 12 'face 'bold)
  (put-text-property 7 12 'invisible t)

  (let ((pos 1))
    (while (setq pos (text-property-any pos (point-max) 'face 'bold (current-buffer)))
      (let ((start pos)
            (end pos))
        (while (and (< end (point-max))
                   (eq (get-text-property end 'face) 'bold))
          (setq end (1+ end)))
        (remove-text-properties start end '(invisible nil) (current-buffer))
        (setq pos end))))

  ;; Second region works correctly
  (test-nil "known-bugs/remove-props-loop-second-region-ok"
            (get-text-property 8 'invisible)))

;;; ============================================================
;;; Bug #2: set-text-properties Loop Bug
;;;
;;; When set-text-properties is called in a loop to process
;;; multiple regions, the FIRST region's properties are not set.
;;; Subsequent regions work correctly.
;;;
;;; See BUGS-DISCOVERED.md for full details.
;;; ============================================================

(test-expect-fail 1)
(with-temp-buffer
  (insert "bold1 bold2")
  (put-text-property 1 6 'face 'bold)
  (put-text-property 7 12 'face 'bold)

  ;; Replace all bold with italic via loop
  (let ((pos 1))
    (while (setq pos (text-property-any pos (point-max) 'face 'bold (current-buffer)))
      (let ((start pos)
            (end pos))
        (while (and (< end (point-max))
                   (eq (get-text-property end 'face) 'bold))
          (setq end (1+ end)))
        (set-text-properties start end '(face italic) (current-buffer))
        (setq pos end))))

  ;; First region should be italic (BUG: it stays bold)
  (test-eq "known-bugs/set-props-loop-first-region"
           'italic (get-text-property 2 'face)))

;; Verify second region DOES work (not an XFAIL)
(with-temp-buffer
  (insert "bold1 bold2")
  (put-text-property 1 6 'face 'bold)
  (put-text-property 7 12 'face 'bold)

  (let ((pos 1))
    (while (setq pos (text-property-any pos (point-max) 'face 'bold (current-buffer)))
      (let ((start pos)
            (end pos))
        (while (and (< end (point-max))
                   (eq (get-text-property end 'face) 'bold))
          (setq end (1+ end)))
        (set-text-properties start end '(face italic) (current-buffer))
        (setq pos end))))

  ;; Second region works correctly
  (test-eq "known-bugs/set-props-loop-second-region-ok"
           'italic (get-text-property 8 'face)))

;;; ============================================================
;;; Bug #4: Buffer Insertion Property Loss - NOW FIXED!
;;;
;;; This bug was about properties being lost after insertion point.
;;; It has been fixed! Including this test without XFAIL to verify
;;; the fix holds.
;;; ============================================================

(with-temp-buffer
  (insert (propertize "AAAAAA" 'face 'bold))
  (goto-char 4)
  (insert "XX")
  ;; After inserting XX at position 4:
  ;; - Positions 1-3: original "AAA" - should be bold
  ;; - Positions 4-5: inserted "XX" - inherits bold
  ;; - Positions 6-8: shifted "AAA" - should be bold
  (test-eq "known-bugs/insert-preserves-after-fixed-start"
           'bold (get-text-property 1 'face))
  (test-eq "known-bugs/insert-preserves-after-fixed-end"
           'bold (get-text-property 7 'face)))

(test-end)
