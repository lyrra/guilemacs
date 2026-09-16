;;; test-m38-imp3-reset.el --- M38 imp-3 shared input-state reset.
;;;
;;; brief.org (M38 imp-3, defect D3): the keyboard corpora run in ONE
;;; emacs process (tool/run-tests.scm:12), so an input-state name a
;;; corpus writes stays written for every corpus that follows.  The
;;; writer map of brief.org §5.1 names the leaking corpora.
;;;
;;; This file is the ONE shared helper of brief.org §8.2.  It clears
;;; each leaked name back to the C/Scheme DEFAULT of §5.4.  It does NOT
;;; restore a pre-corpus snapshot: a snapshot keeps the leak alive.
;;;
;;; The writer corpora call it from unwind-protect, so the clear runs
;;; on the normal and on the non-local exit path (§8.1).
;;;
;;; The name list is the single source of truth.  test/keyboard/
;;; test-m38-imp3.scm reads this file and checks each writer restores
;;; exactly the names of §5.1 (drift guard).  A copied helper cannot
;;; drift from this list without failing that check (review F2 of
;;; cr-m38-imp2-response.org).

(provide 'm38-imp3-reset)

;;; The input-state names the helper clears, with their §5.4 origin:
;;;   last-input-event          C  src/keyboard-globals.c:64
;;;   last-nonmenu-event        C  src/keyboard-globals.c:58
;;;   last-event-frame          C  src/keyboard-globals.c:333
;;;   deactivate-mark           C  src/keyboard-globals.c:127 (buffer-local)
;;;   last-event-device         Scheme mod/emacs/command-loop.scm:1219
;;;   num-nonmacro-input-events Scheme mod/emacs/command-loop.scm:1234
(defconst m38-imp3-reset-names
  '(last-input-event last-nonmenu-event last-event-frame
    deactivate-mark last-event-device num-nonmacro-input-events)
  "Input-state names the M38 imp-3 helper clears (brief.org §5.4).")

(defun m38-imp3-reset-input-state (&optional buf)
  "Restore the input-state names to their defaults (brief.org §5.4).
Reset BUF (the buffer current when the corpus started), or the current
buffer, because `deactivate-mark' is buffer-local (§8.4 item 4).  Run
the defaults through eval-scheme so the two relocated names use the
(emacs command-loop) defaults, not a C cell."
  (let ((b (if (bufferp buf) buf (current-buffer))))
    (with-current-buffer b
      (eval-scheme
       "(begin
          (set-symbol-value! 'last-input-event #nil)
          (set-symbol-value! 'last-nonmenu-event #nil)
          (set-symbol-value! 'last-event-frame #nil)
          (set-symbol-value! 'deactivate-mark #nil)
          (set-symbol-value! 'last-event-device #nil)
          (set-symbol-value! 'num-nonmacro-input-events 0))"))))
