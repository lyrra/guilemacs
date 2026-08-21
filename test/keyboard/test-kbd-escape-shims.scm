;;; test-kbd-escape-shims.scm --- M11 imp-1.3 test corpus for the
;;; kbd-buffer C-escape shims
;;;
;;; Sourced by test/keyboard/test-kbd-escape-shims.el via eval-scheme.
;;; Accumulates PASS/FAIL entries into `test-results` for readback
;;; from elisp — Scheme format output does not reach emacs --batch
;;; stdout.
;;;
;;; Scope: thin-wrapper shape checks only (return shapes, no signal
;;; on the happy path).  Wait-loop / dispatch semantics are imp-2/3/4
;;; territory and are NOT exercised here; in particular the 4-arg
;;; --wait-reading-process-output is only tested with a small NSEC
;;; (no long sleeps in CI), and --quit-throw-to-read-char is only
;;; checked for registration (it longjmps to the wait point and
;;; must never be called from a test).

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (%sym name)
  (symbol-function name))

;;; --- Registration ---------------------------------------------------
;;; All 14 shims must be registered as DEFUNs (syms_of_keyboard).

(define shim-names
  '(--quit-throw-to-read-char
    --wait-reading-process-output
    --activate-menubar-hook
    --kbd-decode-multibyte-string
    --kbd-noninteractive-getchar
    --mouse-position-hook
    --detect-conversion-events
    --handle-pending-conversion-events
    --conversion-disabled-p
    --unhold-keyboard-input
    --kbd-on-hold-p
    --x-detect-pending-selection-requests
    --x-handle-pending-selection-requests
    --gobble-input))

(for-each (lambda (n)
            (check (string-append "registered:" (symbol->string n)) #t
                   (not (eq? (%sym n) #nil))))
          shim-names)

;;; --- Pure pass-through shims ----------------------------------------

;; --gobble-input: fixnum (events read, or -1 when blocked).
(let ((r ((%sym '--gobble-input))))
  (check "gobble-input-fixnum" #t (integer? r)))

;; --kbd-on-hold-p: t/nil, no signal.
(let ((r ((%sym '--kbd-on-hold-p))))
  (check "kbd-on-hold-p-shape" #t
         (or (eq? r #t) (eq? r #nil))))

;; --unhold-keyboard-input: nil.
(check "unhold-keyboard-input-nil" #nil
       ((%sym '--unhold-keyboard-input)))

;; --quit-throw-to-read-char: never called here (longjmp); the
;; registration check above covers its existence.

;; --kbd-noninteractive-getchar: fixnum (EOF ⇒ -1 when stdin is
;; closed in batch — the raw-int contract), or nil on builds compiled
;; with DBus / file-notify / threads (no fast path; see the DEFUN
;; docstring).
(let ((r ((%sym '--kbd-noninteractive-getchar))))
  (check "kbd-noninteractive-getchar-shape" #t
         (or (integer? r) (eq? r #nil))))

;;; --- Predicates / platform-gated -------------------------------------

;; Text-conversion trio: t/nil shapes, never signal; nil on builds
;; without HAVE_TEXT_CONVERSION (termcap batch build).
(let ((r ((%sym '--detect-conversion-events))))
  (check "detect-conversion-events-shape" #t
         (or (eq? r #t) (eq? r #nil))))
(check "handle-pending-conversion-events-nil" #nil
       ((%sym '--handle-pending-conversion-events)))
(let ((r ((%sym '--conversion-disabled-p))))
  (check "conversion-disabled-p-shape" #t
         (or (eq? r #t) (eq? r #nil))))

;; X selection-request pair: nil on non-X builds, t/nil on X.
(let ((r ((%sym '--x-detect-pending-selection-requests))))
  (check "x-detect-pending-selection-requests-shape" #t
         (or (eq? r #t) (eq? r #nil))))
(check "x-handle-pending-selection-requests-nil" #nil
       ((%sym '--x-handle-pending-selection-requests)))

;;; --- Hook shims -------------------------------------------------------

;; --activate-menubar-hook on the live selected frame: nil (termcap
;; builds have no activate_menubar_hook).
(check "activate-menubar-hook-selected-frame" #nil
       ((%sym '--activate-menubar-hook) ((%sym 'selected-frame))))

;; --mouse-position-hook on the live selected frame: nil (termcap:
;; hook NULL) or a 6-element list (window-system builds) — imp-4
;; extended the shape to (F BAR-WINDOW PART X Y T).
(let ((r ((%sym '--mouse-position-hook) ((%sym 'selected-frame)))))
  (check "mouse-position-hook-shape" #t
         (or (eq? r #nil)
             (and (list? r) (= 6 (length r))))))

;;; --- --wait-reading-process-output ------------------------------------

;; Small NSEC sleep only (1 ms) — no long timeouts in CI.  Nil return.
(check "wait-reading-process-output-nil" #nil
       ((%sym '--wait-reading-process-output) 0 1000000 -1 0))

;; Non-fixnum SEC/NSEC/READ-KBD must signal wrong-type-argument
;; (CHECK_FIXNUM), not silently UB.
(check "wait-reading-process-output-typecheck" #t
       (catch #t
         (lambda ()
           ((%sym '--wait-reading-process-output) "sec" 0 -1 0)
           #f)
         (lambda (k . args) #t)))

;;; --- --kbd-decode-multibyte-string ------------------------------------

;; Multibyte string → nil or decoded string; must not abort.
(let ((r ((%sym '--kbd-decode-multibyte-string)
          ((%sym 'string-make-multibyte) "héllo"))))
  (check "kbd-decode-multibyte-string-shape" #t
         (or (eq? r #nil) (string? r))))
