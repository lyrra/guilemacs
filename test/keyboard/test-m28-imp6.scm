;;; test-m28-imp6.scm --- M28 imp-6: close-out.  Pin the M28 end state.
;;;
;;; brief.org (M28 imp-6) is the accounting/close-out step, not a port
;;; step.  This corpus pins the state the M28 reclaim cascade left
;;; behind at HEAD 9689988, so a later commit that regresses the sweep
;;; is caught here:
;;;
;;;   1. every DEFUN reclaimed during M28 reads back as nil (the C subr
;;;      is gone and nothing re-registers the name);
;;;   2. --kbd-empty-p (the one M28 addition) resolves;
;;;   3. a sample of the stay-C families still registers its shims;
;;;   4. the remnant line counts are printed -- not asserted -- because
;;;      they move with every later milestone.
;;;
;;; The reclaimed list is built from the M28 diff:
;;;   git diff 1eda15c~1..HEAD -- src/keyboard.c | grep '^-DEFUN'
;;; and cross-checked against the per-family corpora
;;; (test-m28-imp1.scm, test-m28-imp4.scm, test-m28-imp5*.scm).
;;; 46 = 3 imp-1 dispatchers + 30 imp-4 --rks- generics + 13 imp-5
;;; cascade reclaims.
;;;
;;; Same harness as test-m28-imp5-f6.scm: sourced by the .el wrapper
;;; via eval-scheme; accumulates (NAME STATUS) pairs into test-results.

(use-modules (ice-9 rdelim))
(use-modules (emacs elisp-ref))
(use-modules (emacs-elisp runtime))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (%sym name)
  (symbol-function name))

;;; --- 1. Every DEFUN reclaimed during M28 reads back as nil ------------
;;; A removed C DEFUN stops being registered, so symbol-function is nil.
;;; Readback uses (symbol-function 'name), not a bare elisp name: a bare
;;; elisp name is unbound as a Scheme identifier in (guile-user).
;;; See docs/arch.org §"scheme test corpora sourced via eval-scheme".
(define %reclaimed
  '(
    ;; imp-1 (1eda15c): 3 dispatcher DEFUNs, callers repointed.
    --tab-bar-enrich-position
    --menu-bar-touch-activate
    --mouse-click-menu-bar-intercept
    ;; imp-4 (faec86c..db8d423): --rks- generic prims (bucket-A DELETE).
    --rks-record-get
    --rks-record-get-int
    --rks-record-set
    --rks-record-set-int
    --rks-record-set-bool
    --rks-new-binding
    --set-rks-new-binding
    --rks-first-unbound
    --set-rks-first-unbound
    --rks-original-uppercase
    --rks-original-uppercase-position
    --set-rks-original-uppercase
    --set-rks-original-uppercase-position
    --rks-shift-translated-p
    --set-rks-shift-translated
    --rks-fkey-start
    --rks-fkey-end
    --rks-keytran-start
    --rks-keytran-end
    --rks-indec-start
    --rks-indec-end
    --set-rks-fkey-start
    --set-rks-fkey-end
    --set-rks-keytran-start
    --set-rks-keytran-end
    --set-rks-indec-start
    --set-rks-indec-end
    --rks-keyremaps-shrink-by
    --rks-reset-fkey-and-keytran-scans
    --rks-init-keyremaps
    ;; imp-5 family-1: the 5 --rc- forwarders the cascade reclaimed.
    --rc-show-help-echo
    --rc-record-char
    --rc-read-char-x-menu-prompt
    --rc-read-char-minibuf-menu-prompt
    --rc-swallow-events
    ;; imp-5 family-2: the --ie-kind-from-name double-hop.
    --ie-kind-from-name
    ;; imp-5 family-4: --timer-check.
    --timer-check
    ;; imp-5 family-5: the dead --button-down-location whole-vector pair.
    --button-down-location
    --set-button-down-location
    ;; imp-5 family-6 (the tail): 4 self-sufficient forwarders.
    --some-mouse-moved
    --record-recent-keys-cmd-pseudo-event
    --coords-in-menu-bar-window
    --line-number-mode-hscroll))

(for-each
 (lambda (name)
   (report (string-append "imp6/no-defun/" (symbol->string name))
           (if (eq? (%sym name) #nil)
               'PASS
               (list 'FAIL 'still-bound name))))
 %reclaimed)

;;; --- 2. --kbd-empty-p (the one M28 addition) resolves -----------------
;;; imp-3 added --kbd-empty-p (batched queue-empty test); it has Scheme
;;; callers in (emacs kbd-buffer), so it must stay a live subr.
(report "imp6/added/--kbd-empty-p"
        (if (procedure? (%sym '--kbd-empty-p))
            'PASS
            (list 'FAIL 'not-a-procedure (%sym '--kbd-empty-p))))

;;; --- 3. A sample of the stay-C families still registers its shims -----
;;; The reclaim sweep left the bulk of the shims C: they wrap raw C
;;; state (file statics, staticpro'd GC-root vectors, signal-context
;;; flag cells, C subroutines).  A stay-C DEFUN stays registered, so
;;; symbol-function is non-nil.  One name per family that stayed C.
(define %stay-c
  '("--buffer-beg"                 ; raw kboard buffer statics
    "--total-keys"                 ; C counter
    "--minibuf-level"              ; C static int
    "--lispy-function-keys"        ; staticpro'd vector
    "--user-signal-list"           ; signal-context cell
    "--input-blocked-p"            ; C subroutine-backed predicate
    "--menu-bar-touch-id"          ; menu/bar C cell (family 5)
    "--set-menu-bar-touch-id"
    "--button-down-location-aref"  ; C static aref path (family 5)
    "--button-down-location-aset"
    "--rks-key"                    ; --rks- fast-path family (stay C)
    "--set-rks-key"
    "--rks-state-stack-push"
    "--rks-t"
    "--this-single-command-key-start"      ; shortlist: live C caller
    "--set-this-single-command-key-start"
    "--adjust-point-for-property-cl1"))    ; shortlist: C-static read

(for-each
 (lambda (name)
   (let ((sym (intern name)))
     (report (string-append "imp6/stay-c/" name)
             (if (not (eq? (%sym sym) #nil))
                 'PASS
                 (list 'FAIL 'missing sym)))))
 %stay-c)

;;; --- 4. Print -- do not assert -- the current remnant line counts -----
;;; The counts move with every later milestone, so they are informational
;;; only.  Locate src/ from the test cwd: run-tests.sh runs from test/,
;;; run-all-tests.el from the repo root, so probe both.
(define (count-lines path)
  (call-with-input-file path
    (lambda (port)
      (let loop ((n 0))
        (let ((line (read-line port)))
          (if (eof-object? line) n (loop (+ n 1))))))))

(define (locate rel)
  (let loop ((bases (list (getcwd)
                          (string-append (getcwd) "/..")
                          (string-append (getcwd) "/../.."))))
    (if (null? bases)
        #f
        (let ((path (string-append (car bases) "/" rel)))
          (if (false-if-exception
               (call-with-input-file path (lambda (port) port)))
              path
              (loop (cdr bases)))))))

(define (note name text)
  (report (string-append "imp6/remnant/" name) (list 'INFO text)))

(let ((kc (locate "src/keyboard.c"))
      (kg (locate "src/keyboard-globals.c")))
  (define (emit label path)
    (note label (if path
                    (format #f "~a lines" (count-lines path))
                    "unavailable")))
  (emit "src/keyboard.c" kc)
  (emit "src/keyboard-globals.c" kg)
  (note "combined"
        (if (and kc kg)
            (format #f "~a lines" (+ (count-lines kc) (count-lines kg)))
            "unavailable")))
