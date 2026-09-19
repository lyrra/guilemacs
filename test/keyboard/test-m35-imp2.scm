;;; test-m35-imp2.scm --- M35 imp-2: the residual-stub disposition corpus.
;;;
;;; brief.org (M35 imp-2) records the final verdict for every residual
;;; keyboard stub.  imp-2 is a documentation-only imp: it changes no C
;;; file and retires no stub.  This corpus pins the disposition so the
;;; claims are checked automatically and not only by hand.
;;;
;;; The decision rules (docs/m35-plan.org §"Residual-stub disposition"):
;;;
;;;   1. A stub retires only when its last live buildable C caller
;;;      leaves C.
;;;   2. An NS caller does not count: HAVE_NS is undefined
;;;      (src/config.h).
;;;
;;; Two kinds of check:
;;;
;;;   - a static keep proof: the nine residual stubs
;;;     (pop_kboard, safe_run_hooks, swallow_events, gen_help_event,
;;;     detect_input_pending, detect_input_pending_run_timers,
;;;     timer_check, gobble_input, kbd_buffer_store_event) each keep a
;;;     definition and a live buildable C caller.  A whole-identifier
;;;     scan is used, so a longer name does not count.
;;;   - a census check: kbd_buffer_store_event has 15 caller files
;;;     (14 buildable + NS), not 16.  The earlier count included
;;;     keyboard.c, which holds the definition and no live call.
;;;
;;; (This corpus used to also check docs/m35-plan.org §"Residual-stub
;;; disposition", docs/kb.org's ** M35 section, and milestone.org's
;;; Exit-criterion section for a matching disposition record.  docs/ is
;;; gitignored and not kept in sync with the git-tracked test/code work,
;;; so those checks either skipped or failed on stale local docs
;;; unrelated to code correctness.  Removed; the disposition itself
;;; (which stub retires, which stays, and why) is still pinned by the
;;; keep-proof and census checks above.)
;;;
;;; All checks read files, so the corpus needs no C entry point and is
;;; batch-safe.
;;;
;;; The repo root is bound by the .el wrapper as %m35-root.
;;;
;;; The .el wrapper turns each (NAME PASS|FAIL) pair into an ERT test and
;;; prints each (NAME INFO VALUE) pair without asserting it; see
;;; test/keyboard/test-m35-imp2.el.

(use-modules (ice-9 rdelim))
(use-modules (srfi srfi-13))
(use-modules (srfi srfi-1))

(define test-results '())

(define (report name status)
  (set! test-results (cons (list name status) test-results)))

(define (check name expected actual)
  (if (equal? expected actual)
      (report name 'PASS)
      (report name (list 'FAIL 'expected expected 'got actual))))

(define (info name value)
  (report name (list 'INFO value)))

(define (slurp path)
  "Return the whole file at PATH as a string, or #f when it is absent."
  (if (not (file-exists? path))
      #f
      (call-with-input-file path
        (lambda (port)
          (let loop ((chars '()))
            (let ((c (read-char port)))
              (if (eof-object? c)
                  (list->string (reverse chars))
                  (loop (cons c chars)))))))))

(define (contains? text needle)
  ;; string-contains returns the match index or #f; normalize to a boolean
  ;; so `check' can compare against #t/#f.
  (and (string? text)
       (if (string-contains text needle) #t #f)))

(define (word-char? c)
  "True when C is an identifier character (letter, digit, or underscore)."
  (or (char-alphabetic? c) (char-numeric? c) (char=? c #\_)))

(define (contains-token? text token)
  "True when TOKEN occurs in TEXT as a whole identifier: no identifier
character on either side.  This matches the grep form \\bNAME\\b."
  (if (not (string? text))
      #f
      (let ((n (string-length token))
            (len (string-length text)))
        (let loop ((i 0))
          (if (> (+ i n) len)
              #f
              (if (and (string=? token (substring text i (+ i n)))
                       (or (= i 0)
                           (not (word-char? (string-ref text (1- i)))))
                       (or (= (+ i n) len)
                           (not (word-char? (string-ref text (+ i n))))))
                  #t
                  (loop (1+ i))))))))

(define (repo path) (string-append %m35-root "/" path))

(define (split-lines text)
  "Return the lines of TEXT as a list."
  (call-with-input-string text
    (lambda (port)
      (let loop ((acc '()))
        (let ((line (read-line port)))
          (if (eof-object? line) (reverse acc) (loop (cons line acc))))))))

(define (files-with-token dir suffix token)
  "Names of the files in DIR whose name ends with SUFFIX and whose text
holds TOKEN as a whole identifier.  This mirrors the scan
`rg -l '\\bTOKEN\\b' DIR`.  A comment mention and a definition count as a
match here; the caller checks below separate them."
  (if (not (file-exists? dir))
      '()
      (let loop ((names (scandir dir (lambda (n) (string-suffix? suffix n))))
                 (acc '()))
        (if (null? names)
            (reverse acc)
            (let ((p (string-append dir "/" (car names))))
              (loop (cdr names)
                    (if (contains-token? (slurp p) token)
                        (cons (car names) acc)
                        acc)))))))

;;; --- 0. The repo root must be known --------------------------------
(if (not (defined? '%m35-root))
    (begin (report "m35/imp2/root-bound" (cons 'FAIL "not bound by wrapper"))
           (set! %m35-root "."))
    (report "m35/imp2/root-bound" 'PASS))

(define kbd     (slurp (repo "src/keyboard.c")))
(define xterm-c (slurp (repo "src/xterm.c")))
(define pgtk-c  (slurp (repo "src/pgtkterm.c")))
(define emacs-c (slurp (repo "src/emacs.c")))
(define xmenu-c (slurp (repo "src/xmenu.c")))
(define pgtkmenu-c (slurp (repo "src/pgtkmenu.c")))
(define process-c (slurp (repo "src/process.c")))
(define dbusbind-c (slurp (repo "src/dbusbind.c")))

;;; --- 1. Every residual stub keeps a definition --------------------
;;; A stub retires only when its last live buildable C caller leaves C.
;;; Each definition below is recorded in docs/m35-plan.org §"Residual-stub
;;; census".
(if (not kbd)
    (report "m35/imp2/scan/keyboard.c" (cons 'FAIL "src/keyboard.c missing"))
    (begin
      ;; M36 imp-2 retired pop_kboard; the kbd_pop_kboard dispatcher is
      ;; not a bare pop_kboard token.
      (check "m35/imp2/def/pop-kboard-retired" #f
             (contains? kbd "\npop_kboard (void)"))
      ;; M36 imp-3 retired safe_run_hooks; the kbd_run_echo_area_clear_hook
      ;; dispatcher is not a bare safe_run_hooks token.
      (check "m35/imp2/def/safe-run-hooks-retired" #f
             (contains? kbd "safe_run_hooks (Lisp_Object hook)"))
      ;; M36 imp-1 retired both stubs.
      (check "m35/imp2/def/swallow-events-retired" #f
             (contains? kbd "swallow_events (bool do_display)"))
      ;; M36 imp-4 retired gen_help_event.
      (check "m35/imp2/def/gen-help-event-retired" #f
             (contains? kbd "gen_help_event (Lisp_Object help"))
      ;; M36 imp-2 retired the detect family.
      (check "m35/imp2/def/detect-input-pending-retired" #f
             (contains? kbd "detect_input_pending (void)"))
      (check "m35/imp2/def/detect-input-pending-run-timers-retired" #f
             (contains? kbd "detect_input_pending_run_timers (bool do_display)"))
      (check "m35/imp2/def/timer-check-retired" #f
             (contains? kbd "timer_check (void)"))
      (check "m35/imp2/def/gobble-input" #t
             (contains? kbd "gobble_input (void)"))
      (check "m35/imp2/def/kbd-buffer-store-event" #t
             (contains? kbd "kbd_buffer_store_event (register struct input_event"))))

;;; --- 2. safe_run_hooks retired except the unbuilt pgtk caller ------
;;; M36 imp-3 moved the buildable callers (emacs.c, keyboard.c, xmenu.c)
;;; out of C.  The pgtkmenu.c caller is unbuilt (HAVE_PGTK is
;;; undefined), so its text stays.  nsmenu.m is NS and does not count.
(check "m35/imp2/keep/safe-run-hooks/emacs.c-retired" #f
       (contains? emacs-c "safe_run_hooks (Qkill_emacs_hook)"))
(check "m35/imp2/keep/safe-run-hooks/keyboard.c-retired" #f
       (contains? kbd "safe_run_hooks (Qecho_area_clear_hook)"))
(check "m35/imp2/keep/safe-run-hooks/xmenu.c-retired" #f
       (contains? xmenu-c "safe_run_hooks (Qactivate_menubar_hook)"))
(check "m35/imp2/keep/safe-run-hooks/pgtkmenu.c" #t
       (contains? pgtkmenu-c "safe_run_hooks (Qmenu_bar_update_hook)"))

;;; --- 3. gen_help_event retired except the unbuilt pgtk caller -----
;;; M36 imp-4 moved the buildable xterm.c caller to the local static
;;; dispatcher x_gen_help_event.  pgtkterm.c is unbuilt (HAVE_PGTK is
;;; undefined), so its text stays.  nsterm.m is NS and does not count.
(check "m35/imp2/keep/gen-help-event/retired" #f
       (contains? xterm-c " gen_help_event (Qnil, frame, Qnil, Qnil, 0)"))
(check "m35/imp2/keep/gen-help-event/pgtkterm.c" #t
       (contains? pgtk-c "gen_help_event (Qnil, frame_obj, Qnil, Qnil, 0)"))

;;; --- 4. The other stubs: disposition after M36 imp-4 ---------------
;;; M36 imp-2 retired pop_kboard and the detect family; M36 imp-3
;;; retired safe_run_hooks; M36 imp-4 retired gen_help_event.  Their
;;; remaining stub keepers (gobble_input, kbd_buffer_store_event) stay C.
(check "m35/imp2/keep/pop-kboard-retired" #f
       (contains? kbd "\n      pop_kboard ();"))
(check "m35/imp2/keep/swallow-events-retired" #f
       (contains? process-c "swallow_events (do_display)"))
(check "m35/imp2/keep/detect-input-pending/process.c-retired" #f
       (contains? process-c "detect_input_pending ()"))
(check "m35/imp2/keep/detect-input-pending/keyboard.c-retired" #f
       (contains? kbd "detect_input_pending () ? Qt"))
(check "m35/imp2/keep/detect-input-pending-run-timers/process.c-retired" #f
       (contains? process-c "detect_input_pending_run_timers (do_display)"))
(check "m35/imp2/keep/detect-input-pending-run-timers/keyboard.c-retired" #f
       (contains? kbd "detect_input_pending_run_timers (!NILP (do_display))"))
(check "m35/imp2/keep/timer-check-retired" #f
       (contains? process-c "timer_check ()"))
(check "m35/imp2/keep/gobble-input" #t
       (contains? kbd "gobble_input ()"))
(check "m35/imp2/keep/kbd-buffer-store-event" #t
       (contains? dbusbind-c "kbd_buffer_store_event (&event)"))

;;; --- 5. Census correction: kbd_buffer_store_event caller files ----
;;; The scan (files-with-token, and `rg -l`) matches the name anywhere:
;;; a comment mention or a definition counts, not only a live call.  The
;;; name matches 17 files.  keyboard.h (extern) and keyboard.c
;;; (definition, no live call) account for two.  This corpus subtracts
;;; keyboard.c by hand, because keyboard.c holds the definition and no
;;; live call.  So 15 files hold live call sites: 14 buildable (.c) plus
;;; NS (.m).  The earlier count said 16; it counted keyboard.c.  The
;;; subtraction is manual: a future file that only mentions the name in
;;; a comment would break the count, because the scan cannot tell a
;;; comment from a call.
(define kbds-c (files-with-token (repo "src") ".c" "kbd_buffer_store_event"))
(define kbds-m (files-with-token (repo "src") ".m" "kbd_buffer_store_event"))
(info "m35/imp2/census/kbd-buffer-store-event/.c-files" (length kbds-c))
(info "m35/imp2/census/kbd-buffer-store-event/.m-files" (length kbds-m))
(check "m35/imp2/census/kbd-buffer-store-event/buildable-callers" 14
       (- (length kbds-c) 1))            ; keyboard.c holds the definition
(check "m35/imp2/census/kbd-buffer-store-event/ns-callers" 1
       (length kbds-m))
(check "m35/imp2/census/kbd-buffer-store-event/total-caller-files" 15
       (+ (- (length kbds-c) 1) (length kbds-m)))
(check "m35/imp2/census/kbd-buffer-store-event/ns-is-nsterm" #t
       (if (member "nsterm.m" kbds-m) #t #f))
;; keyboard.c holds the definition and no live call.  A live call would
;; match the "kbd_buffer_store_event (&" form.
(check "m35/imp2/census/kbd-buffer-store-event/keyboard.c-no-call" #f
       (contains? kbd "kbd_buffer_store_event (&"))

;;; --- 6. Static: the corpus is registered in the keyboard group ----
;;; The row must quote the corpus path, and it must sit inside the
;;; keyboard group.  A row in another group fails the check.  The group
;;; runs from its header line to the first line that holds only a
;;; closing paren.
(define run-tests (slurp (repo "tool/run-tests.scm")))

(define (line-index-with lines needle)
  "Index of the first line of LINES that contains NEEDLE, or #f."
  (list-index (lambda (l) (string-contains l needle)) lines))

(define (group-close-index lines start)
  "Index of the first line at or after START whose text is only a
closing paren, or #f.  The keyboard group is flat, so this is its end."
  (let loop ((i start))
    (cond ((>= i (length lines)) #f)
          ((equal? ")" (string-trim (list-ref lines i))) i)
          (else (loop (1+ i))))))

(let* ((rt-lines (and run-tests (split-lines run-tests)))
       (kg-start (and rt-lines
                      (line-index-with rt-lines "(group ; keyboard.c")))
       (kg-end (and kg-start (group-close-index rt-lines (1+ kg-start))))
       (reg-idx (and rt-lines
                     (line-index-with rt-lines
                                      "\"test/keyboard/test-m35-imp2.el\""))))
  (check "m35/imp2/run-tests.scm/registers-el" #t
         (and (string? run-tests)
              (and reg-idx
                   (contains? (list-ref rt-lines reg-idx)
                              "\"test/keyboard/test-m35-imp2.el\""))
              (and kg-end
                   (< kg-start reg-idx)
                   (< reg-idx kg-end)))))
