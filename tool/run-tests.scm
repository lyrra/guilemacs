;; todo:
;; - unique names for generated tests
;; - --filter flag

(use-modules (ice-9 match)
             (ice-9 format)
             (ice-9 popen)
             (ice-9 regex)
             (srfi srfi-1)
             (rnrs io ports)
             (utils))
; accumulate all testfiles and run them in a single guile-emacs program
;
; by stating the word RUN on a single line, all
; accumulated test files so far will be run,
; this is useful if tests needs to be run isolated
;
; if you are debugging and need to quit early, state DONE
; on a single line
;
; try to sort the test from most primordial elisp functionallity
; towards more complex elisp applications

(define %tests '(
(group (prelude)
  ;; emacs-elisp -- core language
  "test/pre/parse.scm"
  "test/pre/dynamic-binding.scm"
  "test/pre/forwarded-binding.scm"
  "test/pre/condition-case.scm"
  "test/pre/handler-bind.scm"
  "test/pre/bindings.scm"
  "test/pre/complex-binding.scm"
  "test/pre/specpdl-introspection.scm"
  "test/pre/eq.scm"
  "test/pre/arith.scm"
  "test/pre/value-cmp.scm"
  "test/pre/bignum.scm"
  "test/pre/bitwise.scm"
  "test/pre/fixnum.scm"
  "test/pre/float.scm"
  "test/pre/string2.scm"
  "test/pre/reader-integers.scm"
  "test/pre/reader-utf8.scm"
  "test/pre/list.scm"
  "test/pre/predicate-simple.scm"
  "test/pre/predicate-comprehensive.scm"
  "test/pre/stringp.scm"
  "test/pre/string-funs.scm"
  "test/pre/natnump.scm"
  "test/pre/record.scm"
  "test/pre/integer-or-marker-p.scm"
  "test/pre/number-or-marker-p.scm"
  "test/pre/eval.scm"
  "test/pre/fns.scm"
  "test/pre/random.scm"
  "test/pre/time.scm"
  "test/pre/buffer-basic.scm"
  "test/pre/buffer-string.scm"
  "test/pre/clear-string.scm"
  "test/pre/string-match-utf8.scm"
  "test/pre/string-cache-debug.scm"
  "test/pre/string-length-bytes-match.scm"
  "test/pre/ensure-empty-lines-arithmetic.scm"
  "test/pre/string-print-utf8.scm"
  "test/pre/string-char.scm"
  "test/pre/text-property-navigation.scm"
  ;; emacs -- as an editor
  "test/pre/miscvar.scm"
  ;; uncategorized LLM generated tests
  "test/pre/bitwise-comprehensive.scm"
  "test/pre/core-comprehensive.scm"
  "test/pre/float-comprehensive.scm"
  "test/pre/type-predicates.scm"
  "test/pre/ie-fields.scm"
  )
(group ; keyboard.c → Guile port (see docs/keyboard.org)
  "test/keyboard/ertest-stub.el"            ; M0
  "test/keyboard/ertest-event-modifiers.el" ; M1
  "test/keyboard/ertest-kboard.el"          ; M2
  "test/keyboard/ertest-recent-keys.el"     ; M3
  "test/keyboard/ertest-recursive-edit.el"  ; M4
  "test/keyboard/ertest-this-command-keys.el" ; M5
  "test/keyboard/ertest-consolidation.el"   ; Consolidation
  "test/keyboard/ertest-command-loop.el"    ; M7a
  "test/keyboard/ertest-read-key-sequence.el" ; M6a
  "test/keyboard/ertest-read-char.el"         ; M8a
  "test/keyboard/test-kbd-escape-shims.el"    ; M11 imp-1.3 (corpus prints PASS/FAIL)
  "test/keyboard/test-kbd-wait-loop.el"       ; M11 imp-2 (corpus prints PASS/FAIL)
  "test/keyboard/test-kbd-dispatch.el"        ; M11 imp-3 (corpus prints PASS/FAIL)
  "test/keyboard/test-kbd-mouse-motion.el"    ; M11 imp-4 (corpus prints PASS/FAIL)
  "test/keyboard/test-m12-shims.el"           ; M12 imp-1 (corpus prints PASS/FAIL)
  "test/keyboard/test-main-queue.el"          ; M12 imp-3 (corpus prints PASS/FAIL)
  "test/keyboard/test-m13-shims.el"           ; M13 imp-1 (corpus prints PASS/FAIL)
  "test/keyboard/test-m13-store.el"           ; M13 imp-2 (corpus prints PASS/FAIL)
  "test/keyboard/test-m14-shims.el"           ; M14 imp-1 (corpus prints PASS/FAIL)
  "test/keyboard/test-m14-bodies.el"          ; M14 imp-2 (corpus prints PASS/FAIL)
  "test/keyboard/test-m14-predicates.el"      ; M14 imp-4 (corpus prints PASS/FAIL)
  "test/keyboard/test-m15-shims.el"           ; M15 imp-1 (corpus prints PASS/FAIL)
  "test/keyboard/test-m15-bodies.el"          ; M15 imp-2 (corpus prints PASS/FAIL)
  "test/keyboard/test-m15-timers.el"          ; M15 imp-4 (corpus prints PASS/FAIL)
  "test/keyboard/test-m16-shims.el"           ; M16 imp-1 (corpus prints PASS/FAIL)
  "test/keyboard/test-m16-bodies.el"          ; M16 imp-2 (corpus prints PASS/FAIL)
  "test/keyboard/test-m16-help-echo.el"       ; M16 imp-3 (corpus prints PASS/FAIL)
  "test/keyboard/test-m17-shims.el"           ; M17 imp-1 (corpus prints PASS/FAIL)
  "test/keyboard/test-m17-bodies.el"          ; M17 imp-2 (corpus prints PASS/FAIL)
  "test/keyboard/test-m17-record-char.el"     ; M17 imp-3 (corpus prints PASS/FAIL)
  "test/keyboard/test-m18-shims.el"           ; M18 imp-1 (corpus prints PASS/FAIL)
  "test/keyboard/test-m18-bodies.el"          ; M18 imp-2 (corpus prints PASS/FAIL)
  "test/keyboard/test-m18-echo.el"            ; M18 imp-3 (corpus prints PASS/FAIL)
  "test/keyboard/test-m19-bodies.el"          ; M19 imp-1 (corpus prints PASS/FAIL)
  "test/keyboard/test-m19-fixes.el"           ; M19 cr.org findings (corpus prints PASS/FAIL)
  "test/keyboard/test-m19-shims.el"           ; M19 imp-2 (corpus prints PASS/FAIL)
  "test/keyboard/test-m19-kind.el"            ; M19 imp-3 (corpus prints PASS/FAIL)
  "test/keyboard/test-m19-tables.el"          ; M19 imp-4 (corpus prints PASS/FAIL)
  "test/keyboard/test-m20-menu-prompt.el"     ; M20 imp-1 + imp-2 (corpus prints PASS/FAIL)
  "test/keyboard/test-m21-read-key-sequence.el" ; M21 imp-1 + imp-2 + imp-3 (corpus prints PASS/FAIL)
  "test/keyboard/test-m22-input-pending.el"     ; M22 imp-1 (corpus prints PASS/FAIL)
  "test/keyboard/test-m22-recursive-edit.el"    ; M22 imp-2 (corpus prints PASS/FAIL)
  "test/keyboard/test-m22-imp3.el"               ; M22 imp-3 (corpus prints PASS/FAIL)
  "test/keyboard/test-m22-imp4.el"               ; M22 imp-4 (corpus prints PASS/FAIL)
  "test/keyboard/test-m23-imp1.el"               ; M23 imp-1 (corpus prints PASS/FAIL)
  "test/keyboard/test-m23-imp2.el"               ; M23 imp-2 (corpus prints PASS/FAIL)
  "test/keyboard/test-m23-imp3.el"               ; M23 imp-3 (corpus prints PASS/FAIL)
  "test/keyboard/test-m23-imp4.el"               ; M23 imp-4 (corpus prints PASS/FAIL)
  "test/keyboard/test-m23-imp5.el"               ; M23 imp-5 (corpus prints PASS/FAIL)
  "test/keyboard/test-m24-input-poll.el"         ; M24 polling policy (corpus prints PASS/FAIL)
  "test/keyboard/test-m25-imp1-user-signal.el"
  "test/keyboard/test-m25-imp2-async-input.el"
  "test/keyboard/test-m25-imp3-gobble-input.el"
  "test/keyboard/test-m25-imp4-tty-read.el"
  "test/keyboard/test-m26-imp1-suspend-emacs.el"
  "test/keyboard/test-m26-imp2-quit-throw.el"
  "test/keyboard/test-m26-imp3-handle-interrupt.el"
  "test/keyboard/test-m27-single-kboard.el"   ; M27 imp-1 single-kboard (corpus prints PASS/FAIL)
  "test/keyboard/test-m27-kboard-lifecycle.el" ; M27 imp-2 kboard lifecycle (corpus prints PASS/FAIL)
  "test/keyboard/test-m27-init-keyboard.el"    ; M27 imp-3 init_keyboard resets (corpus prints PASS/FAIL)
  "test/keyboard/test-m27-ring-storage.el"     ; M27 imp-4 ring storage store->get->dispatch (corpus prints PASS/FAIL)
  "test/keyboard/test-m28-imp1.el"              ; M28 imp-1 reclaim 5 residual M8/M10 shims (corpus prints PASS/FAIL)
  "test/keyboard/test-m28-imp3.el"              ; M28 imp-3 --kbd-empty-p batch + wait-path cut-over (corpus prints PASS/FAIL)
  "test/keyboard/test-m28-imp4.el"              ; M28 imp-4 Step 1 record-primitive port (corpus prints PASS/FAIL)
  "test/keyboard/test-m28-imp5.el"              ; M28 imp-5 family 2 --ie-kind-from-name reclaim (corpus prints PASS/FAIL)
  "test/keyboard/test-m28-imp5-f3.el"           ; M28 imp-5 family 3 --frame- / --window- stay-C audit (corpus prints PASS/FAIL)
  "test/keyboard/test-m28-imp5-f4.el"           ; M28 imp-5 family 4 --timer-check reclaim + --tty-/--timer-/--read-/--reset- audit (corpus prints PASS/FAIL)
  "test/keyboard/test-m28-imp5-f5.el"           ; M28 imp-5 family 5 --button-down-location pair reclaim + --menu-/--x-/--tool-/--tab-/--button- audit (corpus prints PASS/FAIL)
  "test/keyboard/test-m28-imp5-f6.el"           ; M28 imp-5 family 6 (the tail) forwarder reclaim + stay-C audit (corpus prints PASS/FAIL)
  "test/keyboard/test-m28-imp6.el"              ; M28 imp-6 close-out — pin the reclaimed end state (corpus prints PASS/FAIL)
  "test/keyboard/test-m30-imp1.el"              ; M30 imp-1 table + --cell-ref / --cell-set! proof (corpus prints PASS/FAIL)
  "test/keyboard/test-m30-imp2.el"              ; M30 imp-2 plain bool cell conversion proof (corpus prints PASS/FAIL)
  "test/keyboard/test-m30-imp3.el"              ; M30 imp-3 plain fixnum cell conversion proof (corpus prints PASS/FAIL)
  "test/keyboard/test-m30-imp4.el"              ; M30 imp-4 Lisp_Object cell conversion proof (corpus prints PASS/FAIL)
  "test/keyboard/test-m30-imp5.el"              ; M30 imp-5 close-out audit: ctag conversion + 47 stay-C names (corpus prints PASS/FAIL)
  "test/keyboard/test-m31-imp1.el"              ; M31 imp-1: last-event-device + cannot-suspend moved to Scheme (corpus prints PASS/FAIL)
  "test/keyboard/test-m31-imp2.el"              ; M31 imp-2: dead SIGDANGER arm deleted + auto-save-interval moved to Scheme (corpus prints PASS/FAIL)
  "test/keyboard/test-m31-imp3.el"              ; M31 imp-3: close-out audit (converted names + budget/unlock-map guards; corpus prints PASS/FAIL)
  "test/keyboard/test-m32-imp1.el"              ; M32 imp-1: process.c wait decision path moved to (emacs process-wait) (corpus prints PASS/FAIL)
  "test/keyboard/test-m32-imp2.el"              ; M32 imp-2: process.c error paths + send_process drain moved to (emacs process-error); cmd_error_internal retired (corpus prints PASS/FAIL)
  "test/keyboard/test-m32-imp3.el"              ; M32 imp-3: emacs.c stuff_buffered_input caller ported; top-level + attempt-orderly-shutdown-on-fatal-signal moved to Scheme (corpus prints PASS/FAIL)
  "test/keyboard/test-m32-imp4.el"              ; M32 imp-4: eval.c probably_quit caller ported to (emacs eval-main); num-nonmacro-input-events + throw-on-input moved to Scheme (corpus prints PASS/FAIL)
  "test/keyboard/test-m32-imp5.el"              ; M32 imp-5: sysdep.c emacs_full_write drain ported to (emacs sysdep-main); tty-erase-char + attempt-stack-overflow-recovery moved to Scheme (corpus prints PASS/FAIL)
  "test/keyboard/test-m33-imp1.el"              ; M33 imp-1: term.c TTY help/mouse consumers moved to (emacs terminal); discard_mouse_events retired (corpus prints PASS/FAIL)
  "test/keyboard/test-m33-imp2.el"              ; M33 imp-2: xmenu.c/gtkutil.c menu/help consumers moved to (emacs menu); show_help_echo retired (corpus prints PASS/FAIL)
  "test/keyboard/test-m33-imp3.el"              ; M33 imp-3: xterm.c help-event decision moved to (emacs xterm) (corpus prints PASS/FAIL)
  "test/keyboard/test-m33-imp4.el"              ; M33 imp-4: xterm.c input test + 2 name readers moved to (emacs xterm) (corpus prints PASS/FAIL)
  "test/keyboard/test-m33-imp5.el"              ; M33 imp-5: pgtkterm.c read path moved to (emacs pgtk) — help guards, extra-keyboard-modifiers, mwheel-coalesce (corpus prints PASS/FAIL)
  "test/keyboard/test-m33-imp6.el"              ; M33 imp-6: 2 DEFVAR_* names moved to Scheme — extra-keyboard-modifiers + mwheel-coalesce-scroll-events deleted from keyboard-globals.c (corpus prints PASS/FAIL)
  "test/keyboard/test-m34-imp1.el"              ; M34 imp-1: dispnew.c display/poll callers moved to (emacs display) (corpus prints PASS/FAIL)
  "test/keyboard/test-m34-imp2.el"              ; M34 imp-2: frame.c swallow + single-kboard callers moved to (emacs frame) (corpus prints PASS/FAIL)
  "test/keyboard/test-m34-imp3.el"              ; M34 imp-3: window.c + fileio.c safe_run_hooks callers moved to (emacs window)/(emacs fileio) (corpus prints PASS/FAIL)
  "test/keyboard/test-m34-imp4.el"              ; M34 imp-4: minibuf.c input-state callers moved to (emacs minibuf) (corpus prints PASS/FAIL)
  "test/keyboard/test-m34-imp5.el"              ; M34 imp-5: xdisp.c part-1 hook callers moved to (emacs xdisp) (corpus prints PASS/FAIL)
  "test/keyboard/test-m34-imp6.el"              ; M34 imp-6: xdisp.c part-2 kboard + name readers moved to (emacs xdisp) (corpus prints PASS/FAIL)
  "test/keyboard/test-m12-umm.el"             ; M12 imp-1+imp-2 (used-mouse-menu flag corpus)
  "test/keyboard/test-m38-imp1.el"              ; M38 imp-1: the ERT count mismatch must fail the run (corpus prints PASS/FAIL)
  )
(group (m39) ; M39 imp-0 audit (docs/m39-plan.org)
  "test/m39/test-m39-imp1.el"                  ; M39 imp-1: the accept-process-output decision path moved into (emacs process-wait); the ported (secs nsecs flag) contract and the src/process.c wiring
  "test/m39/test-m39-imp2.el"                  ; M39 imp-2: the process read/write decision paths moved into (emacs process-io); the state gate and gap-move contract and the src/process.c wiring
  "test/m39/test-m39-imp3.el"                  ; M39 imp-3: the process Group A accessors moved into (emacs process-accessors); the --process-ref/--process-set! bridge and the retired-DEFUN wiring
  "test/m39/test-m39-imp3-e2e.el"              ; M39 imp-3 e2e: the moved accessors called on a live pipe process
  "test/m39/test-m39-imp4.el"                  ; M39 imp-4: the process signal family moved into (emacs process-signal); the retired DEFUNs, the --signal-* bridge, the type slot row, the image.c rewire
  "test/m39/test-m39-imp4-e2e.el"              ; M39 imp-4 e2e: the moved signal names called live (fboundp, signal-process, the stop/continue gate)
  "test/m39/test-m39-imp5.el"                  ; M39 imp-5 close-out: the end-to-end process surface (configure, talk, wait, signal), the M39 state words in the durable record, and this registration (corpus registers ERT tests)
  )
(group (m40) ; M40 imp-0 audit + imp-1 multibyte predicates + imp-2 send_process decision + imp-3 Group A accessors + imp-4a/4b Group C gates and lifecycle + imp-5 close-out (docs/m40-plan.org)
  "test/m40/test-m40-imp0-audit.el"           ; M40 imp-0 audit: the base re-scan, the send_process line pins, the doc pins (corpus registers ERT tests)
  "test/m40/test-m40-imp1.el"                 ; M40 imp-1: the multibyte-string-p deviation and the buffer enable-multibyte-characters read
  "test/m40/test-m40-imp2.el"                 ; M40 imp-2: the send_process multibyte-versus-unibyte decision moved to (emacs process-io); the two predicates and the src/process.c wiring
  "test/m40/test-m40-imp3.el"                 ; M40 imp-3: process-tty-name and process-inherit-coding-system-flag moved to (emacs process-accessors); the four new table rows and the two removed DEFUNs
  "test/m40/test-m40-imp4a.el"                ; M40 imp-4a: the Group C small-gate decisions moved to (emacs process-lifecycle); set-process-window-size / set-process-coding-system / process-datagram-address / set-process-datagram-address and the src/process.c wiring
  "test/m40/test-m40-imp4b.el"                ; M40 imp-4b: the remaining Group C decisions moved to (emacs process-lifecycle); delete-process / process-send-eof / internal-default-process-filter / internal-default-process-sentinel and the src/process.c wiring
  "test/m40/test-m40-imp5.el"                 ; M40 imp-5 close-out: the re-measured surface table, the src/process.c line pins, and the M40 close-out state words in the durable records (corpus reads files only)
  )
(group (m41) ; M41 imp-1 audit: the src/xdisp.c DEFUN classification and the caller map (docs/m41-plan.org)
  "test/m41/test-m41-imp1.el"                 ; M41 imp-1 audit: the base numbers, the 24 DEFUN classification words, the reclaimable/blocked caller map, and the (emacs xdisp) module (corpus reads files only)
  "test/m41/test-m41-imp2.el"                 ; M41 imp-2: the long-line-optimizations-p and invisible-p decisions moved to (emacs xdisp); the two static C dispatchers, the mapping unit checks, and the scm_c_public_ref re-pins (corpus reads files only)
  "test/m41/test-m41-imp3.el"                 ; M41 imp-3: the set-buffer-redisplay, get-display-property, and lookup-image-map decisions moved to (emacs xdisp); the three static C dispatchers and the scm_c_public_ref re-pins (corpus reads files only)
  "test/m41/test-m41-imp4.el"                 ; M41 imp-4 close-out: the re-measured surface table, the 24 src/xdisp.c DEFUN line pins, and the M41 close-out state words in the durable records (corpus reads files only)
  )
(group (m42) ; M42 imp-1 API audit + imp-2 Scheme policy with C syscall leaves
  "test/m42/test-m42-imp1.el"                 ; M42 imp-1 audit: the base numbers, the two OS shims and the Scheme policy body (imp-1 changes no C/Scheme), the descriptor source facts, and the A1 decision words (corpus reads files only)
  "test/m42/test-m42-imp2.el"                 ; M42 imp-2 redo: C retains read/ioctl leaves; Scheme policy tests, non-TTY leaf probes, and direction pins
  "test/m42/test-m42-imp3.el"                 ; M42 imp-3: the pty harness and cases 1-2 (no input, short read); INFO-skip when no pty or no built src/emacs
  "test/m42/test-m42-imp4.el"                 ; M42 imp-4: pty cases 3-6 (meta decode, quit byte, terminal loss, continuation); INFO-skip when no pty or no built src/emacs
  "test/m42/test-m42-imp5.el"                 ; M42 imp-5 close-out: the end surface, the two C leaf pins, the tracked close-out record, and the gate state
  )
(group (m43) ; M43 imp-1 audit + imp-2 the typed C termios leaves + imp-3 the init_sys_modes policy + imp-4 the reset/restore policy + imp-5 the tty-size policy + imp-6 the close-out (docs/m43-plan.org)
  "test/m43/test-m43-imp1.el"                 ; M43 imp-1 audit: the base re-scan, the src/sysdep.c function map, the termios leaf sites, and the A1/A2 decision words (corpus reads files only)
  "test/m43/test-m43-imp2.el"                 ; M43 imp-2: the two typed C termios leaves (--tty-get-mode, --tty-set-mode), the --tty-fd accessor, (emacs tty-modes), and the re-measured surface (corpus reads files only)
  "test/m43/test-m43-imp3.el"                 ; M43 imp-3: the init_sys_modes policy in (emacs tty-modes) (tty-mode-wanted, init-tty-mode, --tty-mode-constants), the C dispatcher, the deleted flag block, and the re-measured surface; the pure policy table test and the gated pty behaviour check (pty-driver-imp3.py) (corpus reads files and loads the .scm)
  "test/m43/test-m43-imp4.el"                 ; M43 imp-4: the reset/restore policy in (emacs tty-modes) (tty-mode-restore, tty-mode-no-echo, reset-tty-mode, suppress-echo-tty, unlock-tty-flow), the three C dispatchers, the --tty-flow-unlock leaf, the rewired reset_sys_modes / suppress_echo_on_tty / init_sys_modes, and the re-measured surface; the pure policy table test and the gated pty restore check (pty-driver-imp4.py) (corpus reads files and loads the .scm)
  "test/m43/test-m43-imp5.el"                 ; M43 imp-5: the tty-size policy in (emacs tty-modes) (tty-size-wanted, tty-size, set-tty-size), the --tty-get-size / --tty-set-size leaves, the get_tty_size_policy / set_window_size_policy dispatchers, the rewired get_tty_size / set_window_size, the deleted WINDOWSNT / MSDOS / TIOCSSIZE arms, and the re-measured surface; the pure size-policy table test and the gated pty size check (pty-driver-imp5.py) (corpus reads files and loads the .scm)
  "test/m43/test-m43-imp6.el"                 ; M43 imp-6 close-out: the re-measured surface, the line map, and the (m43) group line (corpus reads files only)
  "test/m43/test-m43-imp6-docs.el"            ; M43 imp-6 close-out docs guard: the three durable records are CLOSED (kb.org, m43-plan.org, milestone-overview.org) and milestone.org holds the next-milestone question; guarded INFO-skip on a fresh clone (corpus reads files only)
  )
(group (m44) ; M44 imp-1 audit: the src/sysdep.c signal / suspend-resume boundary (docs/m44-plan.org)
  "test/m44/test-m44-imp1.el"                 ; M44 imp-1 audit: the base re-scan, the signal / suspend line map, the four handler definition pins, the leaf shape, the min-count guard, and the A1/A2 decision (corpus reads files only)
  )
(group (m45) ; M45 imp-1 audit + imp-2 the typed C callproc.c leaves + imp-3 the parent-side rewire + imp-4 the close-out (docs/m45-plan.org)
  "test/m45/test-m45-imp1.el"                 ; M45 imp-1 audit: the base re-scan, the block line map, the three DEFUN pins, the two file facts, the leaf shape, the min-count guard, and the A1/A2 decision (corpus reads files only)
  "test/m45/test-m45-imp2.el"                 ; M45 imp-2: the four typed C leaves (--callproc-argv, --callproc-env, --callproc-resolve-program, --callproc-temp-name), (emacs process-create), the guile.h include, the re-measured surface, and the gated runtime probe (corpus reads files, and runs the built src/emacs)
  "test/m45/test-m45-imp3.el"                 ; M45 imp-3: the four C dispatch helpers and the unwinder, the rewired call_process / create_temp_file / make_environment_block hubs, the deleted inline policy, the two nil guards, the re-pinned tree-wide ref count, and the re-measured surface (corpus reads files, and runs the built src/emacs)
  "test/m45/test-m45-imp4.el"                 ; M45 imp-4 close-out: the re-measured surface, the (m45) group line, the per-group min-count guard, the close-out words in the gitignored records, and the env-guarded nested m45 gate check (corpus reads files, and runs ./tool/run-tests.sh --filter=m45)
  )
(group
  "test/src/eval-tests.el"
  "test/src/timefns-tests.el"
  "test/src/fns-tests.el"
  "test/src/floatfns-tests.el"
  "test/lisp/sort-tests.el"
  "test/src/data-tests.el"
  )
;; in the following group, all of the test files works with guilemacs
(group
  "test/lisp/ansi-color-tests.el" ;; fails
)(group
  "test/lisp/allout-widgets-tests.el"
  "test/lisp/ansi-osc-tests.el"
)(group
  "test/lisp/auth-source-pass-tests.el" ;; fails
;;;  )(group
  )
(group
  "test/lisp/autoinsert-tests.el"
  )
(group
  "test/lisp/battery-tests.el"
  )
   (group "test/lisp/buff-menu-tests.el") ;; fails
   (group "test/lisp/button-tests.el" ) ;; fails

(group
  "test/lisp/calculator-tests.el"
  "test/lisp/cedet/cedet-files-tests.el"
  "test/lisp/cedet/semantic-utest-c.el"
  "test/lisp/cedet/semantic/bovine/gcc-tests.el"
  )
(group
  "test/lisp/cedet/semantic/fw-tests.el"
  )
(group
  "test/lisp/cedet/srecode/fields-tests.el"
  )
(group
  "test/lisp/completion-tests.el"
  )
   (group "test/lisp/color-tests.el" ) ;; fails
  (group
  "test/lisp/cus-edit-tests.el"
  )
  (group
  "test/lisp/delim-col-tests.el"
  "test/lisp/desktop-tests.el"
  "test/lisp/elide-head-tests.el"
  )
  (group "test/lisp/edmacro-tests.el") ;; fails
  (group
  "test/lisp/emacs-lisp/byte-run-tests.el"
  "test/lisp/emacs-lisp/check-declare-tests.el"
  "test/lisp/emacs-lisp/cl-preloaded-tests.el"
  )
   (group "test/lisp/emacs-lisp/cl-print-tests.el" ) ;; fails
(group
  "test/lisp/emacs-lisp/cl-seq-tests.el"
  "test/lisp/emacs-lisp/copyright-tests.el"
  "test/lisp/emacs-lisp/derived-tests.el"
;;;  "test/lisp/emacs-lisp/easy-mmode-tests.el"
  )
   ; faceup uses syntax for string text-property #("ABC") but guile reader doesn't support  that
   ;(group "test/lisp/emacs-lisp/faceup-tests/faceup-test-files.el") ;; fails
   ;(group "test/lisp/emacs-lisp/faceup-tests/faceup-test-basics.el" ) ; fails
  (group
  "test/lisp/emacs-lisp/float-sup-tests.el"
  ; "test/lisp/emacs-lisp/hierarchy-tests.el" ;; fails, strings are eq in guilemacs, internalized
  )
  (group "test/lisp/emacs-lisp/lisp-mode-tests.el" ) ;; fails
  (group
  "test/lisp/emacs-lisp/icons-tests.el"
  ; "test/lisp/emacs-lisp/lisp-mnt-tests.el" ; fails
  ;"test/lisp/emacs-lisp/memory-report-tests.el" ; fails
  )
(group ;; fails
  "test/lisp/emacs-lisp/pp-tests.el"
;;;  "test/lisp/emacs-lisp/range-tests.el"
  "test/lisp/emacs-lisp/regexp-opt-tests.el"
  "test/lisp/emacs-lisp/ring-tests.el"
  )
(group
  "test/lisp/emacs-lisp/seq-tests.el" ;; pass
  )
(group
  "test/lisp/emacs-lisp/shadow-tests.el" ;; pass
  )
(group
  "test/lisp/emacs-lisp/syntax-tests.el" ;; pass
  "test/lisp/emacs-lisp/tabulated-list-tests.el" ;; fails -- depends on text-properties
 )
  (group "test/lisp/emacs-lisp/text-property-search-tests.el" ) ;; fails
  (group
  "test/lisp/emacs-lisp/thunk-tests.el"
  ;"test/lisp/emacs-lisp/unsafep-tests.el" ;; fail
  )
  (group
  "test/lisp/emacs-lisp/vtable-tests.el"
  )(group
  "test/lisp/faces-tests.el" ;; fails
  )(group
  "test/lisp/env-tests.el"
  ;"test/lisp/find-cmd-tests.el" ; fails
  "test/lisp/font-lock-tests.el" ; fails
  )
(group
  "test/lisp/format-spec-tests.el"
  "test/lisp/hfy-cmap-tests.el"
  "test/lisp/hi-lock-tests.el"
;;;  "test/lisp/htmlfontify-tests.el"
  )
  (group
  "test/lisp/ido-tests.el" ;; fails
  )
  ;(group
  ; "test/lisp/image-file-tests.el" ; fails
  ; )
  (group
  "test/lisp/imenu-tests.el"
  )
  (group
  "test/lisp/info-tests.el"
  )
  ; (group "test/lisp/international/mule-util-tests.el" ) ;; fails
  (group
   "test/lisp/isearch-tests.el" ; fails
   "test/lisp/jit-lock-tests.el" ; fails
   "test/lisp/json-tests.el" ; fails
  )
  (group
   "test/src/json-tests.el"
   )
  (group
  "test/lisp/misc-tests.el" ;; fails
  "test/lisp/lpr-tests.el"
  "test/lisp/md4-tests.el"
  "test/lisp/mwheel-tests.el"
  )
   ;(group "test/lisp/nxml/nxml-mode-tests.el" ) ;; fails
  (group
  ; "test/lisp/nxml/xsd-regexp-tests.el" ; fails
  "test/lisp/paren-tests.el"
  )(group
  "test/lisp/password-cache-tests.el"
  )(group
  "test/lisp/progmodes/asm-mode-tests.el" ;; fails
  )(group
  ;"test/lisp/pcmpl-linux-tests.el"
  "test/lisp/pcomplete-tests.el"
  ; "test/lisp/progmodes/autoconf-tests.el" ; fails
 )
;;; (group
;;;  "test/lisp/progmodes/bat-mode-tests.el"
;;;  "test/lisp/progmodes/bug-reference-tests.el"
;;;  "test/lisp/progmodes/executable-tests.el"
;;;  "test/lisp/progmodes/gdb-mi-tests.el"
;;;  )
;;; (group
;;;  "test/lisp/progmodes/glasses-tests.el"
;;;  "test/lisp/progmodes/opascal-tests.el"
;;;  "test/lisp/progmodes/pascal-tests.el"
;;;  "test/lisp/progmodes/ps-mode-tests.el"
;;;  )
   (group "test/lisp/progmodes/sh-script-tests.el")
  (group
  "test/lisp/progmodes/subword-tests.el"
  )
  (group
  "test/lisp/progmodes/tcl-tests.el"
  "test/lisp/ps-print-tests.el"
  )
;;;(group
;;;  "test/lisp/register-tests.el"
;;;  "test/lisp/rot13-tests.el"
;;;  "test/lisp/scroll-lock-tests.el"
;;;  "test/lisp/ses-tests.el"
;;;  )
;; in the rest of the groups, most test file has some test that
;; had to be disabled to work with guilemacs, they are counted as
;; false positives. So if you count total passed tests,
;; they need to be subtracted.
(group
  ;; these doesn't want to play with others
   "test/lisp/emacs-lisp/find-func-tests.el" ; doesn't like test/lisp/emacs-lisp/checkdoc-tests.el fails
;  "test/lisp/help-mode-tests.el" ; fails
   "test/lisp/help-fns-tests.el" ; fails
  )
(group
  "test/lisp/dired-tests.el"
  "test/lisp/progmodes/compile-tests.el"
;;;  "test/lisp/progmodes/js-tests.el"
  "test/lisp/simple-tests.el"
  )
(group ;; hangs
  "test/lisp/emacs-lisp/pcase-tests.el"
;;;  "test/lisp/emacs-lisp/package-tests.el"
  "test/lisp/replace-tests.el"
;;;  "test/lisp/international/mule-tests.el"
  )
;;;(group
;;; "test/lisp/mouse-tests.el"
  ; "test/lisp/auth-source-tests.el" ; fails
;;;  "test/lisp/dabbrev-tests.el"
;;;  "test/lisp/emacs-lisp/macroexp-tests.el"
;;;  )
(group
  "test/lisp/ls-lisp-tests.el"
  ; "test/lisp/loadhist-tests.el" ; fails
  )
(group
  ;"test/lisp/abbrev-tests.el" ;; hangs (or group)
   "test/lisp/emacs-lisp/let-alist-tests.el" ; fails
  )
(group
  "test/lisp/info-xref-tests.el"
;;;  "test/lisp/image-tests.el"
;;;  "test/lisp/ibuffer-tests.el"
  "test/lisp/hl-line-tests.el"
  )
(group
  "test/lisp/help-tests.el"
;;;  "test/lisp/obarray-tests.el" ;; pass
  "test/lisp/emacs-lisp/gv-tests.el"
  "test/lisp/files-tests.el"
  )
  (group "test/lisp/ffap-tests.el" ) ;; multibyte bug ; fails
  (group
  "test/lisp/progmodes/f90-tests.el" ;; crashes
  )(group
  "test/lisp/progmodes/elisp-mode-tests.el"
  )
(group "test/lisp/emacs-lisp/ert-x-tests.el" )
(group
  "test/lisp/emacs-lisp/ert-tests.el"
  )
(group
  "test/lisp/progmodes/flymake-tests.el"
  )
(group
  "test/lisp/emacs-lisp/lisp-tests.el"
  "test/lisp/emacs-lisp/subr-x-tests.el"
  "test/lisp/emacs-lisp/timer-tests.el"
  "test/lisp/emacs-lisp/warnings-tests.el"
;;;  "test/lisp/emacs-lisp/cl-generic-tests.el"
  )
 (group ; segfaults
   "test/lisp/emacs-lisp/cl-lib-tests.el"
   "test/lisp/emacs-lisp/cl-macs-tests.el"
   "test/lisp/emacs-lisp/comp-cstr-tests.el"
;;;   "test/lisp/emacs-lisp/ert-font-lock-tests.el"
   )
 (group
   "test/lisp/emacs-lisp/map-tests.el"
;;;   "test/lisp/emacs-lisp/rmc-tests.el"
   "test/lisp/emacs-lisp/rx-tests.el"
   "test/lisp/emacs-lisp/backquote-tests.el"
   )
 (group
;;;   "test/lisp/emacs-lisp/benchmark-tests.el"
   "test/lisp/emacs-lisp/bindat-tests.el"
;;;   "test/lisp/emacs-lisp/cconv-tests.el"
   "test/lisp/emacs-lisp/cl-extra-tests.el"
  )
(group
  "test/lisp/emacs-lisp/checkdoc-tests.el" ; run this not with test/lisp/emacs-lisp/find-func-tests.el

  "test/lisp/saveplace-tests.el"
  "test/lisp/shell-tests.el"
  "test/lisp/international/ccl-tests.el"
  )
(group
  "test/lisp/minibuffer-tests.el"
;;;  "test/lisp/align-tests.el"
  "test/lisp/allout-tests.el"
  "test/lisp/arc-mode-tests.el"
  "test/lisp/descr-text-tests.el"
  )
(group
;;;  "test/lisp/bookmark-tests.el"
;;;  "test/lisp/completion-preview-tests.el"
;;;  "test/lisp/custom-tests.el"
  )
  (group
;;;  "test/lisp/dired-aux-tests.el"
  "test/lisp/dired-x-tests.el"
;;;  "test/lisp/dnd-tests.el"
  "test/lisp/dom-tests.el"
  )
;;;  (group
;;;  "test/lisp/progmodes/cperl-mode-tests.el"
;;;  "test/lisp/progmodes/csharp-mode-tests.el"
;;;  "test/lisp/progmodes/project-tests.el"
;;;  )
 (group
  "test/lisp/progmodes/ruby-mode-tests.el"
  )
;;;(group
;;;  "test/lisp/progmodes/scheme-tests.el"
;;;  )
   (group "test/lisp/progmodes/sql-tests.el") ; fails

   (group "test/lisp/xt-mouse-tests.el")

;; M38 imp-1: the count-mismatch fixture.  Normally green, so it never
;; reddens a run; the m38-imp1 corpus runs it stressed
;; (GUILEMACS_M38_FIXTURE=1) to prove the harness exits non-zero on a
;; count mismatch.  Kept out of the keyboard group (brief.org M38 imp-1).
 (group
  "test/m38/test-m38-imp1-fixture.el"
  )

 ))

(define %emacs-exec "../src/temacs")

;; keep track manually of which tests are expensive or unstable
(define %skipped-tests '(
 "cperl-test-bug-10483" "info-xref-test-emacs-manuals" "package-test-update-archives-async" "password-cache-tests-add/expires-key" "test-htmlfontify-load-rgb-file" "cl-seq-test-bug24264" "srecode-field-utest-impl" "semantic-test-c-preprocessor-simulation"
 "dnd-tests-open-remote-url"))

(define %read-failures 0)
(define %total-passed-tests 0)
(define %total-failed-tests 0)
(define %total-gen-tests '())
(define %total-ert-tests '())
(define %total-found-gen-tests '())
(define %total-found-ert-tests '())
(define %total-failed-gen-tests '())
(define %total-failed-ert-tests '())
(define %total-passed-gen-tests '())
(define %total-passed-ert-tests '())

(define (elfmt-walk form)
  (cond
   ((and (pair? form) (eq? 'raw (car form)))
    (format #f "~a" (cadr form)))
   ((pair? form)
    (cons (elfmt-walk (car form)) (elfmt-walk (cdr form))))
   ((string? form)
    (format #f "~s" form))
   (else
    form)))

(define (elfmt form)
  (display (elfmt-walk form)
           (current-output-port))
  (newline (current-output-port)))

(define (el-expr form)
  (format (current-output-port) "~a" form))

(define (el-str str)
  (format #f "~a" str))

(define-syntax deftest
  (lambda (x)
    (syntax-case x ()
      ((_ name (expect) . body)
       #'(emit-test 'name #f 'expect (lambda () . body))))))

(define-syntax deftestf
  (lambda (x)
    (syntax-case x ()
      ((_ name (expect) . body)
       #'(emit-test name #f expect (lambda () . body)))
      ((_ name (type expect) . body)
       #'(emit-test name 'type expect (lambda () . body))))))

(define %testnum 0)

(define (emit-test name type expect thunk)
  ;; ensure name is unique
  (let* ((name (format #f "~a" name))
         (name (if (member name %total-gen-tests)
                   (let ((num (1+ %testnum)))
                     (set! %testnum num)
                     (string-concatenate (list name (format #f "-~a" num))))
                   name)))
    (push! %total-gen-tests name)
    (format (current-output-port) "(princ \"\\n-- test begin: ~a\\n\")~%" name)
    (format (current-output-port) "(princ \"\\n-- test expect: ~a\\n\")~%"
            (cond
             ((eq? type 'text) (format #f "~a" expect))
             ((string? expect) (format #f "\\\"~a\\\"" expect))
             (else expect)))
    (thunk)
    (format (current-output-port) "(princ \"\\n-- test end: ~a\\n\")~%" name)
    (format (current-output-port) "(flush-standard-output)~%")))

;; use the scheme-parser to read through the elisp-file
;; and search for deftest forms.
(define (scan-testfile filename)
  (let* ((failure #f)
         (r (lambda (port)
              (with-exception-handler
                  (lambda (exn)
                    (apply (lambda args
                             (format (current-error-port) "SCAN ERROR: filename: ~s, error: ~s~%" filename args)
                             (set! failure #t)
                             (set! %read-failures (1+ %read-failures))
                             #f)
                           (exception-kind exn)
                           (exception-args exn)))
                (lambda () (read port))
                #:unwind? #t
                #:unwind-for-type #t))))
    (call-with-input-file filename
      (lambda (port)
        (do ((form (r port) (r port)))
            ((eof-object? form))
          (if (and (pair? form) (eq? 'ert-deftest (car form)))
              (if (and (pair? (cdr form)) (symbol? (cadr form)))
                  (set! %total-ert-tests (assoc-set! %total-ert-tests
                                                     (symbol->string (cadr form))
                                                     '())))))))
    (when failure
      (format #t "Need to rescan file ~s.~%" filename)
      (call-with-input-file filename
        (lambda (port)
          (do ((line (get-line port) (get-line port)))
              ((eof-object? line))
            (cond
             ;; dont account skipped tests
             ((string-contains line "'(SIGSEGV-guilemacs") #f)
             ((string-contains line "'(DISABLE-guilemacs") #f)
             ((string-contains line "'(ert-deftest") #f)
             ((= 0 (or (string-contains line ";") -1)) #f)
             (else
              (let ((n (string-contains line "ert-deftest")))
                (when n
                  (let* ((name (substring line (+ 1 n (string-length "ert-deftest"))))
                         (name (substring name 0 (string-contains name " "))))
                    (if (and (not (string-contains name ",")) ; emit deftest through macro
                             (not (string-contains name ",(intern")) ; ditto
                             (not (string=? name "")))
                        (set! %total-ert-tests (assoc-set! %total-ert-tests name '()))))))))))))))

;; take a test-specification in scheme and generate an elisp test file
(define (testcompile-file file)
  (let ((elfile (substring (substring file 0 (- (string-length file) 4)) 5)))
    (with-output-to-file (string-concatenate (list elfile ".el"))
      (lambda ()
        (primitive-load (substring file 5)))
      #:encoding "UTF-8")
    elfile))

(define (testcompile-files files)
  (map (lambda (file)
         (cond
          ;; scheme file, first compile it
          ((= (- (string-length file) 4) (or (string-contains file ".scm") 0))
           (testcompile-file file))
          ;; raw elisp file, feed it to test target (emacs)
          (else
           ;; remove "/test" prefix and ".el" suffix
           (let ((s (substring file 5)))
             (scan-testfile s)
             (substring s 0 (- (string-length s) 3))))))
       files))

(define (run-tests-bare-emacs files keys)
  (let* ((files (randomize-list (testcompile-files files)))
         (args (append
                `(,%emacs-exec "-nl" "-Q" "--batch")
                (list
                 (string-concatenate
                  (apply append (map (lambda (file)
                                       (list "--prelude " (getcwd) "/" file " "))
                                     files))))
                '(" 2>&1"))))
    (format #t "Running prelude test files: ~a~%" files)
    (format #t "running ===> ~a~%" args)
    (let* ((port (open-input-pipe (string-join args " ")))
           (found '()) (pass '()) (fail '())
           (curname #f)
           (prevres #f)
           (expected #f)
           (curstr ""))
      (let loop ((line (get-line port)))
        (cond
         ((eof-object? line) #f)
         (else
          (cond
           ((equal? 0 (string-contains line "loading ")) #f) ; load messages
           ((equal? 0 (string-contains line ";;; ")) #f) ; guile notes and warnings
           ((equal? 0 (string-contains line ";; ")) #f) ; guile notes and warnings
           ((string-contains line "Symbol's elisp-function definition is void") #f)
           ((and (string-contains line "Loading ")
                 (string-contains line "(source)"))
            #f)
           ((string-contains line "-- test begin: ") =>
            (lambda (idx)
              ;; catch if a test-protocol didn't report TEST-END
              (if (and curname (not prevres))
                (push! fail curname))
              (let ((name (substring line (+ idx (string-length "-- test begin: ")))))
                (set! prevres #f)
                (set! curname name)
                (push! found name)
                (format #t "TEST-BEGIN: name [~s]~%" name))))
           ((string-contains line "-- test end: ") =>
            (lambda (idx)
              (let ((name (substring line (+ idx (string-length "-- test end: ")))))
                (format #t "TEST-END: name [~s]~%" name))
              (cond
               ((equal? expected curstr)
                (format #t "    Ok ~s.~%" curname)
                (push! pass curname)
                (set! prevres #t))
               (else
                (format #t "    FAIL!~%")
                (format #t "    EXPECTED: ~s~%" expected)
                (format #t "    GOT: ~s~%" curstr)
                (set! prevres #t) ;; avoid reporting failure again after loop-end
                (push! fail curname)))
              (set! expected #f)
              (set! curstr "")))
           ((string-contains line "-- test expect: ") =>
            (lambda (idx)
              (let ((val (substring line (+ idx (string-length "-- test expect: ")))))
                (set! expected val)
                (format #t "  TEST-EXPECT: val [~s]~%" val))))
           (else
            (if curname
                (set! curstr (string-concatenate (list curstr line))))
            (format #t "~a:~a [~a] >>> ~a~%"
                    (+ %total-passed-tests (length pass))
                    (+ %total-failed-tests (length fail))
                    curname line)))
          (loop (get-line port)))))
      (if (and curname (not prevres))
          (push! fail curname))
      (list found pass fail))))

(define (run-tests-loadup-emacs files keys)
  (let* ((files (randomize-list (testcompile-files files)))
         (args (append
                '("../src/emacs" "--no-init-file" "--no-site-file" "--no-site-lisp" "-L" ":." "-l" "ert")
                (apply append (map (lambda (file)
                                     (list "-l" file))
                                   files))
                '("--batch" "--eval" "'(ert-run-tests-batch-and-exit (quote (not (or (tag :expensive-test) (tag :unstable) (tag :nativecomp)))))' 2>&1"))))
    (format #t "Running test files: ~a~%" files)
    (format #t "running ===> ~a~%" args)
    (let* ((port (open-input-pipe (string-join args " ")))
           (pass '())
           (skipped 0)
           (tot 0)
           (ran-summary? #f)
           ;; Match an ERT per-test result line:
           ;;   passed  1/3  allout-test-range-overlaps (0.000 sec)
           ;;   FAILED  3/3  name (0.000 sec)
           ;; Group 1 is the result word, group 2 the index N, group 3 the
           ;; total M, group 4 the test name.  ERT prints the total M on
           ;; every result line (passed or not).  Do NOT key on the index N:
           ;; N stops at the last PASS, so a failing LAST test hides the
           ;; count mismatch (M38 D1, review F1).
           (re (make-regexp "^[ ]*(passed|failed|FAILED|skipped|SKIPPED|aborted|ABORTED|quit|QUIT|unknown|UNKNOWN|PASSED)[ ]+([0-9]+)/([0-9]+)[ ]+([^ ]*)")))
      (let loop ((line (get-line port)))
        (cond
         ((eof-object? line) #f)
         (else
          (format #t "~a:~a >>> ~a~%" (+ (length pass) %total-passed-tests)
                  %total-failed-tests line)
          ;; ERT's own completion banner, printed once ert-run-tests-
          ;; batch-and-exit finishes: "Ran N tests, M results as expected,
          ;; K unexpected (...)", optionally "Aborted: " prefixed.  This
          ;; substring is distinctive and appears regardless of N, so
          ;; seeing it at all -- even for N = 0 -- proves the batch runner
          ;; actually ran to completion; a *test* selected out by tag
          ;; (:unstable, :expensive-test, :nativecomp) still prints it.
          ;; Its absence means the subprocess crashed or aborted before
          ;; getting there (see the TOT == 0 arm below).
          (if (string-contains line "results as expected,")
              (set! ran-summary? #t))
          (let ((f (list-matches re line)))
            (unless (null? f)
              (let* ((pos-res (vector-ref (car f) 2))
                     (pos-tot (vector-ref (car f) 4))
                     (pos-name (vector-ref (car f) 5))
                     (result (substring line (car pos-res) (cdr pos-res)))
                     (total (substring line (car pos-tot) (cdr pos-tot)))
                     (test-name (substring line (car pos-name) (cdr pos-name))))
                (set! tot (string->number total))
                (cond
                 ((string-ci=? result "passed") (push! pass test-name))
                 ((string-ci=? result "skipped") (set! skipped (1+ skipped))))))
          (loop (get-line port))))))
      ;; Assert the ERT test protocol.  ERT ran TOT tests, but only the
      ;; observed pass names plus controlled skips were accounted for.  A
      ;; difference means a test failed with no other record (false green,
      ;; M38 D1).  Keep the ERROR text and record the mismatch in the fail
      ;; list, so the single exit path at the report reaches it.  Do not
      ;; change PASS.
      ;;
      ;; A batch that never prints its completion summary at all is its
      ;; own failure, not a silent pass-through: FILES is never empty here
      ;; (maybe-run-tests only calls run-tests, and so this function, with
      ;; a non-empty, already-filtered file list), so the subprocess
      ;; always loads at least one real test file.  RAN-SUMMARY? staying
      ;; #f means ert-run-tests-batch-and-exit never finished -- e.g. an
      ;; uncaught error while loading one of the -l files (a missing
      ;; docs/ file read unconditionally) crashes the subprocess before
      ;; ERT gets to run at all.  TOT stays at its initial 0 in this case,
      ;; which is NOT the same as a group that legitimately selects zero
      ;; tests (every test in the file tagged out): that case DOES print
      ;; the completion summary ("Ran 0 tests, 0 results as expected, 0
      ;; unexpected") and RAN-SUMMARY? distinguishes it from a crash.
      ;; Without this arm, both cases satisfy (+ (length pass) skipped) =
      ;; tot vacuously (0 = 0) and the crash case hides the same
      ;; false-green class M38 D1 was written to catch.
      (let ((crashed? (not ran-summary?))
            (mismatch? (not (= (+ (length pass) skipped) tot))))
        (if (or crashed? mismatch?)
            (format #t "ERROR: ~a passed, but ~a counted pass~a.~%"
                    (length pass) tot
                    (if crashed? " (batch runner never completed)" "")))
        ;; Name FILES in the mismatch string itself, not just in the
        ;; "Running test files:" line printed above: that line is easy to
        ;; find in this group's own raw output, but the mismatch string is
        ;; also what ends up alone, far from that context, in the final
        ;; report's summary list (run-tests's caller collects fail lists
        ;; across every group into one flat accumulator).  Without FILES
        ;; here, tracing a mismatch back to its group means grepping the
        ;; full log by hand for the nearest preceding "Running test
        ;; files:" line.
        (list pass pass
              (cond
               (crashed?
                (list (format #f "ERT count mismatch: batch runner never completed (subprocess crashed or aborted before any result was reported) [~a]"
                              files)))
               (mismatch?
                (list (format #f "ERT count mismatch: ~a passed, but ~a counted pass [~a]"
                              (length pass) tot files)))
               (else '())))))))

(define (run-tests files keys)
  (flush-all-ports)
  (match (cond
          ((memq 'prelude keys)
           (match (run-tests-bare-emacs files keys)
             ((found pass fail)
              (push-append! %total-found-gen-tests found)
              (push-append! %total-passed-gen-tests pass)
              (push-append! %total-failed-gen-tests fail)
              (list found pass fail))))
          (else
           (match (run-tests-loadup-emacs files keys)
             ((found pass fail)
              (push-append! %total-found-ert-tests found)
              (push-append! %total-passed-ert-tests pass)
              (push-append! %total-failed-ert-tests fail)
              (list found pass fail)))))
    ((found pass fail)
     (set! %total-failed-tests (+ (length fail) %total-failed-tests))
     (format #t "tests result in group: ~a found tests (atleast), ~a passed, ~a failed~%"
                (length found) (length pass) (length fail))
     (if (not (null? fail))
         (format #t "  failed tests: ~s~%" fail)))))

(define (maybe-run-tests files keys test-filter)
  (when (or (null? (memq 'prelude keys))
            ;; check prelude
            (if (memq 'prelude test-filter)
                (memq 'prelude keys)
                #t))
    ;; check filter
    (let ((filters (filter string? test-filter)))
      (if (not (null? filters))
          (set! files
                (filter (lambda (file)
                          (fold (lambda (a m)
                                  (or m
                                      (string-contains file a)))
                                #f
                                filters))
                        files)))
      (if (not (null? files))
          (run-tests files keys)))))

(define (main args)
  (let ((test-filter '()))
    (for-each (lambda (arg)
                (if (string=? "--prelude" arg)
                    (push! test-filter 'prelude))
                (if (string-contains arg "--filter=")
                    (push! test-filter (substring arg 9))))
              args)
    (set! *random-state* (random-state-from-platform))
    ;; test
    (let* ((files '())
           (done #f))
      (for-each (lambda (line)
                  (when (not done)
                    (cond
                     ((eq? 'done line) (set! done #t))
                     ((and (pair? line)
                           (eq? 'quote (car line)))
                      #f)
                     ((and (pair? line)
                           (eq? 'group (car line)))
                      (let ((keys (if (and (pair? (cdr line)) (pair? (cadr line)))
                                      (cadr line)
                                      '())))
                        (if (not (null? keys)) ; skip the keys
                            (set! line (cdr line)))
                        ;; run any currently collected files
                        (unless (null? files)
                          (maybe-run-tests files '() test-filter))
                        ;; run the files in the group
                        (maybe-run-tests (cdr line) keys test-filter)
                        (set! files '())))
                     (else
                      (push! files line)))))
                %tests)
      (unless (null? files)
        (maybe-run-tests files '() test-filter)))
    (flush-all-ports)
    ;; report
    (format #t "~%#################################################################~%")
    (format #t "# * ERT test -- a test that comes from the Emacs Regression Test framework.~%")
    (format #t "#   These test files are scanned and counted before being run~%")
    (format #t "#   (because running the target may abort and not report totals).~%")
    (format #t "# * gen test -- a simple test protocol, where Scheme is used to generated test cases in elisp-files, these are counted during emit.~%")
    (format #t "# * found -- a test that is either emitted during test generation, or found when search the ERT suite~%")
    (format #t "# * passed -- a test that explicitly reports success~%")
    (format #t "# * failed -- a test that explicitly reports a failure mode~%")
    (format #t "# * missing -- a test that was found during search, but has not reported its result, the test has either aborted during run,~%")
    (format #t "#   or hasn't been runned, both cases are counted as a failed test (ie, not a controlled skip).~%")
    (format #t "# * found: known tests found during emit or search~%")
    (let* ((num-total-gen-tests (length %total-gen-tests))
           (num-total-ert-tests (length %total-ert-tests))
           (num-total-found-gen-tests (length %total-found-gen-tests))
           (num-total-found-ert-tests (length %total-found-ert-tests))
           (num-total-passed-gen-tests (length %total-passed-gen-tests))
           (num-total-passed-ert-tests (length %total-passed-ert-tests))
           (num-total-failed-gen-tests (length %total-failed-gen-tests))
           (failed-gen (filter (lambda (x)
                                 (not (member x %total-passed-gen-tests)))
                               %total-gen-tests))
           (failed-ert (filter (lambda (x)
                                 (and (not (member (car x) %total-passed-ert-tests))
                                      (not (member (car x) %skipped-tests))))
                               %total-ert-tests))
           (num-total-failed-ert-tests (+ (length failed-ert)
                                          ;; M38 D1: count mismatches recorded
                                          ;; by run-tests-loadup-emacs.
                                          (length %total-failed-ert-tests))))
      (format #t "~%")
      (if (not (null? %total-failed-gen-tests))
          (format #t "~%~%* failed generated tests ~s~%" %total-failed-gen-tests))
      (if (not (null? %total-failed-ert-tests))
          (format #t "* failed ERT tests ~s~%" %total-failed-ert-tests))
      (if (not (null? failed-gen))
          (format #t "~%failed gen tests: ~s~%~%" failed-gen))
      (if (not (null? failed-ert))
          (format #t "failed ERT tests: ~s~%~%" failed-ert))
      (format #t "Read failures when reading ERT test files: ~s~%" %read-failures)
      ;; M38 D1/review F3: this line must agree with the "fail ERT" cell of
      ;; the table below.  Use num-total-failed-ert-tests, which is the
      ;; scanned-missing set plus the count-mismatch accumulator.
      (format #t "Total number of failed/missing ERT tests: ~a   ;; scanned but never runned, or counted but not passed~%"
              num-total-failed-ert-tests)
      (format #t "--------------------------------------------~%")
      (print-report-table
       (list '("" "gen" "ERT" "total" "")
             (list "found"
                   num-total-gen-tests
                   num-total-ert-tests
                   (+ num-total-gen-tests num-total-ert-tests)
                   ; #f
                   )
             (list "runned"
                   num-total-found-gen-tests
                   num-total-found-ert-tests
                   (+ num-total-found-gen-tests num-total-found-ert-tests)
                   ; #f
                   )
             (list "pass"
                   num-total-passed-gen-tests
                   num-total-passed-ert-tests
                   (+ num-total-passed-gen-tests num-total-passed-ert-tests)
                   ; %total-passed-tests
                   )
             (list "fail"
                   num-total-failed-gen-tests
                   num-total-failed-ert-tests
                   (+ num-total-failed-gen-tests num-total-failed-ert-tests)
                   ; %total-failed-tests
                   )))
      (exit (if (> (+ num-total-failed-gen-tests num-total-failed-ert-tests) 0)
                1 0)))))
