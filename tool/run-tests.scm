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
(group (strings) ; the (emacs strings) module predicates
  "test/strings/elisp-stringp.el"            ; a SCHEME-MODULE test: the elisp-stringp / elisp-char-or-string-p wrapper arms, which an elisp (stringp X) call cannot reach (the `or' short-circuits on a real string, and the `defined?' guard reads the dynamic current module).  Drives the (emacs strings) procedures directly with the current module set
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
  "test/m43/test-m43-imp3.el"                 ; M43 imp-3: the init_sys_modes policy in (emacs tty-modes) (tty-mode-wanted, init-tty-mode, --tty-mode-constants), the C dispatcher, the deleted flag block, and the re-measured surface; the pure policy table test and the gated pty behaviour check (test/pty-driver.py --group m43-imp3) (corpus reads files and loads the .scm)
  "test/m43/test-m43-imp4.el"                 ; M43 imp-4: the reset/restore policy in (emacs tty-modes) (tty-mode-restore, tty-mode-no-echo, reset-tty-mode, suppress-echo-tty, unlock-tty-flow), the three C dispatchers, the --tty-flow-unlock leaf, the rewired reset_sys_modes / suppress_echo_on_tty / init_sys_modes, and the re-measured surface; the pure policy table test and the gated pty restore check (test/pty-driver.py --group m43-imp4) (corpus reads files and loads the .scm)
  "test/m43/test-m43-imp5.el"                 ; M43 imp-5: the tty-size policy in (emacs tty-modes) (tty-size-wanted, tty-size, set-tty-size), the --tty-get-size / --tty-set-size leaves, the get_tty_size_policy / set_window_size_policy dispatchers, the rewired get_tty_size / set_window_size, the deleted WINDOWSNT / MSDOS / TIOCSSIZE arms, and the re-measured surface; the pure size-policy table test and the gated pty size check (test/pty-driver.py --group m43-imp5) (corpus reads files and loads the .scm)
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
(group (m46) ; M46 imp-1 audit + imp-2 the typed C filelock.c leaves + imp-3 the parent-side rewire + imp-4 the close-out (docs/m46-plan.org)
  "test/m46/test-m46-imp1.el"                 ; M46 imp-1 audit: the base re-scan, the block line map, the five DEFUN pins, the two file facts, the leaf shape, the min-count guard, and the A1/A2 decision (corpus reads files only)
  "test/m46/test-m46-imp2.el"                 ; M46 imp-2: the eight typed C leaves (--filelock-boot-sec, --filelock-lock-info, ...), (emacs filelock), the guile.h include, the re-measured surface, and the gated runtime probe (corpus reads files, and runs the built src/emacs)
  "test/m46/test-m46-imp3.el"                 ; M46 imp-3: the eight C dispatch helpers and the clash static, the rewired lock_file_1 / lock_file / unlock_file / file-locked-p hubs, the deleted lock_if_free inline policy, the raw-owner-line shape, the re-pinned tree-wide ref count, and the re-measured surface (corpus reads files, and runs the built src/emacs)
  "test/m46/test-m46-imp4.el"                 ; M46 imp-4 close-out: the re-measured surface, the (m46) group line, the per-group min-count guard, the close-out words in the gitignored records, and the env-guarded nested m46 gate check (corpus reads files, and runs ./tool/run-tests.sh --filter=m46)
  )
(group (m47) ; M47 imp-1 audit + imp-2 the typed C fileio.c leaves (docs/m47-plan.org)
  "test/m47/test-m47-imp1.el"                 ; M47 imp-1 audit: the base re-scan, the block line map (the 32 block definitions + the ref site), the file facts, the leaf shape, the min-count guard, and the A1/A2 decision (corpus reads files only)
  "test/m47/test-m47-imp2.el"                 ; M47 imp-2: the 26 typed C leaves (--fileio-file-name-directory, --fileio-expand-file-name, ...), (emacs fileio), the guile.h include, the re-measured surface, and the gated runtime probe (corpus reads files, and runs the built src/emacs)
  "test/m47/test-m47-imp3.el"                 ; M47 imp-3: the 8 G1 dispatch helpers and the 8 pure C mechanisms, the rewired file-name / path hubs, the 2 OPEN G1 leaves unblocked, the real (emacs fileio) path policy, the re-measured surface, and the gated runtime probe (corpus reads files, and runs the built src/emacs)
  "test/m47/test-m47-imp4.el"                 ; M47 imp-4: the 11 G2 dispatch helpers and the 11 pure C mechanisms (check_file_access_1, file_writable_p_1), the rewired OS-query predicate hubs (file-exists-p ... file-system-info), the real (emacs fileio) G2 decision, the C errno channel, the re-measured surface, and the gated runtime probe (corpus reads files, and runs the built src/emacs)
  "test/m47/test-m47-imp5.el"                 ; M47 imp-5: the 7 G3 dispatch helpers and the 7 pure C mechanisms (copy_file_1 ... make_symbolic_link_1), the rewired copy / rename / link / delete hubs, the 4 G3 OPEN leaves unblocked, the real (emacs fileio) target-name resolution, the deleted expand_cp_target, the re-measured surface, and the gated runtime probe (corpus reads files, and runs the built src/emacs)
  "test/m47/test-m47-imp6.el"                 ; M47 imp-6 close-out: the re-measured surface, the (m47) group registration, the per-group min-count guard, and the in-process group-total ert-deftest (corpus reads files only)
  )
(group (m48) ; M48 imp-1 audit + imp-2 the typed C term.c --term-* leaves + imp-3 the G1 terminal-capability policy + imp-4 the G3 query / geometry policy (docs/m48-plan.org)
  "test/m48/test-m48-imp1.el"                 ; M48 imp-1 audit: the base re-scan (D1), the block map as the ordered DEFUN name list (the 19 block names + the 3 ref sites, D2), and the per-group min-count guard (D5).  Tracked files only: the record needles live in tool/m48-plan-lint.sh, which this group does not run
  "test/m48/test-m48-imp2.el"                 ; M48 imp-2: the 8 typed C leaves (--term-display-color-p ... --term-display-pixel-height), the 8 wrappers of (emacs terminal), the guile.h include, the boundary rules, and the gated runtime probe (corpus reads tracked files, and runs the built src/emacs)
  "test/m48/test-m48-imp3.el"                 ; M48 imp-3: the G1 terminal-capability policy (tty-display-color-p / -cells, tty-type, controlling-tty-p) moves to (emacs terminal).  The 4 *_scheme dispatch helpers, the 4 rewired hubs with the inline decision gone, the 4 new ref sites, the boundary rules on the unchanged module, and the gated runtime probe (tracked files only, plus the built src/emacs)
  "test/m48/test-m48-imp4.el"                 ; M48 imp-4: the G3 query / geometry policy (tty-frame-geometry / -edges, tty-display-pixel-width / -height) moves to (emacs terminal).  The 4 *_scheme dispatch helpers over the 2 shared static helpers, the rewired hubs with the inline geometry arithmetic and the 80x25 pair gone, the 4 new ref sites, the boundary rules on the unchanged module, and the gated runtime probe (tracked files only, plus the built src/emacs)
  "test/m48/test-m48-imp5.el"                 ; M48 imp-5 close-out: the re-measured surface, the (m48) group registration, the per-group min-count guard, and the in-process group-total ert-deftest (corpus reads tracked files only)
  )
(group (m49) ; M49 imp-1 the src/dired.c directory / attribute boundary audit + imp-2 the typed C --dired-* leaves + imp-3 the G1 listing policy + imp-4 the G3 attribute predicate in Scheme (docs/m49-plan.org)
  "test/m49/test-m49-imp1.el"                 ; M49 imp-1 audit: the base re-scan (D1), the block map as the ordered DEFUN name list (the 8 block names, D2), and the per-group min-count guard (D5).  Tracked files only: the record needles live in tool/m49-plan-lint.sh, which this group does not run
  "test/m49/test-m49-imp2.el"                 ; M49 imp-2: the 4 typed C --dired-* leaves (2 after imp-4; G2 returns A2), the guile.h include, the wrappers of (emacs dired), the boundary rules, and the gated runtime probe
  "test/m49/test-m49-imp3.el"                 ; M49 imp-3: the deleted G1 leaf, the static dired_read_names_1 mechanism, the (emacs dired) dired-listing-names policy (separator / join / match / count / sort), the rewired directory-files hub, the boundary rules, and one gated runtime probe (FULL / MATCH / NOSORT / COUNT)
  "test/m49/test-m49-imp4.el"                 ; M49 imp-4: the deleted G3 leaf, the static G3 dispatch helper, the (emacs dired) dired-file-attributes-lessp predicate over %string-lessp, the rewired file-attributes-lessp hub that keeps the Fcar extraction, the G2 A2 record, the boundary rules, and the gated runtime probe (sole exact match / longest common prefix / directory slash / sort key)
  "test/m49/test-m49-imp5.el"                 ; M49 imp-5 close-out: the re-measured surface, the (m49) group registration, the per-group min-count guard, and the in-process group-total ert-deftest (corpus reads tracked files only)
  )
(group (m50) ; M50 imp-1 the src/emacs.c invocation / daemon boundary audit (docs/m50-plan.org)
  "test/m50/test-m50-imp1.el"                 ; M50 imp-1 audit: the three-candidate base re-scan (D1), the src/emacs.c block map as the ordered DEFUN name list (the 5 block names, D2), and the per-group min-count guard (D5).  Tracked files only: the record needles live in tool/m50-plan-lint.sh, which this group does not run
  "test/m50/test-m50-imp2.el"                 ; M50 imp-2: the (emacs emacs) module and the boundary facts that survive imp-3; the typed --emacs-daemon-state leaf is deleted by imp-3, so its decision, bridge, and policy live in the imp-3 corpus
  "test/m50/test-m50-imp3.el"                 ; M50 imp-3: the moved daemonp decision, the deleted --emacs-daemon-state leaf, the C bridge emacs_daemonp_scheme, the (emacs emacs) emacs-daemonp policy, the boundary rules, and the gated runtime probe (the daemonp nil result)
  "test/m50/test-m50-imp4.el"                 ; M50 imp-4: the EMPTY finding.  The re-scan of src/emacs.c gives the 5-block map (G1), the verdict that no movable policy remains, and the settled audit ambiguity (a copy is not a decision, so the two invocation accessors STAY C); the re-measured surface (G2); the group registration and the per-group min-count guards (G3); and the gated runtime probe (the daemonp nil result).  C delta 0; Scheme delta 0
  "test/m50/test-m50-imp5.el"                 ; M50 imp-5 close-out: the re-measured surface of section 3 (S1), the (m50) group registration after imp-4 (S2), the per-group min-count guards and the in-process group-total ert-deftest (S3), and the gated runtime probe (the daemonp nil result).  Tracked files only (src/, mod/, prelude/, tool/); the record needles live in tool/m50-plan-lint.sh, which this group does not run.  C delta 0; Scheme delta 0
  )
(group (m51) ; M51 imp-4 the src/image.c image file handle moves to Scheme (docs/m51-plan.org)
  "test/m51/test-m51-imp4.el"                 ; M51 imp-4 behavior: the image file handle in (emacs image).  The headless hop group calls the module through the elisp eval-scheme bridge and checks the bytevector of the tracked etc/images/alt.pbm (resolve, byte count vs the file size, first byte, a miss, an empty file); the decode group loads a real tracked PBM and a scratch-dir PBM through the built src/emacs and checks a missing-file failure path.  A missing window system is an explicit INFO-skip; any other signalled error is a FAIL.  Min-count guards make a zero-check run FAIL.  Tracked files only.  The imp-1 / imp-3 static audits move to tool/ and run from the advisory tool/m51-audit.sh (tool/test-m51-imp1.el, tool/test-m51-imp3.el); the record needles live in tool/m51-plan-lint.sh
  "test/m51/test-m51-imp5.el"                 ; M51 imp-5 behavior: the streaming image file handle.  The headless `stream` group drives the tracked etc/images/gnus/gnus.png through (emacs image) image-open-stream / image-handle-read / image-close via the elisp eval-scheme bridge (the open returns a port, the first chunk has the PNG magic byte 0x89, the read reaches #f EOF, a missing file yields #f, the close is idempotent); the window-gated `decode` group loads a tracked PNG and JPEG through the built src/emacs and exercises the decoder-failure cleanup on a truncated PNG.  A missing window system is an explicit INFO-skip; any other signalled error is a FAIL.  Min-count guards make a zero-check run FAIL.  Tracked files only.  The static audits move to tool/ and run from the advisory tool/m51-audit.sh; the record needles live in tool/m51-plan-lint.sh
  )
(group (m52) ; M52 imp-3 the src/term.c TTY output boundary leaves + the (emacs tty-output) module (docs/m52-plan.org)
  "test/m52/test-m52-imp3.el"                 ; M52 imp-3 behavior: runs the built src/emacs on a pty and calls the Scheme tty-write-bytes, tty-emit-cap, and tty-emit-seq wrappers.  The driver reads bytes from the pty master and compares each marked output span with the expected bytes and the leaf's reported count.  No source-layout checks run in test/.  A pty allocation failure is an explicit INFO skip; a child or output mismatch is a FAIL.
  "test/m52/test-m52-imp4.el"                 ; M52 imp-4 behavior: the 5 insert / highlight policy procedures of (emacs tty-output).  Headless checks resolve the module through eval-scheme and call each procedure for both flags (the policy table and the #nil rule).  One pty case drives the built src/emacs through the policy -> key -> bytes chain.  No source-layout checks run in test/.  A pty allocation failure is an explicit INFO skip.
  "test/m52/test-m52-imp5.el"                 ; M52 imp-5 behavior: the 6 bell / cursor / update-end policy procedures of (emacs tty-output).  Headless checks resolve the module through eval-scheme and call each procedure for every flag combination (the policy table, the #nil rule, and the ordered step list).  One pty case drives the built src/emacs through the policy -> key -> bytes chain.  No source-layout checks run in test/.  A pty allocation failure is an explicit INFO skip.
  "test/m52/test-m52-imp6.el"                 ; M52 imp-6 behavior: the 4 terminal-mode / cursor-motion policy procedures of (emacs tty-output).  Headless checks resolve the module through eval-scheme and call each procedure for every flag combination (the policy table, the #nil rule, the ordered step list with markers, and the marker-only rule for the 2 cursor hubs).  One pty case drives the built src/emacs through the policy -> key -> bytes chain.  No source-layout checks run in test/.  A pty allocation failure is an explicit INFO skip.
  "test/m52/test-m52-imp7.el"                 ; M52 imp-7 behavior: the 3 clear-selection policy procedures of (emacs tty-output).  Headless checks resolve the module through eval-scheme and call each procedure for every flag combination (the policy table, the key/marker shapes, the #nil guard rule for the end-of-line procedure).  One pty case drives the built src/emacs through the policy -> key -> bytes chain.  No source-layout checks run in test/.  A pty allocation failure is an explicit INFO skip.
  "test/m52/test-m52-imp8.el"                 ; M52 imp-8 behavior: the 4 scroll / window / glyph arithmetic policy procedures of (emacs tty-output).  Headless checks resolve the module through eval-scheme and call each procedure for every flag combination (the policy table, the key/marker shapes, the #nil guard rule for the ins/del procedure, and the m52_caps key pin).  One pty case drives the built src/emacs through the policy -> key -> bytes chain.  No source-layout checks run in test/.  A pty allocation failure is an explicit INFO skip.
  "test/m52/test-m52-imp9.el"                 ; M52 imp-9 close-out: the re-measured surface of brief.org section 3.2 (S1), the (m52) group registration after imp-8 and the test/pty-driver.py group / total-case-count pins (S2), the per-group min-count guards and the in-process group-total ert-deftest (S3).  Tracked files only (src/, mod/, prelude/, tool/run-tests.scm, test/pty-driver.py); it does NOT read docs/.  C delta 0; Scheme delta 0
  )
(group (m53) ; M53 imp-1 the end-state evidence audit; M53 imp-2 the standalone Guile loader check (docs/m53-plan.org)
  "test/m53/test-m53-imp1.el"                 ; M53 imp-1 audit (docs only; C delta 0, Scheme delta 0): S1 re-measures the brief.org section 5 surface (src/term.c 6,078 lines / 29 ^DEFUN ( / 4 --tty-* leaf DEFUNs / 33 scm_c_public_ref sites; mod/emacs/tty-output.scm 343 lines; tree-wide scm_c_public_ref 257).  S2 is CHECK 1, the standalone loader: a plain `guile' subprocess (no Emacs C core) loads (emacs loader) and (emacs reader), a real Elisp file loads through the Scheme loader, and the loader / reader / src/lread.c entry points are present.  S3 is CHECK 2, the PTY terminal path: the src/termchar.h FILE * streams, the test/pty-driver.py groups, and the test/m42/pty-runner.el harness.  S4 pins the (m53) group registration, the pty-driver 26-case total and the --selftest entry.  S5 holds the per-group min-count guards and the in-process group-total ert-deftest.  Tracked files only; it does NOT read docs/.  A missing guile binary is an explicit INFO skip, never a pass
  "test/m53/test-m53-imp2.el"                 ; M53 imp-2 behavior (brief.org section 3.3): the standalone Guile loader check.  S1 is the loader POLICY fix in mod/emacs/loader.scm -- elisp-validate-load-file tolerates the empty `length' cell (the FIRST blocked cell on the real path) via elisp-string-length-for-load, and elisp-check-file-handler guards the (downstream) empty find-file-name-handler cell with symbol-fbound?; a plain `guile -L mod' subprocess loads a real temporary .el file through the Scheme loader, passes validation, and stops at the recorded blocker (the empty get-load-suffixes cell), instead of raising wrong-type-arg at the handler.  (The old comment claimed "Scheme #nil is truthy"; that is FALSE -- (if #nil 'T 'F) yields F -- so only the apply raised, inside the let binding, before the (if handler ...) test.)  S2 is the traced cell list in call order: length (cell 1, tolerated), find-file-name-handler (cell 2, tolerated), get-load-suffixes (cell 3, blocked); each is EMPTY in a plain `guile' probe.  S3 is the A1 sub-check: a real Elisp file loads through the Scheme loader in the built src/emacs and its setq side effect is read.  S4 pins the registration and the per-group min-count guards; the group-total deftest selects only ^m53-imp2.  Tracked files only; it does NOT read docs/.  A missing guile binary is an explicit INFO skip, never a pass
  "test/m53/test-m53-imp3.el"                 ; M53 imp-3 behavior (brief.org section 3): the PTY terminal VERTICAL SLICE.  One driver case (m53-imp3/vertical-slice-e2e) runs the whole slice in the built src/emacs on a pty -- start, load a real Elisp file, read input, write output, resize (TIOCSWINSZ, a live resize after READY), exit, and restore the terminal modes (a termios read-back after exit).  S1 pins the driver case name and group.  S2 pins the resize / mode-readback / exit-wait / load-fixture wiring in test/pty-driver.py.  S3 runs the real slice (python3 test/pty-driver.py --emacs src/emacs --group m53-imp3); a missing built src/emacs or a missing pty is a controlled INFO skip.  S4 pins the registration and the per-group min-count guards; the group-total deftest selects only ^m53-imp3.  Tracked files only; it does NOT read docs/
  "test/m53/test-m53-imp4.el"                 ; M53 imp-4 close-out: the re-measured surface of brief.org section 3 (S1: src/term.c 6,078 lines / 29 ^DEFUN ( / 4 --tty-* leaf DEFUNs / 33 scm_c_public_ref sites; mod/emacs/tty-output.scm 343 lines; tree-wide scm_c_public_ref 257), the (m53) group registration after imp-3 and the test/pty-driver.py 26-case total pin (S2), the per-group min-count guards and the in-process group-total ert-deftest selecting ^m53-imp4 (S3).  Tracked files only (src/, mod/, tool/run-tests.scm, test/pty-driver.py); it does NOT read docs/.  C delta 0; Scheme delta 0
  )
(group (m54) ; M54 imp-1 the TTY stream ownership audit (docs/m54-plan.org)
  "test/m54/test-m54-imp1.el"                 ; M54 imp-1 audit (docs only; C delta 0, Scheme delta 0): the TTY stream ownership boundary.  S1 re-measures the brief.org section 4.3 surface (src/term.c 6,078 lines / 29 ^DEFUN ( / 4 --tty-* leaf DEFUNs / 33 scm_c_public_ref sites; mod/emacs/tty-output.scm 343 lines; tree-wide scm_c_public_ref 257).  S2 pins the 3 src/termchar.h FILE * streams of struct tty_display_info (input :51, output :53, termscript :61; name, type, and line) and the boundary rule ("one owner, one writer": no Guile port owns a C FILE *).  S3 pins the src/term.c site map as an ordered name list (the output / termscript writes, the flushes, the read handle, the open / close, the init, the size query), the 4 --tty-* leaf DEFUNs, the two M52 writer helpers, and the lifecycle anchors.  S4 pins the (m54) group registration after (m53) and the (m52) / (m53) groups.  S5 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m54-imp1.  Tracked files only; it does NOT read docs/
  "test/m54/test-m54-imp2.el"                 ; M54 imp-2 behavior: the after-write verdict of ONE output write.  S1 resolves (emacs tty-output) through eval-scheme and calls tty-write-verdict for each plain (written len err) pair (done / retry / give-up) and checks the #nil-free string return.  S2 checks the plain tty-out-handle record (plain fixnums only; no port, no FILE *).  S3 checks the seam by name: the m54_tty_write_verdict_scheme dispatcher, the single call site in m52_tty_write_1, the scm_c_public_ref site, and the give-up test.  S4 pins the (m54) group registration after imp-1.  S5 holds the per-group min-count guards and the group-total ert-deftest selecting ^m54-imp2.  Tracked files only; it does NOT read docs/.  The real path is the separate pty case m54-imp2/output-write-verdict-e2e
  "test/m54/test-m54-imp3.el"                 ; M54 imp-3 behavior: the termscript copy decision.  A termscript is a COPY of the terminal output (src/termchar.h :61).  imp-3 moves ONE operation of the copy stream: the after-write DECISION of ONE termscript copy write, REUSING tty-write-verdict (imp-2) through the SAME dispatcher and plain values.  S1 resolves (emacs tty-output) through eval-scheme, calls tty-write-verdict for the copy count pairs (done / retry / give-up), and checks that no twin verdict procedure exists.  S2 checks the plain tty-out-handle built from the copy counts by tty-termscript-copy-handle (Option A of brief.org section 9; plain fixnums only, no port, no FILE *).  S3 checks the seam by name: the reused dispatcher, the ONE new call site in m52_tty_write_1, the new m54_tty_termscript_* helper, the scm_c_public_ref site, and the 10 classified copy sites of brief.org section 5.  S4 pins the (m54) registration after imp-2.  S5 holds the per-group min-count guards and the group-total ert-deftest selecting ^m54-imp3.  Tracked files only; it does NOT read docs/.  The real path is the separate pty case m54-imp3/termscript-copy-e2e
  "test/m54/test-m54-imp4.el"                 ; M54 imp-4 behavior: the input stream TAB policy.  imp-4 moves ONE decision of the src/termchar.h INPUT stream (src/termchar.h :51): the terminal TAB policy UseTabs of ONE tty init (src/term.c :5030).  C keeps the mechanism (tabs_safe_p (fileno (tty->input)) and TabWidth) and passes the two plain values to Scheme; Scheme owns the pure decision tty-tab-verdict (#t 8 -> "tabs", else "spaces").  S1 resolves (emacs tty-output) through eval-scheme and calls tty-tab-verdict for the plain pairs (#t 8 / #t 7 / #f 8 / #f 7) and checks that no twin procedure exists.  S2 checks the seam by name: the m54_tty_tabs_verdict_scheme dispatcher, the ONE call site in init_tty, the scm_c_public_ref site, the C anchors, and the nil fallback that keeps the present C behavior.  S3 pins the (m54) registration after imp-3.  S4 pins the pty case m54-imp4/tab-policy-e2e and the case-count pins.  S5 holds the per-group min-count guards and the group-total ert-deftest selecting ^m54-imp4.  Tracked files only; it does NOT read docs/.  The real path is the separate pty case m54-imp4/tab-policy-e2e
  "test/m54/test-m54-imp5.el"                 ; M54 imp-5 close-out: the re-measured surface of brief.org section 5 (S1: src/term.c 6,214 lines / 29 ^DEFUN ( / 4 --tty-* leaf DEFUNs / 36 scm_c_public_ref sites; mod/emacs/tty-output.scm 454 lines; tree-wide scm_c_public_ref 260), the (m54) group registration after imp-4 and the test/pty-driver.py 26-case total pin (S2: 4 checks), the per-group min-count guards and the in-process group-total ert-deftest selecting ^m54-imp5 (S3).  Tracked files only (src/, mod/, tool/run-tests.scm, test/pty-driver.py); it does NOT read docs/.  C delta 0; Scheme delta 0
  )
(group (m55) ; M55 imp-1 the standalone loader runtime registration audit; M55 imp-2 the minimal Scheme registration; M55 imp-3 the standalone load check; M55 imp-4 the source-reading load path; M55 imp-5 the close-out (docs/m55-plan.org)
  "test/m55/test-m55-imp1.el"                 ; M55 imp-1 audit (docs only; C delta 0, Scheme delta 0): the standalone loader runtime registration boundary.  S1 re-measures the brief.org section 4 surface (mod/emacs/loader.scm 1190 lines / 74 (symbol-function 'X) apply matches / 18 symbol-fbound? line-count / 14 set-symbol-function! line-count / 7 FIX-*-guilemacs line-count; mod/emacs/reader.scm 2,021 lines; prelude/load.scm 265 lines / 70 (use-modules ...) line-count / 31 (init-...-registrations) line-count).  S2 pins the cell map (brief.org section 5) in call order: the loader POLICY cells length, find-file-name-handler; the reachable runtime cells get-load-suffixes, append, symbol-value, car, expand-file-name, file-directory-p, cdr; then the elisp compiler (lookup-language 'emacs-elisp) STAYS C.  The REAL path is a plain `guile -L mod' subprocess that loads a real .el file through the Scheme loader: it derives the first empty cell (get-load-suffixes; the raise is wrong-type-arg), and the deep trace supplies rows 3 ... 9 with tolerant Scheme stubs and pins the imp-4 end state (the load no longer stops at row 10; it COMPLETES).  S3 pins the registration site prelude/load.scm and the 2 loader set-symbol-function! cells (load, autoload-do-load), in module-before-init order.  S4 pins the (m55) group registration after (m54) and (m54) stays present.  S5 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m55-imp1.  Tracked files only (mod/, prelude/, tool/run-tests.scm); it does NOT read docs/.  A missing guile binary is an explicit INFO skip, never a pass
  "test/m55/test-m55-imp2.el"                 ; M55 imp-2 behavior (brief.org sections 5 and 8): the minimal Scheme runtime registration.  S1 checks the 7 new set-symbol-function! cells in init-loader (mod/emacs/loader.scm), in call order: get-load-suffixes, append, symbol-value, car, expand-file-name, file-directory-p, cdr; and the 2 new pure-Scheme procedures elisp-loader-expand-file-name (a path join) and elisp-loader-file-directory-p (a stat), with no C-backed (emacs fileio) cell and no C leaf.  S2 runs the REAL path: a plain `guile -L mod -c' subprocess calls init-loader (the registration site) and then elisp-load on a real .el file.  It DERIVES that no reachable cell is empty; M55 imp-4 removed row 10 from the route, so the load no longer stops there -- the check pins the imp-4 end state (the LOAD-OK outcome).  S3 pins the re-measured surface (loader.scm 1190 lines / 74 (symbol-function 'X) apply matches / 18 symbol-fbound? / 14 set-symbol-function! / 7 FIX-*-guilemacs; reader.scm 2,021; prelude/load.scm 265).  S4 pins the registration: the (m55) group, the imp-2 file, and the group order after (m54).  S5 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m55-imp2.  Tracked files only (mod/, prelude/, tool/run-tests.scm); it does NOT read docs/.  A missing guile binary is an explicit INFO skip, never a pass
  "test/m55/test-m55-imp3.el"                 ; M55 imp-3 behavior (brief.org section 1): the standalone load check.  It proves the imp-2 end state by measurement on the REAL path; C delta 0 and no mod/ or prelude/ line changes.  S1 runs a plain `guile -L mod -c' subprocess that calls (use-modules (emacs loader)) and (use-modules (emacs-elisp runtime)), then init-loader (the registration site), then elisp-load on a real .el file; it DERIVES that no reachable cell is empty (the FIRST empty cell of the ordered list is NONE).  M55 imp-4 removed row 10 from the route, so the load no longer stops there; the check pins the imp-4 end state (the LOAD-OK outcome).  S2 pins the ordered cell list: the 7 set-symbol-function! cells (get-load-suffixes, append, symbol-value, car, expand-file-name, file-directory-p, cdr) in call order (rows 3 ... 9) in mod/emacs/loader.scm.  S3 pins the re-measured surface (loader.scm 1190 lines / 74 (symbol-function 'X) apply matches / 18 symbol-fbound? / 14 set-symbol-function! / 7 FIX-*-guilemacs; reader.scm 2,021; prelude/load.scm 265).  S4 pins the registration: the (m55) group holds the imp-3 file, the group comes after (m54), and it holds the imp-1 and imp-2 files.  S5 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m55-imp3.  Tracked files only (mod/, prelude/, tool/run-tests.scm); it does NOT read docs/.  A missing guile binary is an explicit INFO skip, never a pass
  "test/m55/test-m55-imp4.el"                 ; M55 imp-4 behavior (brief.org section 1): the source-reading load path.  imp-4 removes row 10 (the elisp compiler) from the plain `guile' load path: load-elisp and load-elisp-full take a source-reading branch when (lookup-language 'emacs-elisp) raises (cr.org M2), and init-loader installs the reader cells (intern, concat, substring) and a minimal Scheme elisp evaluator for the eval cell.  S1 runs the REAL path (a plain `guile -L mod -c' subprocess calls init-loader then elisp-load on a real .el file): it derives that no reachable cell is empty (the ordered 11-cell list is FIRST-EMPTY:NONE), pins the LOAD-OK outcome, and pins the OBSERVABLE SIDE EFFECT (the file setq-s a marker string read back after the load; the check FAILS when the loader only READS the file and does NOT run it).  S2 pins the route (the compiler-absent test, the source reader) and the 4 reader/eval cells (intern, concat, substring, eval) in call order with symbol-fbound? guards; it also pins that the evaluator defines the minimal special forms and is not the compiler.  S3 pins the re-measured surface (loader.scm 1190 lines / 74 (symbol-function 'X) apply matches / 18 symbol-fbound? / 14 set-symbol-function! / 7 FIX-*-guilemacs; reader.scm 2,021; prelude/load.scm 265).  S4 pins the registration: the (m55) group holds the imp-4 file, after (m54), and holds imp-1/imp-2/imp-3.  S5 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m55-imp4.  Tracked files only (mod/, prelude/, tool/run-tests.scm); it does NOT read docs/.  A missing guile binary is an explicit INFO skip, never a pass
  "test/m55/test-m55-imp5.el"                 ; M55 imp-5 close-out: the re-measured surface of brief.org section 4 (S1: loader.scm 1,187 lines / 74 (symbol-function 'X) apply matches / 18 symbol-fbound? / 14 set-symbol-function! / 7 FIX-*-guilemacs; reader.scm 2,021 lines; prelude/load.scm 265 lines / 70 ^(use-modules / 31 ^(init-...-registrations)), the real-path re-check (S1b: a plain `guile -L mod -c' subprocess calls init-loader then elisp-load on a real .el file and pins the LOAD-OK outcome plus the observable side effect; 2 checks), the (m55) group registration after imp-4 and the advisory tool/m55-audit.sh load line (S2: 6 checks; the audit helper is untracked, so its check is an INFO skip when absent), the per-group min-count guards and the in-process group-total ert-deftest selecting ^m55-imp5 (S3).  Tracked files only (mod/, prelude/, tool/run-tests.scm); the advisory tool/m55-audit.sh is untracked, so its check is an INFO skip when absent; it does NOT read docs/.  C delta 0; Scheme delta 0
  )
(group (m56) ; M56 imp-1 the deferred M54 input-stream descriptor audit; M56 imp-2 the real-path PTY check (docs/m56-plan.org)
  "test/m56/test-m56-imp1.el"                 ; M56 imp-1 audit (docs only; C delta 0, Scheme delta 0): the deferred M54 input-stream descriptor rows (add_keyboard_wait_descriptor, get_tty_size, init_baud_rate).  S1 re-measures the brief.org section 3 surface (the base 30213d139 is an ANCESTOR of HEAD; src/term.c 6,214 lines / 29 ^DEFUN ( / 4 --tty-* leaf DEFUNs / 36 scm_c_public_ref sites; tree-wide scm_c_public_ref 260; mod/emacs/tty-output.scm 454 lines; the 3 src/termchar.h FILE * streams at :51/:53/:61; test/pty-driver.py 26 cases).  S2 pins the row map: the 3 C1 rows, their C definitions (src/process.c:8361, src/sysdep.c:1342 + policy :1293, src/sysdep.c:425), their src/term.c sites, and the tracked C evidence per class -- row 1 and row 3 STAYS C (C state keyed on the descriptor / the termios read on the C descriptor); row 2 keeps the C wrapper only (its DECISION already moved to Scheme `tty-size', M43 imp-5, and the descriptor read stays C; a passthrough is not a port).  S3 runs the real tty init path: the built src/emacs on a real PTY through test/pty-driver.py (group m53-imp3); a missing python3 / built src/emacs / PTY is an explicit INFO skip, never a pass.  S4 pins the (m56) group registration after (m55) and that (m55) stays present.  S5 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m56-imp1.  Tracked files only (src/, mod/, tool/run-tests.scm, test/pty-driver.py); it does NOT read docs/
  "test/m56/test-m56-imp2.el"                 ; M56 imp-2 behavior (brief.org sections 1, 5): the real-path PTY check.  It adds ONE PTY case m56-imp2/tty-init-e2e to test/pty-driver.py that boots the built src/emacs on a real PTY and drives the terminal, so the C `init_tty' runs and therefore the three C1 rows (add_keyboard_wait_descriptor, get_tty_size, init_baud_rate).  C delta 0; Scheme delta 0.  Row 3 (init_baud_rate) has NO plain Scheme observable, so the case does NOT assert a baud value (brief.org section 4.1); it pins the WHOLE path by the terminal's live behaviour (brief.org section 4.2): the (emacs gobble) read path reports its counts; the write path writes real bytes to the PTY (BEGIN marker / out bytes / END marker) and reports the byte count; and the driver resizes the PTY after READY so a size read after the gate follows the resize and proves a LIVE size query.  S1 pins the case wiring in test/pty-driver.py (name, group, M56_IMP2_CASES tuple, CASES / GROUPS entries, the selftest group-count and total-case-count 26 pins, the output span and its pinned bytes, and the resize).  S2 runs the REAL path (python3 test/pty-driver.py --selftest, and the case on the built src/emacs on a real PTY); a missing python3 / built src/emacs / PTY is an explicit INFO skip, never a pass.  S3 pins the (m56) group registration after test-m56-imp1.el.  S4 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m56-imp2.  Tracked files only (test/pty-driver.py, tool/run-tests.scm); it does NOT read docs/
  "test/m56/test-m56-imp3.el"                 ; M56 imp-3 CLOSE-OUT: the re-measured surface of brief.org section 4 (S1: Group A the M55 loader surface -- loader.scm 1,187 lines / 74 (symbol-function 'X) matches / 18 symbol-fbound? / 14 set-symbol-function! / 7 FIX-*-guilemacs; reader.scm 2,021 lines; prelude/load.scm 265 lines / 70 ^(use-modules / 31 ^(init-...-registrations); Group B the TTY surface -- src/term.c 6,214 lines / 29 ^DEFUN / 4 --tty-* leaf DEFUNs / 36 scm_c_public_ref sites; tree-wide scm_c_public_ref 260 over src/*.[chm]; mod/emacs/tty-output.scm 454 lines; the 3 src/termchar.h FILE * streams at :51/:53/:61; test/pty-driver.py 26 cases), the registration (S2: the (m56) group holds this corpus after test-m56-imp2.el, the base dc8af1488 is an ANCESTOR of HEAD via git merge-base --is-ancestor, and the untracked advisory tool/m56-audit.sh load line is an INFO skip when absent), the real-path re-check (S3: python3 test/pty-driver.py --selftest prints SELFTEST OK, and the case m56-imp2/tty-init-e2e PASSES on the built src/emacs on a real PTY; a missing python3 / built src/emacs / PTY is an explicit INFO skip, never a pass), and the per-group min-count guards plus the in-process group-total ert-deftest selecting ^m56-imp3 (S4).  Tracked files only (src/, mod/, prelude/, tool/run-tests.scm, test/pty-driver.py); the advisory tool/m56-audit.sh is untracked, so its check is an INFO skip when absent; it does NOT read docs/.  C delta 0; Scheme delta 0
  )
(group (m57) ; M57 imp-1 the C2 TTY FILE * stream ownership audit; M57 imp-5 the close-out (docs/m57-plan.org)
  "test/m57/test-m57-imp1.el"                 ; M57 imp-1 audit (docs only; C delta 0, Scheme delta 0): Candidate C2, the ownership of the 3 src/termchar.h FILE * streams (input :51, output :53, termscript :61).  S1 re-measures the brief.org section 3 surface (the base e2423fcb0 is an ANCESTOR of HEAD; src/term.c 6,214 lines / 29 ^DEFUN ( / 4 --tty-* leaf DEFUNs / 36 scm_c_public_ref sites; tree-wide scm_c_public_ref 260 over src/*.[ch]; mod/emacs/tty-output.scm 454 lines; the 3 src/termchar.h FILE * streams at :51/:53/:61; test/pty-driver.py 26 cases).  S2 pins the row map grouped by stream: the OUTPUT path (the termcap fwrite / the space putc / the M52 leaf write / the fflush / the clearerr), the TERMSCRIPT path (the copy fwrite / putc, the NULL guard, the M52 copy write, the close), and the INPUT path (the read handle / the descriptor reads add_keyboard_wait_descriptor / get_tty_size / init_baud_rate / tabs_safe_p / the open / close / the NULL clears), plus the boundary rule do-not-give-scheme-a-C-descriptor by name in the TRACKED C source.  Every path STAYS C (the C FILE * / descriptor / C state keyed on them; a passthrough is not a port).  S3 runs the real tty init path: the built src/emacs on a real PTY through test/pty-driver.py (group m56-imp2); a missing python3 / built src/emacs / PTY is an explicit INFO skip, never a pass.  S4 pins the (m57) group registration after (m56) and that (m56) stays present.  S5 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m57-imp1.  Tracked files only (src/, mod/, tool/run-tests.scm, test/pty-driver.py); it does NOT read docs/
  "test/m57/test-m57-imp5.el"                 ; M57 imp-5 CLOSE-OUT (brief.org sections 4.1 and 5; C delta 0, Scheme delta 0; the checked files are src/term.c, src/termchar.h, mod/emacs/tty-output.scm, test/pty-driver.py, tool/run-tests.scm).  It records and re-checks the close-out of Candidate C2, the ownership of the 3 src/termchar.h FILE * streams (input :51, output :53, termscript :61).  The C2 result: the audit is A1, the port is A2, 21 stream paths STAYS C (8 OUTPUT, 5 TERMSCRIPT, 8 INPUT), MOVE 0, NOT PROVEN 0; C2 is EXHAUSTED.  S1 re-measures the brief.org section 3 surface (the base e2423fcb0 is an ANCESTOR of HEAD; src/term.c 6,214 lines / 29 ^DEFUN ( / 4 --tty-* leaf DEFUNs / 36 scm_c_public_ref sites; tree-wide scm_c_public_ref 260 over src/*.[ch]; mod/emacs/tty-output.scm 454 lines; the 3 src/termchar.h FILE * streams at :51/:53/:61; test/pty-driver.py 26 cases; test/m57/test-m57-imp1.el 483 lines).  S2 pins the C2 result against the TRACKED C source: the row map grouped by stream (the OUTPUT write / flush / clearerr / close / open / GPM sites, the TERMSCRIPT copy write / putc / NULL guard / close, the INPUT handle / descriptor registration / size query / baud query / tab policy / NULL clear / open / close) and the boundary rule by name ("no Guile port owns a FILE *", src/term.c :5484).  Every path STAYS C.  S3 runs the real path (python3 test/pty-driver.py --selftest prints SELFTEST OK, and the case m56-imp2/tty-init-e2e PASSES on the built src/emacs on a real PTY; a missing python3 / built src/emacs / PTY is an explicit INFO skip, never a pass).  S4 pins the (m57) group registration: this corpus AFTER test-m57-imp1.el, the imp-1 corpus kept, and (m56) present; the base e2423fcb0 is an ANCESTOR of HEAD; the UNTRACKED advisory tool/m57-audit.sh is not a dependency.  S5 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m57-imp5.  Tracked files only (src/, mod/, tool/run-tests.scm, test/pty-driver.py); it does NOT read docs/
  )
(group (m58) ; M58 imp-1 the remaining TTY policy surface audit; M58 imp-2 the real-path PTY face-appearance check (docs/m58-plan.org)
  "test/m58/test-m58-imp1.el"                 ; M58 imp-1 audit (docs only; C delta 0, Scheme delta 0): the remaining movable TTY policy and state paths in src/term.c, plus the C3 elisp-compiler boundary re-check.  S1 re-measures the brief.org section 3 surface (the base fca28d3be is an ANCESTOR of HEAD; src/term.c 6,214 lines / 29 ^DEFUN ( / 4 --tty-* leaf DEFUNs / 36 scm_c_public_ref sites; tree-wide scm_c_public_ref 260 over src/*.[ch]; mod/emacs/tty-output.scm 454 lines; the 3 src/termchar.h FILE * streams at :51/:53/:61; test/pty-driver.py 26 cases (re-pinned by M58 imp-2)).  S2 pins the row map of brief.org section 5 by group, against the TRACKED source, one check per group: group A the face-appearance policy (turn_on_face / turn_off_face / tty_capable_p, a MOVE candidate), group B the color-mode policy (tty_setup_colors / set_tty_color_mode / tty-display-color-cells, a MOVE candidate), group C the cost policy (string_cost / calculate_ins_del_char_costs / calculate_costs / cmcostinit, STAYS C), group D the init policy (maybe_fatal / scroll_region_ok / init_baud_rate; the UseTabs verdict already moved, the ins/del verdicts NOT PROVEN), group E the C-mechanism blocks (tty_write_glyphs / term_get_fkeys / tty_menu_activate / tty_send_additional_strings, STAYS C), group F the read-only accessors (tty-no-underline / tty-top-frame MOVE candidates, tty-frame-list-z-order / suspend-tty / resume-tty STAYS C, tty--set-output-buffer-size / tty--output-buffer-size NOT PROVEN), and group G the C3 elisp-compiler boundary (src/emacs.c resolves the (emacs-elisp spec) module; loader.scm / runtime.scm call (lookup-language 'emacs-elisp); STAYS C without a safe handle first), plus the boundary rule do-not-give-scheme-a-C-descriptor by name in the TRACKED C source.  S3 runs the real tty init path: the built src/emacs on a real PTY through test/pty-driver.py (group m56-imp2); a missing python3 / built src/emacs / PTY is an explicit INFO skip, never a pass.  S4 pins the (m58) group registration after (m57) and that (m57) stays present.  S5 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m58-imp1.  Tracked files only (src/, mod/, tool/run-tests.scm, test/pty-driver.py); it does NOT read docs/
  "test/m58/test-m58-imp2.el"                 ; M58 imp-2 EVIDENCE (C delta 0, Scheme delta 0): the ONE real-path PTY check of the TTY face-appearance policy (Group A: turn_on_face / turn_off_face / tty_capable_p, src/term.c).  It adds ONE PTY case m58-imp2/face-appearance-e2e to test/pty-driver.py and a child PRELUDE hook that runs before the gate read; the prelude inserts BEGIN + propertize "X" 'face 'bold + END into the buffer the selected window already shows and forces a real redisplay, so the C hub runs.  NO MOVE: the Group A decision stays in C.  T1 pins the C trigger (the two static signatures at :2245 / :2327, tty_capable_p at :2370, the SIX glyph-writer callers at :1033 / :1051 / :1095 / :1110 / :1171 / :1202, the bold gate / exit, and the boundary rule "no Guile port owns a FILE *").  T2 pins the case, the m58-imp2 group, the case-count pins (TOTAL 26 = the SUM of the 17 group pins) and the span_requires shape (the measured terminfo "bold" byte; an absent capability is an explicit INFO skip, a capable host that emits no byte FAILS; NO hand-copied output_span_bytes).  T3 runs the real path (PASS, or an explicit INFO skip; a bad run retries once).  T4 pins the (m58) registration after the imp-1 line.  T5 pins the cross-corpus re-pin of test-m58-imp1.el (25 -> 26).  T6 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m58-imp2.  Tracked files only (src/, mod/, test/pty-driver.py, tool/run-tests.scm, test/m58/test-m58-imp1.el); it does NOT read docs/
  "test/m58/test-m58-imp3.el"                 ; M58 imp-3 the Group A MOVE (brief.org steps 1 ... 5; C delta +267 / -118, net +149 lines -- no line drop is claimed; Scheme delta +184 / -1).  It moves the face-appearance DECISION of turn_on_face, turn_off_face, and tty_capable_p to (emacs tty-output).  C keeps every mechanism: the struct face field reads, MAY_USE_WITH_COLORS_P, the TS_* / TF_* / TN_* reads, face_tty_specified_color, the strcmp of the two exit sequences, tparam, the OUTPUT / OUTPUT1 / OUTPUT_IF macros, tty_toggle_highlight, the standout_mode clear, and the FILE *.  U1 pins the 3 pure procedures in mod/emacs/tty-output.scm: their definitions, their #:export entries, their purity (no leaf call, no emit, no set!), and the published 5-step protocol.  U2 runs the REAL behaviour: a plain `guile -L mod -c' subprocess calls the 3 procedures with plain fixnums and the check compares the returned step lists and verdicts with the C semantics they replaced (order: reverse first, then bold / italic / underline / strike-through, then fg / bg / underline-color; the off decision: me + clear-standout before the orig-pair reset; the 7 TTY_CAPABLE_P_TRY rows as one table).  A missing guile is an explicit INFO skip, never a pass.  U3 pins the C wiring: the 3 m58_*_scheme dispatcher resolve sites, the step walker and the mechanisms that STAY C, the 7 non-parameterized face keys in m52_caps[], the ABSENCE of the 4 tparam keys, and the DELETED inline decision (TTY_CAPABLE_P_TRY is gone).  U4 pins the 5 real-path PTY cases (face-off-e2e, face-italic-e2e, face-underline-e2e, face-color-e2e, capable-p-e2e) in test/pty-driver.py, the (m58-imp3) group, the case-count pins (TOTAL 31 = the SUM of the 18 group pins), the distinct marker spans, and the ORDERED needle run of the color case.  U5 pins the cross-corpus re-pins in the older corpora (src/term.c 6,363 lines / 39 scm_c_public_ref / tree-wide 263; mod/emacs/tty-output.scm 637 lines; the hub signature lines 2372 / 2495; the PTY total 31; the imp-1 Group A row).  U6 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m58-imp3.  Tracked files only (src/, mod/, test/, tool/run-tests.scm); it does NOT read docs/.  The negative control of the MOVE: with the 3 Scheme procedures forced to return an empty step list, NO face byte reaches the PTY (bold / italic / underline / color all vanish), which proves C no longer holds the decision
  "test/m58/test-m58-imp4.el"                 ; M58 imp-4 the Group B color-mode MOVE (brief.org sections 1, 5, 6, 7, and 8; C delta +91 / -29, net +62 lines -- no line drop is claimed; Scheme delta +46 / -1).  It moves the mode canonicalization and the -1 / 0 / 8 scheme choice of tty_setup_colors, and the change gate of set_tty_color_mode, to (emacs tty-output): tty-color-mode-tag and tty-color-mode-changed-p.  C keeps every mechanism: the cap strings (with the TERMINFO variants), every TN_* and TS_* write, the static default slots, the param_alist and tty-color-mode-alist resolve, the raw previous_color_mode store, safe_calln, and the FILE * streams.  T1 pins the C sites that stay C, the 2 DELETED inline decisions, the gate, the raw store, the ONE caller (the frame switch), and the boundary rule.  T2 pins the new PTY case m58-imp4/color-mode-e2e (value "8 0 8", two tty frames, 3 switches, the narrow info_report_prefix skip, TOTAL 32 = the SUM of the 19 group pins).  T3 runs the real path (PASS or an explicit INFO skip).  T4 pins the (m58) registration after the imp-3 line.  T5 pins the cross-corpus 31 -> 32 re-pins and that this group comment holds the MEASURED delta (repin/group-comment-measured).  T6 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m58-imp4.  T7 pins the 2 pure procedures and their semantics through guile -L mod, plus the DIRECT C-vs-Scheme tag cross-check.  T8 pins the 2 dispatcher resolve sites, the tag runner, the STAYS C list, and the raw store.  T9 re-pins the measured surface (src/term.c 6,425 lines / 41 scm_c_public_ref / tree-wide 265; mod/emacs/tty-output.scm 682 lines), records the negative control (tty-color-mode-changed-p forced to 0 gives "8 8 8"), and pins that the 3 limits are written down (record/limits-written-down).  The 3 limits are written down here too: L3 no C fallback -- a missing mod/ on the load path turns the color mode OFF with no error and no message, and the first scm_c_public_ref runs inside redisplay at the first frame switch, so a load failure aborts redisplay (proven on THIS host only); L4 the extra crossing is not measured -- one scm_call_1 and one scm_call_2 join the redisplay path, once per frame switch and not per glyph, and no timing was taken; L5 a tag that drifts from the Scheme names emits nothing and raises no error -- the check m58-imp4/scheme/tag-strings-match-C now compares the 2 sides DIRECTLY (it derives the C tag names from src/term.c and the Scheme tag names from a guile subprocess).  Tracked files only (src/, mod/, test/, tool/run-tests.scm); it does NOT read docs/
  "test/m58/test-m58-imp5.el"                 ; M58 imp-5 the CLOSE-OUT (brief.org sections 4 ... 10; C delta 0, Scheme delta 0).  No C and no Scheme policy moves: it re-measures the surface, runs the gates, and records ONE measured verdict for each of the 3 open MOVE-candidate rows of the imp-1 row map.  The 3 verdicts, MEASURED at HEAD: row A the calculate_costs TS_repeat test (src/term.c :1502) STAYS C (RPov has 3 sites and no reader -- the 2 writes at :1506 / :1508 and the declaration at src/termchar.h :182; the cost inputs per_line_cost / string_cost are C termcap calls (tputs)); row B tty-no-underline (:2882) STAYS C (one C field write behind a C type test -- the observable is the missing underline byte, but no plain value crosses that C would not compute itself, so a port is a passthrough, not a port: passthrough-leaf-is-not-a-port); row C tty-top-frame (:2900) STAYS C (a pure read of a C struct member -- a Lisp_Object field; it computes nothing and it needs the C struct itself).  The row map CLOSES as MOVE 5 (Group A tty-face-on-steps / tty-face-off-steps / tty-capable-p, Group B tty-color-mode-tag / tty-color-mode-changed-p), STAYS C 3 (the 3 rows above), NOT PROVEN 5 (no observable: the 3 Group D rows scroll_region_ok / line_ins_del_ok / char_ins_del_ok and the 2 Group F rows tty--set-output-buffer-size / tty--output-buffer-size), and Group G (the elisp compiler) STAYS C (src/emacs.c resolves the (emacs-elisp spec) module; mod/emacs/loader.scm tests (lookup-language 'emacs-elisp)).  It re-measures the surface at HEAD: src/term.c 6,425 lines / 29 ^DEFUN ( / 4 --tty-* leaf DEFUNs / 41 scm_c_public_ref sites; tree-wide scm_c_public_ref 265 over src/*.[ch]; mod/emacs/tty-output.scm 682 lines; test/pty-driver.py 32 cases in 19 groups (NO new case); test/m58 5 corpus files.  Gates at HEAD a583dc86f (2026-10-19): --filter=m58 147 found / 147 pass / 0 fail; --filter=m57 67 found / 67 pass / 0 fail; PTY m58-imp2 PASS, m58-imp3 5/5 PASS, m58-imp4 PASS "8 0 8"; --selftest SELFTEST OK (32 cases); m58-plan-lint.sh 0 STALE, exit 0; m58-audit.sh PASS.  It pins: V1 the 3 row verdicts (site line, key C text, measured fact, token and reason); V2 the row-map close; V3 the surface re-measure; V4 the registration; V5 the real path of the 3 EXISTING PTY groups (an absent src/emacs, python3, or PTY is an explicit INFO skip, never a pass); V6 the per-group min-count guards and the group total.  The record files are docs/m58-plan.org (section 13) and docs/kb.org (m58-close-out-row-verdicts), plus milestone.org and m58-imp5-commit-msg.txt.  Tracked files only (src/, mod/, test/, tool/run-tests.scm); it does NOT read docs/
  )
(group (m59) ; M59 imp-1 the src/xfaces.c face surface audit (docs/m59-plan.org)
  "test/m59/test-m59-imp1.el"                 ; M59 imp-1 AUDIT (docs only; C delta 0, Scheme delta 0).  It measures the remaining C surface of src/xfaces.c, classes every DEFUN, and names ONE fresh MOVE candidate plus a runner-up.  S1 re-measures the brief.org section 2 surface (the base e9f87b051 is an ANCESTOR of HEAD; src/xfaces.c 7,741 lines / 33 ^DEFUN ( / 2 scm_c_public_ref LINES / 8 guile lines / 21 scm_* lines (a LINE count, like grep -c); tree-wide scm_c_public_ref 267 OCCURRENCES over src/*.[ch]; these 5 numbers were re-pinned by M59 imp-4 at e9eb77e39 (imp-3 moved the DEFUN to :4197; imp-4 moved bitmap-spec-p to :843 and added the 2nd scm_c_public_ref LINE; M59 imp-6 corrected this stale comment, cr.org F5); test/pty-driver.py 32 cases (NO new case); test/m59/ present).  S2 pins the row map: the NAMED candidate face-attribute-relative-p (:4173 ... :4193 at imp-1, :4197 after the M59 imp-3 MOVE: the Qunspecified / QCignore_defface test, the QCheight branch, the FIXNUMP return, plus the imp-3 dispatcher and its 2 resolve strings) with 0 internal C callers (only the EXFUN at src/globals.h :5226); the RUNNER-UP bitmap-spec-p (:814 after the MOVE) with its 5 C callers at :878 / :1401 / :1915 / :2885 / :3584; the 5 MOVE rows (4 fresh plus the ALREADY LANDED color-values-from-color-spec, which returns guile_parse_color_spec at :1047 after the MOVE); the class counts MOVE 5 / STAYS C 26 / NOT PROVEN 2 = 33 (rule 5.6 of brief.org: merge-face-attribute :4218 calls the Lisp engine through safe_calln at :2281, and color-distance :4788 reads a struct frame at :4800, a C hook at :4782 / :4790, and the metric at :4801, so both rows are NOT PROVEN; the corpus pins both blockers); one STAYS C witness per class reason in the TRACKED C source (the face-cache read lface_equal_p (XVECTOR (lface1)->contents), the 2 C statics next_lface_id / font_sort_order[4], the C FILE * of x-load-color-file, the C hook defined_color_hook); plus the boundary rule do-not-give-scheme-a-C-descriptor by name in the TRACKED C source ("no Guile port owns a FILE *", src/term.c :5682 -- the M58 plan cite :5484 is STALE).  The 2 rows that move against review-m59-imp1-scope.org section 3.3 are internal-lisp-face-equal-p (:4498) and internal-lisp-face-empty-p (:4524): both read the C lface vector from the frame face cache, so both STAYS C.  S3 runs the real path: test/pty-driver.py --selftest SELFTEST OK and the EXISTING case m56-imp2/tty-init-e2e on the built src/emacs on a real PTY; a missing python3 / built src/emacs / PTY is an explicit INFO skip, never a pass.  S4 pins the (m59) group registration after (m58) and that (m58) stays present.  S5 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m59-imp1.  Tracked files only (src/, tool/run-tests.scm, test/pty-driver.py); it does NOT read docs/.  The advisory tool/m59-audit.sh and tool/m59-plan-lint.sh are NOT written in imp-1
  "test/m59/test-m59-imp2.el"                 ; M59 imp-2 EVIDENCE (C delta 0, Scheme delta 0): the ONE real-path check for face-attribute-relative-p.  The (m59) group has NO prelude key, so this group runs through run-tests-loadup-emacs: the corpus runs INSIDE the built src/emacs, so a direct call to the subr is the REAL path (no child process, no PTY case; the test/pty-driver.py case pin stays 32).  S1 pins the observable: the 3 milestone values (:height 1.5 -> t, :height 12 -> nil, :foreground unspecified -> t), 5 branch controls that tell the 3 C branches apart (:foreground "red" -> nil, :height 1 -> nil, :height unspecified -> t, :height :ignore-defface -> t, :foreground 'ignore-defface -> nil -- MEASURED: QCignore_defface is the KEYWORD :ignore-defface, src/xfaces.c :7468, so the SYMBOL takes branch 3), and 2 subr checks (subrp is non-nil; a 1-argument call signals wrong-number-of-arguments).  S2 re-measures the C row: the DEFUN line (:4173 at imp-2, :4197 after the M59 imp-3 MOVE), the 3 body tests (now the 3 plain booleans plus the dispatcher call), and 0 internal C callers -- scoped to src/xfaces.c, because a tree-wide count over src/*.[ch] is 2 on a built tree (the generated, untracked src/globals.h holds the EXFUN at :5226; NOT pinned).  S3 pins this registration: exactly 1 line, after the imp-1 line, imp-1 kept, (m58) before (m59).  S4 holds the per-group min-count guards and the in-process group-total ert-deftest selecting ^m59-imp2.  Tracked files only (src/, tool/run-tests.scm); it does NOT read docs/.  The 3 values were MEASURED on 2026-10-19 at HEAD c5ad1632a
  "test/m59/test-m59-imp3.el"                 ; M59 imp-3 the MOVE (C delta +29 / -6, net +23 lines -- no line drop is claimed; Scheme delta +45 lines in mod/emacs/faces.scm, prelude/load.scm +1 line).  It moves the 3-branch DECISION of face-attribute-relative-p (src/xfaces.c :4187 ... :4192 at the imp-2 HEAD) to (emacs faces): the pure procedure face-attribute-relative-verdict takes 3 plain booleans and returns 1 plain boolean.  C keeps the DEFUN, the doc string, the 3 keyword symbols, and the 3 type tests (bool a = EQ (value, Qunspecified) || EQ (value, QCignore_defface), bool b = EQ (attribute, QCheight), bool c = FIXNUMP (value)); the new dispatcher m59_face_attribute_relative_p_scheme resolves the Scheme binding and crosses once per call.  The inline decision is DELETED (a passthrough is not a port).  U1 pins the new module and the ONE ordered (use-modules (emacs faces)) load line; U2 runs the REAL path -- 8 calls of the subr, one per truth-table row, plus the 5 imp-2 controls; U3 pins the C wiring (the dispatcher, its 2 resolve strings, SCM_CALL_3, the 3 type tests, the DELETED inline decision, 33 ^DEFUN ( LINES, 1 scm_c_public_ref LINE in src/xfaces.c, 266 tree-wide OCCURRENCES) and the absence of a C fallback; U4 pins the negative control; U5 pins this registration after the imp-2 line; U6 holds the min-count guards and the group total.  Negative control (MEASURED on this host, NO rebuild): the exported name was renamed for one run, so scm_c_public_ref fails at the first call and the subr SIGNALS (exact text, MEASURED on this host: misc-error: ("public-lookup" "No variable bound to ~s in module ~s" (face-attribute-relative-verdict (emacs faces)) #f)) -- it does NOT return a default verdict; the edit was reverted and the 3 values returned t / nil / t.  The live Scheme half of the control rebinds the module binding with module-set! and the verdict flips t -> #f.  The 4 limits: L1 no C fallback -- an absent module or a renamed binding makes the subr signal at the first call; L2 the extra crossing is not measured -- one scm_c_public_ref (once) plus one SCM_CALL_3 per call join the path, no timing was taken; L3 the C delta is POSITIVE (+29 / -6, MEASURED) and no line drop is claimed; L4 no new PTY case -- the test/pty-driver.py pin stays 32.  Tracked files only (src/, mod/, prelude/, tool/run-tests.scm); it does NOT read docs/.  The values were MEASURED on 2026-10-19 at HEAD 2841bc4db
  "test/m59/test-m59-imp4.el"                 ; M59 imp-4 the MOVE of the RUNNER-UP (C delta +48 / -15, net +33 lines -- no line drop is claimed; the deleted accept rule is 2 lines of arithmetic and the dispatcher plus its comment add the rest).  Scheme delta +23 lines (+24 / -1) in mod/emacs/faces.scm; prelude/load.scm unchanged (266 lines, 1 (emacs faces) line).  It moves the DECISION of bitmap-spec-p (the accept rule at src/xfaces.c :825 ... :860 at the imp-3 HEAD) to (emacs faces): the pure procedure bitmap-spec-verdict takes 4 plain values (1 boolean, 3 integers) and returns 1 plain boolean.  C keeps the DEFUN, the doc string, Qbitmap_spec_p, the CONSP unpack (XCAR / XCDR), the 5 internal callers, the type tests (STRINGP, CONSP, FIXNUMP on WIDTH / HEIGHT, STRINGP (data)), and the BYTE length SBYTES -- a Scheme (string-length ...) counts characters and answers wrong on a multibyte DATA string.  The inline accept rule is DELETED: no bytes_per_row, no RANGED_FIXNUMP (its 2 bounds are part of the decision), no C copy and no C fallback.  A field that is not of the expected type crosses as -1; the sentinel can only make the verdict false, and a real WIDTH of -1 is a fixnum that fails the 1 <= WIDTH bound.  The new dispatcher m59_bitmap_spec_p_scheme sits inside the HAVE_WINDOW_SYSTEM guard, above the DEFUN, and crosses once per call.  W1 pins the module (2 #:export entries, 2 procedure definitions, purity, 1 load line, 266 prelude lines, and the imp-4 base cite of the deleted C rule); W2 runs the REAL path -- 13 calls of the subr, one per brief.org section 6 row, plus 3 DATA-length controls; W3 pins the C wiring (the dispatcher, the 2 resolve strings, SCM_CALL_4, the type tests and SBYTES that STAY C, the DELETED bytes_per_row rule, the DELETED RANGED_FIXNUMP, 2 scm_c_public_ref LINES in src/xfaces.c, 267 tree-wide OCCURRENCES, the 6 Fbitmap_spec_p OCCURRENCES, 33 ^DEFUN ( LINES), the absence of a C fallback, and a guard that no re-pinned check name keeps a stale count (cr.org F4); W4 pins the negative control; W5 pins this registration after the imp-3 line; W6 holds the min-count guards and the group total.  The 13 rows were MEASURED TWICE on the built src/emacs -- on the C path before the edit and through Scheme after it -- and the two series are EQUAL: t / t / t / t / t / nil / nil / nil / nil / t / nil / nil / nil.  MEASURED correction: (string 1 0) is a TWO-character string, so rows 4 and 5 are EXACT FITS and measure t, not nil; the 3 extra controls (8 3), (9 2) and (1 8) are really too short and measure nil, so the deleted bytes_per_row rule stays covered.  Row 13 needs a 64-bit host: 2147483648 IS a fixnum here, C crosses it, and the Scheme bound rejects it, so the row measures nil and is NOT an INFO skip.  (fboundp 'bitmap-spec-p) = t on this build.  Negative control (MEASURED on this host, NO rebuild): the exported name was renamed for one run, so scm_c_public_ref fails at the first call and the subr SIGNALS (exact text, MEASURED on this host: (error "public-lookup" "No variable bound to ~s in module ~s" (bitmap-spec-verdict (emacs faces)) #<scheme #f>)) -- it does NOT return a default verdict; the edit was reverted and the row returned t.  The live Scheme half of the control rebinds the module binding with module-set! and the verdict flips (#t #f).  The 6 limits: L1 no C fallback -- an absent module or a renamed binding makes the subr signal at the first call; L2 the 5 internal C callers each add one crossing, and no timing was taken; L3 the C delta is POSITIVE (+48 / -15, MEASURED) and no line drop is claimed; L4 no new PTY case -- the test/pty-driver.py pin stays 32; L5 the static SCM slot is the landed M59 idiom -- a static slot is not a GC root, this imp does not change the idiom and does not measure the risk; L6 the row is GUI-only -- the fboundp answer is a property of THIS build, not of the source, and it is recorded with the commit; L7 the W4 live module-set! control runs in a FRESH guile process and proves the Scheme side only -- the dispatcher keeps the procedure object in a static SCM slot, so an in-process module-set! after the first call does not change the object that C holds, and the proof that C holds no copy is the C SOURCE that W3 pins (no bytes_per_row, no RANGED_FIXNUMP, one SCM_CALL_4 per call).  Tracked files only (src/, mod/, prelude/, tool/run-tests.scm); it does NOT read docs/.  The values were MEASURED on 2026-10-19 at HEAD 0a20145d0
  )
(group (m60) ; M60 imp-1 the standalone-load boundary audit (docs/m60-plan.org)  AUDIT (docs only; C delta 0, Scheme delta 0; no file moves).  It measures 3 subjects on the real plain-guile path -- the ordered empty cells, the (language emacs-elisp) registration, and the C bootstrap cells -- and classes every reachable cell MOVE / STAYS C / NOT PROVEN.  Verdict A1 for the audit, A2 for the move.  NAMED candidate: the (language emacs-elisp spec) registration (mod/emacs-elisp/spec.scm :20 ... :26 plus :37, and the prelude patch prelude/load.scm :61 ... :90); blocker = the language object and its only consumer sit in the SAME module, so spec.scm :37 needs the language that :20 defines, and lookup-language does not look in (emacs-elisp spec) (MEASURED: a plain guile -L mod process raises "no such language emacs-elisp" at system/base/language.scm :66).  RUNNER-UP: the provide cell with the features variable (mod/emacs/utils.scm :211 define, :576 install, src/fns.c :6372 DEFVAR_LISP) -- MEASURED observable: lisp/cdl.el loads to the END and (featurep 'cdl) is #t once features is bound; negative control without the bind raises memq on the unbound sentinel.  S1 re-measures the surface of brief.org section 3 (base 3603a6795 is an ANCESTOR of HEAD; src/xfaces.c 7,741 / mod/emacs/loader.scm 1,190 / mod/emacs/reader.scm 2,021 / prelude/load.scm 266 / mod/emacs/faces.scm 70 / mod/emacs-elisp/spec.scm 38 LINES (wc -l); loader.scm 18 symbol-fbound? / 14 set-symbol-function! / 7 FIX-*-guilemacs LINES (grep -c); tree-wide scm_c_public_ref 267 OCCURRENCES over src/*.[ch]; test/mod 6 FILES; mod/emacs-elisp 9 ENTRIES because runtime/ is one entry -- milestone.org section 4 says 8, cr.org F5).  S2 pins the ordered cell list: the 11 GUARDED installs in call order (get-load-suffixes, append, symbol-value, car, expand-file-name, file-directory-p, cdr, intern, concat, substring, eval) with EMPTY-CELLS () MEASURED after init-loader, so the M55 imp-3 result HOLDS; the 2 UNGUARDED cells (load :1146, autoload-do-load :1147); the 4 variable binds (load-path :1128, load-suffixes :1130, load-file-rep-suffixes :1132, load-read-function :1143); the MEASURED stop point cells of 4 REAL lisp/ files (subdirs.el -> normal-top-level-add-to-load-path, cdl.el -> provide, obarray.el -> defconst, hex-util.el -> eval-when-compile) and the FIRST stop that a pure stub can NOT pass: (void-variable obarray-default-size), because elisp-loader-eval has no defvar branch; the provide/require ASYMMETRY (elisp-provide defined at utils.scm :211 and installed at :576, reached only from prelude/load.scm :236; elisp-require appears ONCE, in the #:export list at :26, and is never defined and never installed; 0 set-symbol-function! 'require sites); the features DEFVAR_LISP at src/fns.c :6372.  S3 pins the registration: the lookup-language sites (loader.scm :1086, runtime.scm :773, prelude/load.scm :63), the monkey patch of lookup-language and default-environment in 2 modules each (:78, :79, :89), the C scm_c_resolve_module ("emacs-elisp spec") at src/emacs.c :1639, the spec.scm circularity that makes the verdict A2, and the NARROW catch at :1086 that re-raises any other misc-error.  S4 pins the C bootstrap rows: the module sequence :1639 ... :1643, symbol-desc :1647 / symbol-function :1648, the SCM_CALL_7 emacs! call at :1672 with the 6 accessor names plus Qnil, and the defsubr wave syms_of_fns :1681 / syms_of_xfaces :1689 / syms_of_keyboard :1697.  S5 pins this group registration: after (m59), (m59) kept, no prelude key.  S6 holds the 5 per-group min-count guards and the in-process group-total ert-deftest (36 tests).  HOST STATE CORRECTED (cr.org F4): the tree IS built -- config.status, src/Makefile and src/emacs are PRESENT (measured 2026-10-20), so an --filter that matches no group is a FALSE GREEN, not an INFO skip; the carry-forward rule now reads "the (m60) group and the corpus did not exist", and imp-2 MUST run ./tool/run-tests.sh --filter=m60 first and record the number of tests that ran.  Tracked files only (src/, mod/, prelude/, tool/run-tests.scm); it does NOT read docs/.  The advisory tool/m60-audit.sh and tool/m60-plan-lint.sh are NOT written
  "test/m60/test-m60-imp1.el"
  "test/m60/test-m60-imp2.el"                 ; M60 imp-2 the MEASUREMENT of the standalone-load boundary (docs/m60-plan.org section 3; C delta 0, Scheme delta 0; no file move).  It registers the (m60) group FIRST, builds nothing, and re-measures the 4 probes of the audit in a plain guile -L mod subprocess: test/m60/probe-imp2.scm takes ONE mode per process (cells / provide / stubs / negative / registration) and prints key: value lines, and this corpus runs it with GUILE_AUTO_COMPILE=0 and GUILEMACS_ROOT from the repo root, so a stub of one mode can not hide the next result.  R1 re-measures the surface (src/xfaces.c 7,741 / mod/emacs/loader.scm 1,190 / mod/emacs/reader.scm 2,021 / prelude/load.scm 266 / mod/emacs/faces.scm 70 / mod/emacs-elisp/spec.scm 38 LINES (wc -l); loader.scm 18 / 14 / 7 LINES (grep -c); tree-wide scm_c_public_ref 267 OCCURRENCES; test/mod 6 FILES; mod/emacs-elisp 9 ENTRIES) and the 2 fixture files.  R2 pins the cell list: the 11 guarded installs in call order, EMPTY-CELLS = () MEASURED after init-loader, so the M55 imp-3 result HOLDS; the 2 unguarded cells (load, autoload-do-load); the 4 variable binds; and the provide / require asymmetry (0 set-symbol-function! 'require sites).  R3 pins the 4 first stops, one per REAL lisp/ file: subdirs.el -> void-function (normal-top-level-add-to-load-path), cdl.el -> (provide), obarray.el -> (defconst), hex-util.el -> (eval-when-compile), plus the unbound features variable (src/fns.c :6372 DEFVAR_LISP).  R4 pins the ordered stub chain, the FIRST stop that a pure stub can NOT pass -- (void-variable obarray-default-size), a VARIABLE, because elisp-loader-eval has no defvar branch -- the LAST GOOD POINT (faithful elisp-provide + features bound: lisp/cdl.el loads to the end, the elisp featurep of cdl is #t, features is (cdl); the real featurep is a C DEFUN and its own cell is empty here, so the fixture uses the elisp definition, a memq over features), and the NEGATIVE CONTROL in its own process (faithful provide WITHOUT the features bind: ERROR wrong-type-arg on the unbound sentinel, NOT void-function; the address in the sentinel changes, so only the 3 stable words are pinned).  R5 pins the NAMED BLOCKER: the registration exit status is not 0, the text holds "no such language emacs-elisp" and system/base/language.scm:66, mod/emacs-elisp/spec.scm :20 defines the language and :37 calls compile-and-load, the prelude monkey patch is still LIVE, and src/emacs.c :1639 resolves the module.  R6 pins THIS registration: the imp-2 line AFTER the imp-1 line, imp-1 kept, (m60) after (m59), and NO prelude key -- so the corpus runs inside the built src/emacs.  R7 holds the 6 per-group min-count guards, the MARKER-ROUTING self-check of the absent-guile skip path (cr.org F4: a missing guile binary is a controlled ERT skip, never a pass), and the group-total ert-deftest selecting ^m60-imp2 (38 checks + 1 deftest = 39 ERT tests).  MEASURED gate: --filter=m60 gives 36 tests for imp-1 before imp-2 and 75 after it (36 + 39), 0 fail, exit 0.  All values were MEASURED on 2026-10-20; the base cite is 3603a6795, an ANCESTOR of HEAD, and no src/, mod/, or prelude/ file differs between that commit and the one that registers this corpus (cr.org F1) -- the imp-1 corpus and its 1-line count fix arrived in the SAME commit as imp-2; none is copied from brief.org.  Tracked files only (src/, mod/, prelude/, tool/run-tests.scm, test/m60/); it does NOT read docs/
  "test/m60/test-m60-imp3.el"                 ; M60 imp-3 the SPLIT of the language registration (C delta 0, Scheme delta +1 file / -36 lines in the prelude).  It moves `define-language emacs-elisp' from (emacs-elisp spec) to the new module (language emacs-elisp spec), because Guile `lookup-language' resolves `(language NAME spec)' and reads the binding NAME in that module (system/base/language.scm:62 ... :66); (emacs-elisp spec) keeps `compile-and-load' and RE-EXPORTS the language, so src/emacs.c:1639 keeps its own resolve.  The prelude monkey patch (lookup-language / default-environment, 4 module-set! sites, 36 lines) is DELETED in the SAME commit: one live mechanism only.  The loader gains the `compiled-file-name' import and makes `elisp-loader-compiler-available?' require the C runtime handoff `c-runtime-installed?' (runtime.scm: emacs!), because the presence of the language no longer proves that a compiled elisp form can RUN -- measured: load-compiled of a compiled fixture raises Unbound variable: n. test/m60/probe-imp3.scm keeps the 5 imp-2 modes without a semantic change and adds mode `language', which prints LANGUAGE? / LANGUAGE-TITLE / LANGUAGE-NAME from Guile's own lookup-language.  MEASURED plain guile: LANGUAGE? #t, title "Modern Emacs Lisp", name emacs-elisp.  NEXT blocker: the fixture still exits 1, and now stops inside `compile-and-load' at `Unbound variable: mapcar' (the Scheme elisp compiler resolves `mapcar'; only the C runtime binds it).  The 5 probe modes reproduce the imp-2 values exactly, the pure-guile gate stays 35 passed (3 + 4 + 28), and no .go file is left in the tree by a plain guile process (the *.el.go rule of .gitignore holds a FULL-Emacs run).  S1 the surface re-measured (prelude/load.scm 266 -> 230, mod/emacs-elisp/spec.scm 38 -> 32, the new module 20 LINES, loader.scm 1203; mod/emacs-elisp stays 9 ENTRIES (brief.org F1: the count does NOT go to 10) and mod/language/emacs-elisp is 1 ENTRY).  S2 the new module holds the language object and NOTHING else.  S3 the observable.  S4 one mechanism only.  S5 no regression (the 5 modes + the 35-case gate).  S1 also pins the fixture header word (cr.org F4) and the .gitignore rule for the generated *.el.go files (cr.org F3: the 154 files of the first attempt were deleted, and the rule sits next to the *.elc rule, because a FULL-Emacs run writes them again).  S4 also pins the loader C-runtime gate (cr.org F2).  S6 this registration: the imp-3 line AFTER the imp-2 line, (m60) after (m59), no prelude key.  S7 the guards (9 / 7 / 4 / 7 / 8 / 4 min counts, the absent-guile marker routing, and the 46 checks + 1 deftest = 47 ERT tests).  MEASURED gate: --filter=m60 gives 122 tests (36 imp-1 + 39 imp-2 + 47 imp-3), 0 fail, exit 0.  Every value was MEASURED on 2026-10-20 on a BUILT tree
  "test/m60/test-m60-imp4.el"                 ; M60 imp-4 rows 18 and 19 of the M60 row map: the `provide' cell and the `features' bind (C delta 0, Scheme delta +10 / -2 lines, ONE home).  Both cells get the home `init-loader' (mod/emacs/loader.scm), because the standalone path runs it and a full Emacs runs it before the prelude; the 2 old homes are DELETED in the SAME commit (prelude/load.scm:227 bare `(set-symbol-value! 'features '())`, mod/emacs/utils.scm:576 `(set-symbol-function! 'provide elisp-provide)` inside init-utils-registrations), so no cell has 2 live mechanisms.  Each cell is GUARDED: `symbol-bound?' for the variable (row 19, a C DEFVAR_LISP at src/fns.c:6372) and `symbol-fbound?' for the function cell (row 18, a C DEFUN at src/fns.c:3450), the shape of the guarded bind block of rows 14 ... 17.  A full Emacs therefore keeps both C cells; a plain `guile -L mod' process gets the pure Scheme cell of (emacs utils):211.  MEASURED acceptance on the plain path: LOAD lisp/cdl.el: done, featurep cdl: #t, features: (cdl), ASYM: require=#f provide=#t, FEATURES-BOUND: #t.  `require' is NOT proven: (elisp-require) is exported at mod/emacs/utils.scm:26 and NEVER defined; row 20 is a separate commit.  The NEGATIVE CONTROL (probe mode negative) takes the SAME boot and then unbinds the value cell of `features' again with the EXPORTED `makunbound!' helper of (emacs-elisp runtime), because a control that skips the boot would also lose the reader cells of init-loader and would stop with `Wrong type to apply: #nil' before `provide' runs (recorded and pinned by probe mode noboot); the load then still raises wrong-type-arg on the unbound sentinel (the 2 pinned words `memq' and `uninterned-symbol unbound', never the address).  S1 the 2 guarded forms, their order after the `%load-path' append, and the FIX-20261020-guilemacs marker.  S2 ONE home: 0 sites in the prelude, 0 in utils.scm, 1 of each in loader.scm.  S3 the acceptance observable through a live guile child (mode cells, which never installs the 2 cells, so the words come from init-loader only).  S4 the negative control (mode negative) and probe mode noboot, the record of why the control keeps the boot.  S5 the re-measured surface: loader.scm 1,203 -> 1,214, prelude/load.scm 230 -> 229, utils.scm 607 -> 606 LINES (wc -l) and loader.scm 18/14/7 -> 19/15/8 LINES (grep -c).  S6 this registration: the imp-4 line AFTER the imp-3 line, imp-1 ... imp-3 kept, no prelude key.  S7 the guards (4 / 3 / 4 / 4 / 4 / 3 min counts, the absent-guile marker routing, and the 29 checks + 1 deftest = 30 ERT tests).  RE-PINNED in the same commit: the 5 m55 corpora, the m56 imp-3 corpus, the m59 imp-4 corpus and the m60 imp-1, imp-2 and imp-3 corpora (the 2 LINE counts, the 3 grep -c counts, the `utils.scm:576' install pin -> a loader.scm pin plus "0 installs in utils.scm", the `provide=#f' and `FEATURES-BOUND: #f' probe pins, and the cdl.el stop of mode `cells', which is now `done').  Host limits: the tree IS built (cr.org F3), so ./tool/run-tests.sh --filter=m60 RUNS and gives 152 tests (36 imp-1 + 39 imp-2 + 47 imp-3 + 30 imp-4), 0 fail, exit 0 -- the trailing-equals form --filter=m60= of the older tracker text matches NO group and is a FALSE GREEN (cr.org F2).  The full-Emacs owner of the 2 cells is a source reading (src/fns.c:3450, :6372), not a measurement on this host; no timing of the 2 added guards was taken.  Tracked files only (src/, mod/, prelude/, tool/run-tests.scm, test/m60/); it does NOT read docs/
  "test/m60/test-m60-imp5.el"                 ; M60 imp-5 row 20 of the M60 row map: the `require' cell (C delta 0, Scheme delta +1 cell / -1 export NAME, ONE home).  The cell gets the home `init-loader' (mod/emacs/loader.scm:915), because the standalone path runs it and a full Emacs runs it before the prelude; the stale `elisp-require' NAME is DELETED from the #:export list of (emacs utils) :26 in the SAME commit, because (emacs loader) uses (emacs utils) (loader.scm:18) and a definition in utils.scm that calls the loader is a module cycle, and because a 2nd live mechanism is NOT permitted.  The cell follows Frequire (src/fns.c:3496): CHECK_SYMBOL (:3521), a `memq' against `features', the elisp `load' protocol with NOMESSAGE t / NOSUFFIX nil / MUST-SUFFIX t only when the name comes from the feature symbol (:3582), the 2nd `memq', and `error "Required feature `%s' was not provided"' (:3604).  It calls `elisp-load' (loader.scm:725), NOT the lower `load-elisp' (:831), and it tests the load value with `elisp-loader-truthy?' (:1050), NOT `(eq? result #nil)': a NOERROR failure of `elisp-load' returns Scheme #f (:785), so a plain nil test reads a FAILED load as a success (RISK R1).  The cell is GUARDED with `symbol-fbound?', exactly like `provide' (row 18), so a full Emacs keeps the C DEFUN.  MEASURED PRECONDITION (the new fact of imp-5): the elisp `load' protocol applies `string-suffix-p' and `file-name-directory' (loader.scm:257, :259) and BOTH function cells are EMPTY in a plain `guile' process, so `elisp-load' stopped with `wrong-type-arg "Wrong type to apply: #nil"' BEFORE the load started; imp-5 installs those 2 cells in the same guarded block, reuses the pure-Scheme `string-suffix-p' of (emacs strings):336 (now exported with #:select) and adds the small loader path split `elisp-loader-file-name-directory' (:991).  MEASURED acceptance on the plain path (probe mode require): REQUIRE-FBOUND #t, features-at-start (), REQUIRE cdl: cdl, features: (cdl), REQUIRE-AGAIN: cdl with ONE `loading cdl' line (the elisp `load-path' variable is emptied before that line, so a real load would fail -- the line proves that no 2nd load runs), REQUIRE-NOT-PROVIDED with the C message words, REQUIRE-MISSING with `Cannot open load file', REQUIRE-NOERROR: #nil.  S1 the cell source: 1 definition in loader.scm, 0 names in utils.scm and in the prelude, the FIX-20261021-guilemacs marker, the `elisp-load' call, and the `elisp-loader-truthy?' test.  S2 the install: 1 guarded site AFTER the `provide' install and BEFORE `(set! %load-extensions ...)', plus the 2 `load' protocol cells.  S3 the 7 keys of mode `require' plus the silence count.  S4 no regression on modes cells / provide / stubs / negative / noboot / registration / language.  S5 the re-measured surface: loader.scm 1,214 -> 1,308, utils.scm 606 (an export NAME was removed, not a line), prelude/load.scm 229 LINES (wc -l) and loader.scm 19/15/8 -> 22/18/9 LINES (grep -c).  S6 this registration: the imp-5 line AFTER the imp-4 line, imp-1 ... imp-4 kept, no prelude key.  S7 the guards (5 / 4 / 8 / 6 / 2 / 3 min counts, the absent-guile marker routing, and the 35 checks + 1 deftest = 36 ERT tests).  RE-PINNED in the same commit: the 5 m55 corpora, the m56 imp-3 corpus and the m60 imp-1, imp-2, imp-3 and imp-4 corpora (the 2 LINE counts and the 3 grep -c counts, the `require-asymmetry' pin of imp-1 (1 name in utils.scm -> 2 OCCURRENCES in loader.scm and 0 in utils.scm and the prelude), the `ASYM: require=#f provide=#t' lines of modes `cells' (imp-2, imp-3, imp-4), and the `require-fbound: #f' pin of mode `provide').  LIMITS, named and NOT claimed: N1 ONE home (loader.scm).  N2 the circular guard `features_being_loaded' (src/fns.c:3488) is C state and is NOT ported -- a circular `require' chain can loop, and the FILE-level skip of `elisp-load' (:757) is NOT a feature-level guard.  N3 the depth-3 limit `require_nesting_list' (:3481) is NOT ported.  N4 `subfeatures', `Vcurrent_load_list', the `after-load-alist' hook and the 2nd error message "Loading file %s failed to provide feature" (:3606) stay C-only behaviour.  N5 the C owner of the cell is a SOURCE READING (src/fns.c:3496), not a measurement: no C core runs on this host.  Host state: the tree IS built, so ./tool/run-tests.sh --filter=m60 RUNS and now gives 188 tests (36 + 39 + 47 + 30 + 36), and ./test/mod/run-mod-tests.sh gives 35.  Tracked files only (mod/, prelude/, tool/run-tests.scm, test/m60/); it does NOT read docs/
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
