"""Case definitions and probes for the PTY driver."""

import atexit
import errno
import os
import shutil
import subprocess
import tempfile

# The meta modifier bit, duplicated from (emacs event-modifiers)
# meta-modifier (char-meta = #x8000000).  The read-path probe reports
# each stored event as a "code:mods" token; a byte whose high bit sets
# the meta modifier (meta key 1) decodes to mods == META.
META = 0x8000000

# The report token for an empty list.  An empty Scheme list reached
# through `eval-scheme' prints as the opaque "#<scheme ()>" object, and
# an empty string is invisible inside a space-separated report, so a
# probe writes this instead.
EMPTY = "-"

# The separator between the repeats of a group (the read path's calls).
JOIN = " | "


# --------------------------------------------------------------------
# The child probes.  Each one's value is a STRING.
# --------------------------------------------------------------------

# The Scheme side of the report format.  A probe that measures several
# numbers splices these in with the @@HELPERS@@ placeholder and formats
# its report with `fmt-call' and `join'.
#
# `fmt-call' is the Scheme twin of render_call below, and `join' is the
# twin of "@@JOIN@@".join.  The two must agree exactly, or a correct
# measurement reports as a FAIL.  selftest_scheme() runs these helpers
# under guile and compares them with the Python renderer for every case,
# so the pair is checked on a host with no pty.
REPORT_HELPERS = r"""
  (define (tok pair)
    (string-append (number->string (car pair)) ":"
                   (number->string (cdr pair))))
  (define (join sep items)
    (if (null? items)
        ""
        (let loop ((l (cdr items)) (s (car items)))
          (if (null? l) s (loop (cdr l) (string-append s sep (car l)))))))
  (define (fmt-call ret stored ev)
    (string-append
     (if (number? ret) (number->string ret) "no-terminal")
     " " (number->string stored)
     " " (if (null? ev) "@@EMPTY@@" (join "," (map tok ev)))))
"""

# M42: the TTY raw-input read path, through (emacs gobble).  Take the
# newest terminal, record every decoded keystroke the policy makes as
# (code . mods), call tty-read-avail-input! @@CALLS@@ times, and report
# "<return> <stored> <order>" per call, joined with " | ".
#
# The probe computes <stored> itself, as the DIFFERENCE between the
# kbd_buffer count after and before the call.  A difference does not
# depend on what the buffer held when the child started, so the expected
# string stays valid whatever the startup leaves behind.
#
# `eval-scheme' evaluates its string in the current module, not in
# (emacs gobble), so every binding the probe needs -- including
# tty-read-avail-input! -- is taken with `module-ref'.  A bare
# (tty-read-avail-input! ...) is an unbound variable there and makes the
# child error out before it reports.
#
# The (emacs gobble) leaves are `defelisp' promises.  Three of them force
# to a PROCEDURE that is then called -- %terminal-list and
# %--kbd-buffer-nr-stored take no argument, %--ie-ascii-keystroke-event
# takes (CODE MODS FRAME); see gobble.scm.  A single (force ...) yields
# the procedure, not its value, so those three need double parentheses:
# ((force %terminal-list)).  tty-read-avail-input! is a plain
# (define ...) procedure, so a single force-then-call is right.
#
# The per-case meta-key / quit-char stubs use the established pattern:
# module-set! the promise to a new delay, run, then module-set! the
# original promise back.  @@META_STUB@@ and @@QUIT_STUB@@ are empty when
# the case asks for no stub.
READ_PATH_PROBE = r"""
(let* ((mod (resolve-module '(emacs gobble)))
       (terms ((force (module-ref mod '%terminal-list))))
       ;; %terminal-list is oldest-first (gobble.scm walk order), so the
       ;; newest terminal is the last element.  Take that; taking the
       ;; head would pick the oldest.
       (term (let ((ts (reverse terms))) (and (pair? ts) (car ts))))
       (mk (module-ref mod '%--ie-ascii-keystroke-event))
       (nr (module-ref mod '%--kbd-buffer-nr-stored))
       (read! (module-ref mod 'tty-read-avail-input!))
       (meta-o (module-ref mod '%--tty-meta-key))
       (quit-o (module-ref mod '%--quit-char))
       (calls @@CALLS@@)
       (order '())
       (out '()))
  ;; The report helpers come first: an internal `define' must precede
  ;; every expression of the body.
@@HELPERS@@
  @@META_STUB@@
  @@QUIT_STUB@@
  (module-set!
   mod '%--ie-ascii-keystroke-event
   (delay (let ((f (force mk)))
            (lambda (code mods frame)
              (set! order (append order (list (cons code mods))))
              (f code mods frame)))))
  (let loop ((k calls) (prev ((force nr))))
    (let* ((ret (if term (read! term) 'no-terminal))
           (n1 ((force nr)))
           (ev order))
      (set! order '())
      (set! out (append out (list (fmt-call ret (- n1 prev) ev))))
      (if (> k 1) (loop (- k 1) n1) #f)))
  (module-set! mod '%--ie-ascii-keystroke-event mk)
  (module-set! mod '%--tty-meta-key meta-o)
  (module-set! mod '%--quit-char quit-o)
  (join "@@JOIN@@" out))
"""

# The Scheme side of the mode comparison, shared by the two mode probes.
# A termios mode is (IFLAG OFLAG CFLAG LFLAG CC-BYTEVECTOR), so equality
# is four numbers plus a bytevector walk.  This was copied in both
# probes; it is spliced in with @@MODE_HELPERS@@.
MODE_HELPERS = r"""
  (define (cc=? a b)
    (and (= (bytevector-length a) (bytevector-length b))
         (let loop ((i 0))
           (or (= i (bytevector-length a))
               (and (= (bytevector-u8-ref a i) (bytevector-u8-ref b i))
                    (loop (1+ i)))))))
  (define (mode=? a b)
    (and (= (list-ref a 0) (list-ref b 0))
         (= (list-ref a 1) (list-ref b 1))
         (= (list-ref a 2) (list-ref b 2))
         (= (list-ref a 3) (list-ref b 3))
         (cc=? (list-ref a 4) (list-ref b 4))))
"""

# M43 imp-3: the observable TTY mode.  Compute the wanted mode with the
# pure policy (tty-mode-wanted), apply it with the imp-2 leaf through the
# thin entry point (init-tty-mode), read the terminal mode back, and
# report whether the applied mode equals the wanted mode.
#
# `init-tty-mode' merges the build constants itself, so FLAGS holds only
# the plain inputs.  `tty-mode-wanted' needs the constants in its flag
# list, so FULL appends them.  FD 0 is the pty slave.
#
# THE JUDGEMENT STAYS IN THE CHILD here, unlike every other probe.  The
# wanted mode comes from `tty-mode-wanted' over the build constants, so
# the driver cannot know it; only the child can see both sides.  The
# probe therefore reports the comparison, not the values.
MODE_PROBE = r"""
(let* ((mod (resolve-module '(emacs tty-modes)))
       (get (module-ref mod 'tty-get-mode))
       (init (module-ref mod 'init-tty-mode))
       (wanted (module-ref mod 'tty-mode-wanted))
       (consts (module-ref mod 'tty-mode-constants))
       (flags (list @@FLAGS@@))
       (base (get 0)))
@@MODE_HELPERS@@
  (if (not base)
      "no-base-mode"
      (let* ((full (append flags (consts)))
             (expect (wanted base full))
             (_applied (init 0 base flags))
             (after (get 0)))
        (cond
         ((not after) "no-mode-after-apply")
         ((mode=? after expect) "ok")
         (else (format #f "mismatch expected=~s actual=~s" expect after))))))
"""

# M43 imp-4: the observable TTY-mode restore.  Read the pre-init mode,
# save it, apply the Emacs mode through `init-tty-mode', restore the
# saved mode through `reset-tty-mode', read the mode back, and compare.
# The judgement stays in the child for the same reason as MODE_PROBE.
RESTORE_PROBE = r"""
(let* ((mod (resolve-module '(emacs tty-modes)))
       (get (module-ref mod 'tty-get-mode))
       (init (module-ref mod 'init-tty-mode))
       (reset (module-ref mod 'reset-tty-mode))
       (flags (list @@FLAGS@@))
       (saved (get 0)))
@@MODE_HELPERS@@
  (if (not saved)
      "no-base-mode"
      (let* ((_init (init 0 saved flags))
             (_reset (reset 0 saved))
             (after (get 0)))
        (cond
         ((not after) "no-mode-after-reset")
         ((mode=? after saved) "ok")
         (else (format #f "mismatch saved=~s after=~s" saved after))))))
"""

# M43 imp-5: the observable TTY size.  Probe the size through the thin
# entry point (tty-size), apply the case's size with set-tty-size, read
# the size back, and REPORT IT as "<width> <height>".
#
# Unlike the two mode probes, this one does not judge: the driver knows
# the size it asked for, so the case can expect the string.  The error
# arms still report a word, which never equals the expected size and so
# becomes a FAIL carrying its reason.
SIZE_PROBE = r"""
(let* ((mod (resolve-module '(emacs tty-modes)))
       (get-size (module-ref mod 'tty-size))
       (set-size (module-ref mod 'set-tty-size))
       (before (get-size 0)))
  (if (not (pair? before))
      "no-size"
      (let ((status (set-size 0 @@HEIGHT@@ @@WIDTH@@)))
        (if (< status 0)
            (format #f "set-failed ~s" status)
            (let ((after (get-size 0)))
              (if (not (pair? after))
                  "no-size-after-set"
                  (string-append (number->string (car after)) " "
                                 (number->string (cdr after)))))))))
"""

# M53 imp-3: the PTY terminal VERTICAL SLICE.  This is the CHECK 2
# smaller step (brief.org section 3).  ONE integrated probe runs the
# whole slice in the built src/emacs on the pty, in this order:
#
#   (a) start  -- the child is already terminal Emacs on the pty.
#   (b) load   -- the child loads a real Elisp file through the elisp
#                 `load' primitive and reads the `setq' side effect back
#                 with (emacs-elisp runtime) `symbol-value'.  A missing
#                 cell or a failed load is "FAIL".
#   (c) read   -- the driver writes input bytes to the master; the child
#                 runs the (emacs gobble) read path once and reports
#                 "<return>,<stored>".  The events order is NOT reported:
#                 the m42-imp3 events-order observation is a separate
#                 pre-existing defect (the store calls the defelisp macro
#                 directly, so the probe's module-set! no longer
#                 intercepts it); the slice pins the read and store
#                 counts, which are the load-bearing observables.
#   (d) write  -- the child writes a BEGIN marker, the out bytes, an END
#                 marker; the driver reads the master and checks the span
#                 between the markers against the reported count and the
#                 pinned out bytes (the m52 output_span mechanism).
#   (e) resize -- the driver resizes the pty (TIOCSWINSZ) after READY;
#                 the child reads tty-size after the gate and reports
#                 "<width>x<height>".  A size that follows the resize
#                 proves a LIVE resize.
#   (f) exit / restore -- the driver captures the pty mode BEFORE Popen,
#                 waits for the child to EXIT, asserts the exit status is
#                 0, and reads the mode back.  The child also judges its
#                 own init/reset round trip here ("RESTORED").
#
# The report is ONE string, one line:
#
#   "load:<OK|FAIL> read:<ret>,<stored> out:<n> size:<W>x<H> mode:<RESTORED|other>"
#
# The child-side load and restore judgement stays in the child, where
# only the child can see both sides (MODE_PROBE, line 230).  The size,
# read counts, and out bytes are judged by the driver, which knows what
# it asked for.
M53_IMP3_BEGIN = b"M53-BEGIN!"
M53_IMP3_END = b"M53-END!"
M53_IMP3_OUT_BYTES = b"M53-IMP3-SLICE-OK!"
M53_IMP3_ROWS = 30
M53_IMP3_COLS = 100

M53_IMP3_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (modes (resolve-module '(emacs tty-modes)))
       (rt (resolve-module '(emacs-elisp runtime)))
       (sv (module-ref rt 'symbol-value))
       (loadf (module-ref rt 'symbol-function))
       (terms ((force (module-ref gobble '%terminal-list))))
       ;; %terminal-list is oldest-first, so the newest terminal is the
       ;; last element (see READ_PATH_PROBE).
       (term (let ((ts (reverse terms))) (and (pair? ts) (car ts))))
       (nr (module-ref gobble '%--kbd-buffer-nr-stored))
       (read! (module-ref gobble 'tty-read-avail-input!))
       (write! (module-ref output 'tty-write-bytes))
       (flush! (module-ref output 'tty-flush))
       (get-size (module-ref modes 'tty-size))
       (get-mode (module-ref modes 'tty-get-mode))
       (init (module-ref modes 'init-tty-mode))
       (reset (module-ref modes 'reset-tty-mode))
       (flags (list @@FLAGS@@)))
@@MODE_HELPERS@@
  (let* ((readstr
         ;; Read input FIRST, right after the gate, before the load:
         ;; Emacs's own input poll can move pending tty bytes into
         ;; kbd_buffer during a longer step, and then FIONREAD reads 0.
          (if (not term)
              "no-terminal"
            (let* ((prev ((force nr)))
                   (ret (read! term))
                   (n1 ((force nr))))
              (string-append
               (if (number? ret) (number->string ret) "no-terminal")
               "," (number->string (- n1 prev))))))
         (loaded (catch #t
                   (lambda ()
                     ((loadf 'load) "@@LOADFILE@@" #nil #nil)
                     (equal? (sv 'm53-imp3-loaded) 4242))
                   (lambda (k . a) #f)))
         (outstr
          (if (not term)
              "no-terminal"
            (begin
              (write! term #vu8(77 53 51 45 66 69 71 73 78 33))
              (let ((n (write! term #vu8(@@OUTBYTES@@))))
                (flush! term)
                (write! term #vu8(77 53 51 45 69 78 68 33))
                (flush! term)
                (if (number? n) (number->string n) "write-failed")))))
         (sizestr
          (if (not term)
              "no-terminal"
            (let ((sz (get-size 0)))
              (if (not (pair? sz))
                  "no-size"
                (string-append (number->string (car sz)) "x"
                               (number->string (cdr sz)))))))
         (modestr
          (let ((saved (get-mode 0)))
            (if (not saved)
                "no-base-mode"
              (let* ((_i (init 0 saved flags))
                     (_r (reset 0 saved))
                     (after (get-mode 0)))
                (if (and after (mode=? after saved)) "RESTORED" "other"))))))
    (string-append "load:" (if loaded "OK" "FAIL")
                   " read:" readstr
                   " out:" outstr
                   " size:" sizestr
                   " mode:" modestr)))
"""


# --------------------------------------------------------------------
# The case tables.  Case NAMES are the driver's contract with the ERT
# corpora, which match "PASS <name>" lines.  Do not rename a case.
# --------------------------------------------------------------------

def read_path_case(name, group, data, calls, meta_key=None, quit_char=None,
                   **extra):
    """Build one read-path case.

    CALLS is a list of (return, stored, order) triples, one per call to
    the read path; ORDER is a list of (code, mods) pairs.  The triples
    are the readable spelling of the expected report; expect_string
    renders them into the one wire format.  META_KEY and QUIT_CHAR stub
    the matching (emacs gobble) leaf for the duration of the probe.
    """
    meta_stub = ("(module-set! mod '%--tty-meta-key (delay (lambda (t) {})))"
                 .format(meta_key) if meta_key is not None else "")
    quit_stub = ("(module-set! mod '%--quit-char (delay (lambda () {})))"
                 .format(quit_char) if quit_char is not None else "")
    case = {
        "name": name,
        "group": group,
        "probe": READ_PATH_PROBE,
        "subst": {"CALLS": str(len(calls)),
                  "META_STUB": meta_stub,
                  "QUIT_STUB": quit_stub},
        "bytes": data,
        "expect_calls": calls,
    }
    case.update(extra)
    return case


def render_call(ret, stored, order):
    """Render one read-path call as "<return> <stored> <order>"."""
    tokens = ",".join("%d:%d" % (code, mods) for code, mods in order)
    return "%s %d %s" % (ret, stored, tokens if tokens else EMPTY)


def expect_string(case):
    """Return the exact report string CASE expects.

    A case may give `expect` directly, or give `expect_calls` as the
    readable per-call spelling of a read-path report.
    """
    if "expect" in case:
        return case["expect"]
    return JOIN.join(render_call(*call) for call in case["expect_calls"])


# Case 1: the pty holds no bytes.  The path returns 0 and stores nothing.
# Case 2: two bytes, far fewer than one batch (KBD_BUFFER_SIZE - 1 =
#         4095).  The path returns the short count (2) and stores exactly
#         two events, in order.  It must not wait for the rest of a batch.
M42_IMP3_CASES = (
    read_path_case("m42-imp3/case-1-no-input", "m42-imp3", b"",
                   [(0, 0, [])]),
    read_path_case("m42-imp3/case-2-short-read", "m42-imp3", b"AB",
                   [(2, 2, [(0x41, 0), (0x42, 0)])]),
)

# Case 3: the meta decode, one sub-case per %--tty-meta-key value.
#   meta key 1 -- the high bit gives the meta modifier, the byte is
#                 stripped to 7 bits (code 0x01/0x61, mods meta).
#   meta key 2 -- no strip, no modifier (code 0x81/0xe1, mods 0).
#   meta key 0 -- no modifier, byte still stripped (code 0x01/0x61, mods 0).
# Case 4: the quit-char batch break.  Five bytes, quit char 7: the path
#   decodes 65, 66 and 7, then drops 67 and 68, but returns the read
#   count (5), not the stored count.
#   FIX-20260928-guilemacs: the decode of the raw C-g does reach
#   kbd-buffer-store-event!, but its folded code (7) equals quit_char, so
#   the quit-char branch handles that event and never ring-appends it
#   (mod/emacs/kbd-buffer.scm, "C 4623-4676 ... never ring-appends").
#   Only 65 and 66 enter kbd_buffer, so the stored count is 2, not 3.
#   The case pins three facts: read count 5, the 2 bytes in kbd_buffer,
#   the 3 decoded keystrokes.
#   FIX-20260928-guilemacs: the rejected option is that a raw C-g must
#   occupy one kbd_buffer slot.  Evidence against it: the
#   kbd-buffer.scm docstring says the quit-char branch never
#   ring-appends, and the passing case-4-meta-quit-guard case agrees --
#   its meta byte folds to code 7 with the meta modifier, which is not
#   equal to quit_char, so it IS stored.  Vanilla C also diverts the
#   quit char to the quit machinery.  The guard case proves the
#   strip/compute order: with meta key 1, byte 0x87 stores code 7 with
#   mods meta and breaks the batch (a backward order gives code 7 mods 0).
#   The driver clears ISIG on the pty before it writes the bytes
#   (deliver_raw): Emacs arms the tty with ISIG and c_cc[VQUIT] =
#   quit_char, so the line discipline would eat a raw 0x07 and flush the
#   queue.  Cases 4 and 6 both send a raw 0x07 and both need this.
# Case 5: terminal loss.  The child ignores SIGHUP before the read
#   (CHILD_PROGRAM), so the driver can close the pty master without
#   terminating the emacs under test.  The slave read then fails with
#   EIO, which the C leaf maps to the close-terminal result -2, and the
#   child writes its report to the report pipe (fd 2), which survives the
#   hangup.  The case measures the -2 arm; a host that cannot give EIO
#   reports an environment-gated INFO skip.
# Case 6: continuation.  Two calls.  The first call reads the whole
#   FIONREAD batch in one read, then drops the byte after the quit char.
#   The second call therefore finds an empty tty: return 0, no store.
#
# FIX-20260928-guilemacs: case 6 first expected byte B to stay on the tty
# for call 2 (return 1, stored 1).  That contradicts the vanilla C
# tty_read_avail_input: the body sizes one emacs_read of the whole
# FIONREAD batch, then breaks the decode at the quit char.  B is consumed
# by that read and dropped, so call 2 reads 0.  The case now pins the
# code's real model (call 2: return 0, stored 0, no events); the product
# is not changed.
#
# FIX-20260928-guilemacs: the same treatment applies to the stored count
# of the first call.  Cases 4 and 6 first expected 3 and 2 stored events,
# but the raw C-g that breaks the decode is handled by the quit-char
# branch and is not ring-appended, so the real model stores 2 and 1.  The
# product is not changed.
M42_IMP4_CASES = (
    read_path_case("m42-imp4/case-3-meta-key-1", "m42-imp4", b"\x81\xe1",
                   [(2, 2, [(0x01, META), (0x61, META)])], meta_key=1),
    read_path_case("m42-imp4/case-3-meta-key-2", "m42-imp4", b"\x81\xe1",
                   [(2, 2, [(0x81, 0), (0xe1, 0)])], meta_key=2),
    read_path_case("m42-imp4/case-3-meta-key-0", "m42-imp4", b"\x81\xe1",
                   [(2, 2, [(0x01, 0), (0x61, 0)])], meta_key=0),
    # FIX-20260928-guilemacs: 65 and 66 enter kbd_buffer; the raw C-g is
    # decoded but takes the quit-char branch, so it is not ring-appended
    # (see the case-4 comment block above).
    read_path_case("m42-imp4/case-4-quit-byte", "m42-imp4", b"AB\x07CD",
                   [(5, 2, [(0x41, 0), (0x42, 0), (0x07, 0)])], quit_char=7),
    read_path_case("m42-imp4/case-4-meta-quit-guard", "m42-imp4", b"A\x87",
                   [(2, 2, [(0x41, 0), (0x07, META)])],
                   meta_key=1, quit_char=7),
    # Take the tty away after READY.  The child ignores SIGHUP, so the
    # hangup does not kill it; the slave read then fails with EIO -> the
    # close-terminal result -2.  If the host cannot give EIO, the verdict
    # is an environment-gated INFO skip (the "env_gate" reason), never an
    # unconditional one.
    read_path_case("m42-imp4/case-5-terminal-loss", "m42-imp4", b"",
                   [(-2, 0, [])],
                   close_master=True,
                   env_gate="host did not give EIO on master close"),
    # FIX-20260928-guilemacs: call 1 reads all 3 bytes and decodes 65 and
    # 7, but only 65 enters kbd_buffer -- the raw C-g takes the quit-char
    # branch (see the case-4 comment block).  Call 2 finds an empty tty,
    # because that one read consumed B.
    read_path_case("m42-imp4/case-6-continuation", "m42-imp4", b"A\x07B",
                   [(3, 1, [(0x41, 0), (0x07, 0)]),
                    (0, 0, [])], quit_char=7),
)

# The tty flags the two mode cases drive the policy with.  This is CASE
# DATA, so it lives here and not inside a probe; both probes take it
# through @@FLAGS@@.
TTY_FLAGS = ("'flow-control? #f 'meta-key? #t "
             "'controlling-tty? #t 'quit-char 7")

# The size the imp-5 case applies and reads back.  set-tty-size takes
# (fd HEIGHT WIDTH); tty-size returns (WIDTH . HEIGHT), so the expected
# report is "<width> <height>".
SIZE_HEIGHT = 30
SIZE_WIDTH = 100

# The two mode probes judge in the child, because only the child can see
# both the wanted mode and the actual one; each reports "ok" or a
# description.  The size probe reports its measurement, like the
# read-path cases, and the case holds the expected value.
M43_CASES = (
    {
        "name": "m43-imp3/pty-e2e",
        "group": "m43-imp3",
        "probe": MODE_PROBE,
        "subst": {"FLAGS": TTY_FLAGS, "MODE_HELPERS": MODE_HELPERS},
        "expect": "ok",
    },
    {
        "name": "m43-imp4/pty-e2e",
        "group": "m43-imp4",
        "probe": RESTORE_PROBE,
        "subst": {"FLAGS": TTY_FLAGS, "MODE_HELPERS": MODE_HELPERS},
        "expect": "ok",
    },
    {
        "name": "m43-imp5/pty-e2e",
        "group": "m43-imp5",
        "probe": SIZE_PROBE,
        "subst": {"HEIGHT": str(SIZE_HEIGHT), "WIDTH": str(SIZE_WIDTH)},
        "expect": "%d %d" % (SIZE_WIDTH, SIZE_HEIGHT),
    },
)

# M53 imp-3: the PTY terminal vertical-slice case (see M53_IMP3_PROBE).
# It lives here, after TTY_FLAGS and MODE_HELPERS are defined, because
# its `subst' reads both at import time.
M53_IMP3_CASES = (
    {
        "name": "m53-imp3/vertical-slice-e2e",
        "group": "m53-imp3",
        "probe": M53_IMP3_PROBE,
        "subst": {"FLAGS": TTY_FLAGS,
                  "MODE_HELPERS": MODE_HELPERS,
                  "OUTBYTES": " ".join(str(b) for b in M53_IMP3_OUT_BYTES)},
        "bytes": b"AB",
        "expect": "load:OK read:2,2 out:18 size:%dx%d mode:RESTORED"
                  % (M53_IMP3_COLS, M53_IMP3_ROWS),
        # The driver resizes the pty after READY, before the gate; the
        # child reads the size after the gate.  30x100 is NOT the pty
        # default, so the report proves the change.
        "resize": (M53_IMP3_ROWS, M53_IMP3_COLS),
        # Capture the pty mode before Popen and read it back after exit
        # (brief.org section 5: the ISIG trap means the capture point
        # MUST be before deliver_raw clears ISIG).
        "capture_mode": True,
        # Wait for the real exit status; today run_case SIGKILLs a live
        # child on a complete report.
        "wait_exit": True,
        # A real Elisp fixture the child loads; its setq is the side
        # effect the child reads back with symbol-value.
        "load_fixture": "(setq m53-imp3-loaded 4242)\n",
        "output_span": (M53_IMP3_BEGIN, M53_IMP3_END),
        # The span bytes are OUR OWN written bytes, not a terminfo span,
        # so pinning them is allowed (brief.org section 4(d)).
        "output_span_bytes": M53_IMP3_OUT_BYTES,
        # The report is composite, so the driver extracts the out count.
        "output_count_re": r"out:(\d+)",
        "env": {"TERM": "xterm"},
    },
)

M52_OUTPUT_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (write! (module-ref output 'tty-write-bytes))
       (flush! (module-ref output 'tty-flush)))
  (if (not term)
      "no-tty-terminal"
    (begin
      (write! term #vu8(77 53 50 45 87 82 73 84 69 45 66 69 71 73 78 33))
      (flush! term)
      (let* ((bytes #vu8(77 53 50 45 73 77 80 51 45 87 82 73 84 69 45 79 75 33))
             (n (write! term bytes))
             (flushed (flush! term)))
        (write! term #vu8(77 53 50 45 87 82 73 84 69 45 69 78 68 33))
        (let ((end-flushed (flush! term)))
          (if (and (= n 18) (= flushed 0) (= end-flushed 0))
              (number->string n)
            "write-failed"))))))
"""

M52_CAP_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (write! (module-ref output 'tty-write-bytes))
       (emit! (module-ref output 'tty-emit-cap))
       (flush! (module-ref output 'tty-flush)))
  (if (not term)
      "no-tty-terminal"
    (begin
      (write! term #vu8(77 53 50 45 67 65 80 45 66 69 71 73 78 33))
      (let ((before-flush (flush! term)))
       (let ((n (emit! term "set-scroll-region" '(2 10))))
        (write! term #vu8(77 53 50 45 67 65 80 45 69 78 68 33))
        (let ((after-flush (flush! term)))
          (if (and (= before-flush 0) (= after-flush 0))
              (number->string n)
            "flush-failed")))))))
"""

M52_SEQ_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (write! (module-ref output 'tty-write-bytes))
       (emit! (module-ref output 'tty-emit-seq))
       (flush! (module-ref output 'tty-flush)))
  (if (not term)
      "no-tty-terminal"
    (begin
      (write! term #vu8(77 53 50 45 83 69 81 45 66 69 71 73 78 33))
      (let ((before-flush (flush! term)))
       (let ((n (emit! term '(("set-scroll-region" 2 10)
                              ("set-scroll-region" 4 8)))))
        (write! term #vu8(77 53 50 45 83 69 81 45 69 78 68 33))
        (let ((after-flush (flush! term)))
          (if (and (= before-flush 0) (= after-flush 0))
              (number->string n)
            "flush-failed")))))))
"""

M52_CASES = (
    {
        "name": "m52-imp3/tty-write-bytes-e2e",
        "group": "m52-imp3",
        "probe": M52_OUTPUT_PROBE,
        "expect_decimal": True,
        "output_span": (b"M52-WRITE-BEGIN!", b"M52-WRITE-END!"),
        "output_span_bytes": b"M52-IMP3-WRITE-OK!",
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m52-imp3/tty-emit-cap-e2e",
        "group": "m52-imp3",
        "probe": M52_CAP_PROBE,
        "expect_decimal": True,
        "output_span": (b"M52-CAP-BEGIN!", b"M52-CAP-END!"),
        "output_span_bytes": b"\x1b[3;11r",
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m52-imp3/tty-emit-seq-e2e",
        "group": "m52-imp3",
        "probe": M52_SEQ_PROBE,
        "expect_decimal": True,
        "output_span": (b"M52-SEQ-BEGIN!", b"M52-SEQ-END!"),
        "output_span_bytes": b"\x1b[3;11r\x1b[5;9r",
        "env": {"TERM": "xterm"},
    },
)

# M52 imp-4: the insert / highlight state-flip policy.  The child calls
# the 5 pure policy procedures of (emacs tty-output) through module-ref
# and emits the returned key through --tty-emit-cap.  This proves the
# policy -> key -> bytes chain.  It does NOT reach the rewired C hubs
# (they have no deterministic elisp trigger), so the corpus header
# states that limitation.
M52_IMP4_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (write! (module-ref output 'tty-write-bytes))
       (emit! (module-ref output 'tty-emit-cap))
       (flush! (module-ref output 'tty-flush))
       (on-ins (module-ref output 'tty-turn-on-insert-cap))
       (off-ins (module-ref output 'tty-turn-off-insert-cap))
       (off-hl (module-ref output 'tty-turn-off-highlight-cap))
       (on-hl (module-ref output 'tty-turn-on-highlight-cap))
       (tog-hl (module-ref output 'tty-toggle-highlight-cap)))
  (if (not term)
      "no-tty-terminal"
    (begin
      (write! term #vu8(77 53 50 45 73 77 80 52 45 66 69 71 73 78 33))
      (flush! term)
      (let ((keys (list (on-ins 1) (on-ins 0) (off-ins 0) (off-ins 1)
                        (off-hl 0) (off-hl 1) (on-hl 1) (on-hl 0)
                        (tog-hl 0) (tog-hl 1)))
            (n 0))
        (for-each (lambda (k) (set! n (+ n (emit! term k '())))) keys)
        (write! term #vu8(77 53 50 45 73 77 80 52 45 69 78 68 33))
        (let ((f (flush! term)))
          (if (= f 0) (number->string n) "flush-failed"))))))
"""

M52_IMP4_CASES = (
    {
        "name": "m52-imp4/policy-key-e2e",
        "group": "m52-imp4",
        "probe": M52_IMP4_PROBE,
        "expect_decimal": True,
        "output_span": (b"M52-IMP4-BEGIN!", b"M52-IMP4-END!"),
        "output_span_bytes": b"\x1b[4h\x1b[4l\x1b[27m\x1b[7m\x1b[7m\x1b[27m",
        "env": {"TERM": "xterm"},
    },
)

M52_IMP5_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (write! (module-ref output 'tty-write-bytes))
       (emit! (module-ref output 'tty-emit-cap))
       (flush! (module-ref output 'tty-flush))
       (bell (module-ref output 'tty-ring-bell-cap))
       (hide (module-ref output 'tty-hide-cursor-cap))
       (show (module-ref output 'tty-show-cursor-cap))
       (bg (module-ref output 'tty-background-highlight-cap))
       (hl (module-ref output 'tty-highlight-if-desired-cap))
       (end (module-ref output 'tty-update-end-steps)))
  (if (not term)
      "no-tty-terminal"
    (begin
      ;; Exercise visible-bell and the #nil cursor arms first.  Their
      ;; bytes are NOT pinned: the terminfo "vb" string may carry a
      ;; $<...> padding marker, and a #nil arm emits nothing.  The
      ;; "show-cursor" update-end step list is checked headlessly.
      (emit! term (bell 1 1) '())
      (hide 1)
      (show 0 0)
      (write! term #vu8(77 53 50 45 73 77 80 53 45 66 69 71 73 78 33))
      (flush! term)
      (let ((keys (list (bell 1 0)
                        (car (hide 0))
                        (car (show 1 0))
                        (car (show 1 1)) (car (cdr (show 1 1)))
                        (bg 0) (bg 1) (hl 0) (hl 1)))
            (n 0))
        (for-each (lambda (k) (set! n (+ n (emit! term k '())))) keys)
        (write! term #vu8(77 53 50 45 73 77 80 53 45 69 78 68 33))
        (let ((f (flush! term)))
          (if (= f 0) (number->string n) "flush-failed"))))))
"""

M52_IMP5_CASES = (
    {
        "name": "m52-imp5/policy-key-e2e",
        "group": "m52-imp5",
        "probe": M52_IMP5_PROBE,
        "expect_decimal": True,
        "output_span": (b"M52-IMP5-BEGIN!", b"M52-IMP5-END!"),
        # bell, cursor-invisible, cursor-normal, cursor-normal +
        # cursor-visible, end-standout-mode, standout-mode,
        # end-standout-mode, standout-mode (TERM=xterm).
        "output_span_bytes": (b"\x07\x1b[?25l\x1b[?12l\x1b[?25h"
                              b"\x1b[?12l\x1b[?25h\x1b[?12;25h"
                              b"\x1b[27m\x1b[7m\x1b[27m\x1b[7m"),
        "env": {"TERM": "xterm"},
    },
)

M52_IMP6_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (write! (module-ref output 'tty-write-bytes))
       (emit! (module-ref output 'tty-emit-cap))
       (flush! (module-ref output 'tty-flush))
       (set-modes (module-ref output 'tty-set-terminal-modes-steps))
       (reset-modes (module-ref output 'tty-reset-terminal-modes-steps))
       (cur (module-ref output 'tty-cursor-to-steps))
       (raw (module-ref output 'tty-raw-cursor-to-steps)))
  (if (not term)
      "no-tty-terminal"
    (begin
      ;; Walk every returned step list and emit ONLY the KEY (string)
      ;; steps through --tty-emit-cap.  The marker steps (the "newlines"
      ;; / "raw-cr" / "move" / "background" / "off-insert" lists) carry
      ;; fixnum data and a C mechanism, so the probe skips them.  The
      ;; two cursor procedures return only markers, so they add no bytes
      ;; here; their step lists are checked headlessly instead.
      (write! term #vu8(77 53 50 45 73 77 80 54 45 66 69 71 73 78 33))
      (let ((steps (append (set-modes 1 24 0)
                           (reset-modes)
                           (cur 0 0 5 7 0 0)
                           (raw 0 0 5 7 0 0)))
            (n 0))
        (for-each (lambda (s)
                    (if (string? s)
                        (set! n (+ n (emit! term s '())))
                        #f))
                  steps)
        (write! term #vu8(77 53 50 45 73 77 80 54 45 69 78 68 33))
        (let ((f (flush! term)))
          (if (= f 0) (number->string n) "flush-failed"))))))
"""

M52_IMP6_CASES = (
    {
        "name": "m52-imp6/policy-key-e2e",
        "group": "m52-imp6",
        "probe": M52_IMP6_PROBE,
        "expect_decimal": True,
        "output_span": (b"M52-IMP6-BEGIN!", b"M52-IMP6-END!"),
        # NO output_span_bytes.  brief.org section 9 forbids hard-coded
        # provisional bytes from the TERM=xterm terminfo: the span MUST be
        # derived from a real pty run, or INFO-skip.  This sandbox denies
        # pty allocation ("out of pty devices"), so the case INFO-skips
        # here.  When a pty is present the driver checks that the reported
        # byte count equals the real span length; the exact bytes stay
        # unverified until a host with a pty derives them.
        "env": {"TERM": "xterm"},
    },
)

M52_IMP7_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (write! (module-ref output 'tty-write-bytes))
       (emit! (module-ref output 'tty-emit-cap))
       (flush! (module-ref output 'tty-flush))
       (to-end (module-ref output 'tty-clear-to-end-steps))
       (frame (module-ref output 'tty-clear-frame-steps))
       (eol (module-ref output 'tty-clear-end-of-line-steps)))
  (if (not term)
      "no-tty-terminal"
    (begin
      ;; The 3 clear procedures return ONE step.  A KEY step is a plain
      ;; string that names one m52_caps key; the probe emits it through
      ;; --tty-emit-cap.  A MARKER step (the "clear-loop" /
      ;; "clear-frame-fallback" / "clear-line-hard" lists) carries a C
      ;; mechanism, so the probe skips it.  The bytes are NOT pinned
      ;; (brief.org section 5).
      (write! term #vu8(77 53 50 45 73 77 80 55 45 66 69 71 73 78 33))
      (let ((steps (list (to-end 1) (to-end 0)
                         (frame 1) (frame 0)
                         (eol 1 2 8 1) (eol 1 2 8 0) (eol 0 2 8 1)))
            (n 0))
        (for-each (lambda (s)
                    (if (string? s)
                        (set! n (+ n (emit! term s '())))
                        #f))
                  steps)
        (write! term #vu8(77 53 50 45 73 77 80 55 45 69 78 68 33))
        (let ((f (flush! term)))
          (if (= f 0) (number->string n) "flush-failed"))))))
"""

M52_IMP7_CASES = (
    {
        "name": "m52-imp7/policy-key-e2e",
        "group": "m52-imp7",
        "probe": M52_IMP7_PROBE,
        "expect_decimal": True,
        "output_span": (b"M52-IMP7-BEGIN!", b"M52-IMP7-END!"),
        # NO output_span_bytes.  brief.org section 5 forbids a hard-coded
        # TERM=xterm span: the span MUST come from a real pty run, or
        # INFO-skip.  This sandbox denies pty allocation ("out of pty
        # devices"), so the case INFO-skips here.  When a pty is present
        # the driver checks that the reported byte count equals the real
        # span length; the exact bytes stay unverified until a host with
        # a pty derives them.
        "env": {"TERM": "xterm"},
    },
)

M52_IMP8_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (write! (module-ref output 'tty-write-bytes))
       (emit! (module-ref output 'tty-emit-cap))
       (flush! (module-ref output 'tty-flush))
       (win (module-ref output 'tty-set-terminal-window-steps))
       (sr (module-ref output 'tty-set-scroll-region-steps))
       (del (module-ref output 'tty-delete-glyphs-steps))
       (idl (module-ref output 'tty-ins-del-lines-steps)))
  (if (not term)
      "no-tty-terminal"
    (begin
      ;; The 4 arithmetic procedures return a single step, an ordered
      ;; step list, or #nil.  A KEY step is a plain string that names one
      ;; m52_caps key; the probe emits it through --tty-emit-cap.  A
      ;; MARKER step (a list) carries a C mechanism, so the probe skips
      ;; it.  The bytes are NOT pinned (brief.org section 5).
      (write! term #vu8(77 53 50 45 73 77 80 56 45 66 69 71 73 78 33))
      (let ((steps (append
                    (win 0 40 1)
                    (win 40 40 0)
                    (list (sr 3 11 40 80 1 0 0))
                    (del 3 0 1)
                    (del 3 1 1)
                    (list (idl 5 3 40 40 1 1 1 0 1))))
            (n 0))
        (for-each (lambda (s)
                    (if (string? s)
                        (set! n (+ n (emit! term s '())))
                        #f))
                  steps)
        (write! term #vu8(77 53 50 45 73 77 80 56 45 69 78 68 33))
        (let ((f (flush! term)))
          ;; tty-flush returns 0 on success.  Return the byte count when
          ;; the flush succeeded, the sentinel "flush-failed" when it did
          ;; not.
          ;;
          ;; A zero byte count means a missing m52_caps row (the emit
          ;; returned 0).  The fixture TERM of this case defines smdc /
          ;; rmdc, so a correct row does emit bytes; a 0 count is then a
          ;; real gap, not a terminal that lacks the capability.  Return
          ;; a non-decimal string, so the driver's expect_decimal verdict
          ;; FAILS (int() raises).  The plain count "0" would PASS, so it
          ;; is not a signal.
          (if (= f 0)
              (if (>= n 1) (number->string n) "no-bytes")
            "flush-failed"))))))
"""

# Compile fixed terminfo entries without reading the host database.
M52_IMP8_TERM = "m52-imp8"
_fixture_dir = None
_fixture_tried = False


def terminfo_fixture(term):
    """Return the environment for a fixed entry, or None if unavailable."""
    global _fixture_dir, _fixture_tried
    if not _fixture_tried:
        _fixture_tried = True
        tic = shutil.which("tic")
        if tic is not None:
            try:
                directory = tempfile.mkdtemp(prefix="pty-terminfo-")
                atexit.register(shutil.rmtree, directory, True)
                source = os.path.join(os.path.dirname(__file__),
                                      "fixtures", "pty-terminfo.src")
                result = subprocess.run([tic, "-x", "-o", directory, source],
                                        stdout=subprocess.DEVNULL,
                                        stderr=subprocess.DEVNULL)
                compiled = {name for _, _, files in os.walk(directory)
                            for name in files}
                if result.returncode == 0 and all(
                        name in compiled for name in ("xterm", "ansi", M52_IMP8_TERM)):
                    _fixture_dir = directory
            except OSError:
                pass
    if _fixture_dir is None:
        return None
    return {"TERM": term, "TERMINFO": _fixture_dir,
            "TERMINFO_DIRS": _fixture_dir}


TERMINFO_FIXTURES = {name: (lambda term=name: terminfo_fixture(term))
                     for name in ("xterm", "ansi", M52_IMP8_TERM)}

M52_IMP8_CASES = (
    {
        "name": "m52-imp8/policy-key-e2e",
        "group": "m52-imp8",
        "probe": M52_IMP8_PROBE,
        "expect_decimal": True,
        "output_span": (b"M52-IMP8-BEGIN!", b"M52-IMP8-END!"),
        # NO output_span_bytes.  brief.org section 5 forbids a hard-coded
        # TERM=xterm span: the span MUST come from a real pty run, or
        # INFO-skip.  The count the probe reports IS checked against the
        # real pty span (check_output).
        #
        # The fixture TERM gives the 2 KEY steps of this group their live
        # terminfo strings (see the fixture note above).
        "terminfo_fixture": M52_IMP8_TERM,
    },
)

# M54 imp-2: the output after-write verdict.  The child resolves the
# (emacs tty-output) module, takes the last terminal of (emacs gobble),
# writes a marked span through tty-write-bytes, and flushes.  This
# proves the seam in m52_tty_write_1 does not drop, reorder, or
# duplicate a byte, and that the reported count equals the span length
# (so the after-write verdict path returned "done").  The span bytes are
# OUR OWN written bytes, so pinning them is allowed.
M54_IMP2_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (write! (module-ref output 'tty-write-bytes))
       (flush! (module-ref output 'tty-flush)))
  (if (not term)
      "no-tty-terminal"
    (begin
      (write! term #vu8(77 53 52 45 73 77 80 50 45 66 69 71 73 78 33))
      (flush! term)
      (let* ((bytes #vu8(77 53 52 45 73 77 80 50 45 87 82 73 84 69 79 75 33))
             (n (write! term bytes))
             (flushed (flush! term)))
        (write! term #vu8(77 53 52 45 73 77 80 50 45 69 78 68 33))
        (let ((end-flushed (flush! term)))
          (if (and (= n 17) (= flushed 0) (= end-flushed 0))
              (number->string n)
            "write-failed"))))))
"""

M54_IMP2_CASES = (
    {
        "name": "m54-imp2/output-write-verdict-e2e",
        "group": "m54-imp2",
        "probe": M54_IMP2_PROBE,
        "expect_decimal": True,
        "output_span": (b"M54-IMP2-BEGIN!", b"M54-IMP2-END!"),
        "output_span_bytes": b"M54-IMP2-WRITEOK!",
        "env": {"TERM": "xterm"},
    },
)

# M54 imp-3: the termscript copy decision.  A termscript is a COPY of the
# terminal output (src/termchar.h :61).  The child opens a real termscript
# file (open-termscript), writes a marked span through tty-write-bytes,
# and closes the termscript (open-termscript with no file flushes and
# closes it).  The driver then compares the bytes of the termscript FILE
# with the bytes read at the pty master: the copy MUST equal the output.
# The span bytes are OUR OWN written bytes, so pinning them is allowed.
M54_IMP3_BEGIN = b"M54-IMP3-BEGIN!"
M54_IMP3_WRITEOK = b"M54-IMP3-WRITEOK!"
M54_IMP3_END = b"M54-IMP3-END!"

M54_IMP3_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (ref (resolve-module '(emacs elisp-ref)))
       (c (module-ref ref '%c))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (write! (module-ref output 'tty-write-bytes))
       (flush! (module-ref output 'tty-flush)))
  (if (not term)
      "no-tty-terminal"
    (begin
      (write! term #vu8(@@BEGB@@))
      (flush! term)
      ((c 'open-termscript) "@@TSPATH@@")
      (let* ((bytes #vu8(@@OKB@@))
             (n (write! term bytes))
             (flushed (flush! term)))
        ((c 'open-termscript) #nil)
        (write! term #vu8(@@ENDB@@))
        (let ((end-flushed (flush! term)))
          (if (and (= n @@NC@@) (= flushed 0) (= end-flushed 0))
              (number->string n)
            "write-failed"))))))
"""

M54_IMP3_CASES = (
    {
        "name": "m54-imp3/termscript-copy-e2e",
        "group": "m54-imp3",
        "probe": M54_IMP3_PROBE,
        "subst": {"BEGB": " ".join(str(b) for b in M54_IMP3_BEGIN),
                  "OKB": " ".join(str(b) for b in M54_IMP3_WRITEOK),
                  "ENDB": " ".join(str(b) for b in M54_IMP3_END),
                  "NC": str(len(M54_IMP3_WRITEOK))},
        "expect_decimal": True,
        "output_span": (M54_IMP3_BEGIN, M54_IMP3_END),
        "output_span_bytes": M54_IMP3_WRITEOK,
        # The driver opens a real termscript file and compares its bytes
        # with the pty master span (brief.org section 11).
        "termscript": True,
        "env": {"TERM": "xterm"},
    },
)

# M54 imp-4: the input stream TAB policy.  The child runs on a real PTY
# with a tab-capable TERM (xterm) and a TabWidth of 8.  The seam runs on
# every tty init.  The probe drives a real horizontal CURSOR MOVE over a
# space run: the display engine's cmgoto path emits a hard-tab byte
# (0x09) when the decision is "tabs".  The case checks the observable
# byte, NOT a module load.  The BEGIN / END markers are our own bytes.
M54_IMP4_BEGIN = b"M54-IMP4-BEGIN!"
M54_IMP4_END = b"M54-IMP4-END!"

M54_IMP4_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (ref (resolve-module '(emacs elisp-ref)))
       (c (module-ref ref '%c))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms)))))
  (if (not term)
      "no-tty-terminal"
    (begin
      ((c 'send-string-to-terminal) "M54-IMP4-BEGIN!")
      ;; Drive a cursor move over a space run: fill the current line with
      ;; spaces, put point past a tab stop, and force a redisplay.  On a
      ;; tab-capable TERM the terminal path emits a hard-tab byte; the
      ;; driver checks that byte INSIDE this case's own BEGIN .. END span.
      ;; A tab-capable host that emits no byte FAILS; only a host whose
      ;; terminfo holds no "ht" capability INFO-skips (span_requires).
      ((c 'goto-char) ((c 'point-min)))
      ((c 'delete-region) ((c 'point-min)) ((c 'point-max)))
      ((c 'insert) "                                                                  ")
      ((c 'goto-char) 41)
      ((c 'redisplay) #t)
      ((c 'send-string-to-terminal) "M54-IMP4-END!")
      "ok")))
"""

M54_IMP4_CASES = (
    {
        "name": "m54-imp4/tab-policy-e2e",
        "group": "m54-imp4",
        "probe": M54_IMP4_PROBE,
        "expect": "ok",
        # The END marker proves the probe ran to completion on the real
        # terminal.  The hard-tab byte MUST appear INSIDE the case's own
        # BEGIN .. END span (the whole transcript is not the evidence).
        # The byte needs a tab-capable TERM: the terminfo "ht" string.
        # When the host terminfo defines "ht" the byte MUST be present,
        # else the case FAILS.  Only a host whose terminfo holds no "ht"
        # (so no HT byte can appear) is an explicit INFO skip
        # (brief.org section 7.2, cr.org F2).
        "pty_contains": M54_IMP4_END,
        "span_requires": {
            "span": (M54_IMP4_BEGIN, M54_IMP4_END),
            "needles": (b"\x09",),
            "capability": "ht",
        },
        "env": {"TERM": "xterm"},
    },
)

# --------------------------------------------------------------------
# M56 imp-2: the TTY init path on the real path.  See M56_IMP2_PROBE.
#
# The tty init path (C `init_tty', src/term.c) calls the three C1 rows:
# add_keyboard_wait_descriptor, get_tty_size, and init_baud_rate.  A case
# that boots the built src/emacs on a real PTY runs init_tty, so it runs
# all three rows.  Row 3 (init_baud_rate) READS the termios state on the
# C descriptor and WRITES the C global baud_rate; it has NO plain Scheme
# observable (brief.org section 4.1), so the case does NOT assert a baud
# value -- that is an honest limit, not a defect.  Because row 3 has no
# plain observable, the case pins the WHOLE init path by the terminal's
# live behaviour (brief.org section 4.2):
#
#   read  -- the child runs the (emacs gobble) read path once and reports
#            "<return>,<stored>";
#   write -- the child writes the BEGIN marker, the out bytes, and the
#            END marker, and reports the byte count; the driver checks the
#            span between the markers;
#   size  -- the driver resizes the PTY (TIOCSWINSZ) after READY, before
#            the gate; the child reads tty-size after the gate and
#            reports "<W>x<H>".  A size that follows the resize proves a
#            LIVE size query on the real descriptor.
#
# The report is ONE string, one line:
#
#   "read:<ret>,<stored> out:<n> size:<W>x<H>"
M56_IMP2_BEGIN = b"M56-IMP2-BEGIN!"
M56_IMP2_END = b"M56-IMP2-END!"
M56_IMP2_OUT_BYTES = b"M56-IMP2-TTY-INIT-OK!"
M56_IMP2_ROWS = 30
M56_IMP2_COLS = 100

M56_IMP2_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (modes (resolve-module '(emacs tty-modes)))
       (terms ((force (module-ref gobble '%terminal-list))))
       ;; %terminal-list is oldest-first, so the newest terminal is the
       ;; last element (see READ_PATH_PROBE).
       (term (let ((ts (reverse terms))) (and (pair? ts) (car ts))))
       (nr (module-ref gobble '%--kbd-buffer-nr-stored))
       (read! (module-ref gobble 'tty-read-avail-input!))
       (write! (module-ref output 'tty-write-bytes))
       (flush! (module-ref output 'tty-flush))
       (get-size (module-ref modes 'tty-size)))
  (if (not term)
      "no-tty-terminal"
    (let* ((readstr
            ;; Read input FIRST, right after the gate, before the write:
            ;; Emacs's own input poll can move pending tty bytes into
            ;; kbd_buffer during a longer step, and then FIONREAD reads 0.
            ;; Report the ACCOUNTED input as ONE number: the stored
            ;; kbd_buffer count after the read.  The read stores each
            ;; byte it reads, so this ONE count is the UNION of the two
            ;; accounting paths, counted once.  The count is 2 for BOTH
            ;; arms (a plain read and a winning poll), so it is RACE-PROOF
            ;; (cr.org F1).  Emacs's own input poll can move the pending
            ;; tty bytes into kbd_buffer before this probe runs; the old
            ;; ret,delta pair then read 0 and 0 and failed on that benign
            ;; variant.  The baseline is EMPTY by construction: the child
            ;; is freshly started and the driver writes nothing before
            ;; READY, and a resize SIGWINCH stores no kbd_buffer event.
            (let* ((ret (read! term))
                   (stored ((force nr))))
              (if (number? ret)
                  (number->string stored)
                  "read-failed")))
           (outstr
            (begin
              (write! term (string->utf8 "M56-IMP2-BEGIN!"))
              (let ((n (write! term #vu8(@@OUTBYTES@@))))
                (flush! term)
                (write! term (string->utf8 "M56-IMP2-END!"))
                (flush! term)
                (if (number? n) (number->string n) "write-failed"))))
           (sizestr
            (let ((sz (get-size 0)))
              (if (not (pair? sz))
                  "no-size"
                (string-append (number->string (car sz)) "x"
                               (number->string (cdr sz)))))))
      (string-append "read:" readstr
                     " out:" outstr
                     " size:" sizestr))))
"""

M56_IMP2_CASES = (
    {
        "name": "m56-imp2/tty-init-e2e",
        "group": "m56-imp2",
        "probe": M56_IMP2_PROBE,
        "subst": {"OUTBYTES": " ".join(str(b) for b in M56_IMP2_OUT_BYTES)},
        "bytes": b"AB",
        "expect": "read:2 out:%d size:%dx%d"
                  % (len(M56_IMP2_OUT_BYTES), M56_IMP2_COLS, M56_IMP2_ROWS),
        # The driver resizes the pty after READY, before the gate; the
        # child reads the size after the gate.  30x100 is NOT the pty
        # default, so the report proves the change and the live query.
        "resize": (M56_IMP2_ROWS, M56_IMP2_COLS),
        # The BEGIN / END markers are our own written bytes, so pinning
        # the span bytes is allowed (brief.org section 4.3).
        "output_span": (M56_IMP2_BEGIN, M56_IMP2_END),
        "output_span_bytes": M56_IMP2_OUT_BYTES,
        # The report is composite, so the driver extracts the out count.
        "output_count_re": r"out:(\d+)",
        "env": {"TERM": "xterm"},
    },
)

# --------------------------------------------------------------------
# M58 imp-2: the face-appearance POLICY on the real path (Group A).
#
# The C hub is turn_on_face / turn_off_face / tty_capable_p
# (src/term.c).  Its only callers are the glyph writers tty_write_glyphs /
# tty_write_glyphs_with_face / tty_insert_glyphs.  A probe that calls
# --tty-emit-cap or --tty-emit-seq does NOT reach that hub: only a real
# redisplay of text that CARRIES a face attribute calls it.  So this case
# drives the hub through a real redisplay, not through a leaf:
#
#   prelude -- runs in the child AFTER the READY letters and BEFORE the
#              gate read.  It changes the buffer the selected window
#              already shows (no new buffer that starts with a space),
#              inserts BEGIN + a bold "X" + END, and forces a redisplay.
#   probe   -- returns a constant.  It proves the child reached the report
#              step; it is NOT the evidence.
#   span    -- the driver requires the terminfo "bold" bytes INSIDE the
#              case's own BEGIN .. END span.  The markers are our own
#              bytes, so a span pin is allowed (the M56 imp-2 rule).  An
#              absent "bold" capability is an explicit INFO skip: no byte
#              can appear.  A capable host that emits no bold byte FAILS.
#
# The MOVE of the Group A decision is imp-3, and only after this check
# returns A1.  This case is EVIDENCE, not a migration.
M58_IMP2_BEGIN = b"M58-FACE-BEGIN!"
M58_IMP2_END = b"M58-FACE-END!"
# The fixed xterm fixture's bold capability.
M58_IMP2_BOLD = b"\x1b[1m"

M58_IMP2_PRELUDE = r"""
(progn
  ;; Change the buffer that the selected window ALREADY shows: do not
  ;; switch to a new buffer that starts with a space.
  (let ((buf (window-buffer (selected-window))))
    (with-current-buffer buf
      (erase-buffer)
      (insert "M58-FACE-BEGIN!")
      (insert (propertize "X" 'face 'bold))
      (insert "M58-FACE-END!")
      (goto-char (point-min))))
  (redisplay t)
  (sit-for 0))
"""

M58_IMP2_PROBE = r"""
;; The report is ONE string.  The evidence is the pty span between the
;; case's own markers, NOT this constant.
"face-emitted"
"""

M58_IMP2_CASES = (
    {
        "name": "m58-imp2/face-appearance-e2e",
        "group": "m58-imp2",
        "probe": M58_IMP2_PROBE,
        "prelude": M58_IMP2_PRELUDE,
        "bytes": b"",
        "expect": "face-emitted",
        # The END marker proves the child's redisplay ran to completion on
        # the real terminal.
        "pty_contains": M58_IMP2_END,
        # The bold bytes MUST appear INSIDE the case's own span.  The byte
        # needs the terminfo "bold" capability; a host without it is an
        # explicit INFO skip, never a pass.
        "span_requires": {
            "span": (M58_IMP2_BEGIN, M58_IMP2_END),
            "needles": (M58_IMP2_BOLD,),
            "capability": "bold",
        },
        "env": {"TERM": "xterm"},
    },
)

# --------------------------------------------------------------------
# M58 imp-3: the Group A face-appearance DECISION, after the MOVE.
#
# The MOVE (src/term.c + (emacs tty-output)) puts the DECISION in
# Scheme: tty-face-on-steps, tty-face-off-steps, and tty-capable-p.  C
# keeps every mechanism.  These cases are the real-path guard of the
# MOVE (brief.org section 5):
#
#   face-off-e2e       the exit sequence of turn_off_face alone (the
#                      "me" path, plus the ("clear-standout") step)
#   face-italic-e2e    italic using the fixed xterm capability
#   face-underline-e2e plain underline (the styled tparam route needs a
#                      Smulx capability; a host that has it uses the
#                      ("tparam" 3 N) step)
#   face-color-e2e     foreground and background through tparam
#   capable-p-e2e      the tty_capable_p verdict against the terminfo
#                      entry of the same TERM
#
# Each case uses its OWN marker pair and a prelude that inserts the
# markers plus face-carrying text, then (redisplay t).  The needle is
# scoped to the case's own span, so a byte elsewhere is not evidence.
M58_IMP3_OFF_BEGIN = b"M58I3-OFF-BEGIN!"
M58_IMP3_OFF_END = b"M58I3-OFF-END!"
M58_IMP3_ITALIC_BEGIN = b"M58I3-ITA-BEGIN!"
M58_IMP3_ITALIC_END = b"M58I3-ITA-END!"
M58_IMP3_UL_BEGIN = b"M58I3-UL-BEGIN!"
M58_IMP3_UL_END = b"M58I3-UL-END!"
M58_IMP3_COLOR_BEGIN = b"M58I3-COL-BEGIN!"
M58_IMP3_COLOR_END = b"M58I3-COL-END!"
M58_IMP3_CAP_BEGIN = b"M58I3-CAP-BEGIN!"
M58_IMP3_CAP_END = b"M58I3-CAP-END!"

# The imp-2 bold byte, re-used as the turn_on_face needle of the
# face-off case: the case pins the EXIT bytes, and the bold byte proves
# the face was on before the exit.
M58_IMP3_BOLD = b"\x1b[1m"
# The fixed xterm fixture's italic capability (terminfo "sitm").
M58_IMP3_ITALIC = b"\x1b[3m"
# The exit-attribute capability ("me").  MEASURED on this host from the
# imp-2 face span (the byte that follows the bold "X"); the emacs
# terminfo lookup and the Python curses binding do not agree on this
# string, so the value is measured, not derived.  turn_off_face writes it
# through OUTPUT1_IF, then the ("clear-standout") step, then the
# orig-pair reset.
M58_IMP3_ME = b"\x1b[0m"
# The underline capability (terminfo "smul").
M58_IMP3_UNDERLINE = b"\x1b[4m"
# setaf / setab through tparam.  MEASURED on this host: the child's tty
# color map resolves EVERY color name to index 0, so the measured bytes
# are setaf 0 / setab 0.  The case therefore pins the two color STEP
# routes in order (bold, then foreground, then background), not the
# numeric color value -- an honest limit, recorded in the close-out.
M58_IMP3_SETAF_RED = b"\x1b[30m"
M58_IMP3_SETAB_BLUE = b"\x1b[40m"


def _m58_imp3_face_prelude(begin, end, face_spec):
    """Return a child PRELUDE that shows FACE-SPEC text between markers."""
    return """
(progn
  (let ((buf (window-buffer (selected-window))))
    (with-current-buffer buf
      (erase-buffer)
      (insert "%s")
      (insert (propertize "X" 'face %s))
      (insert "%s")
      (goto-char (point-min))))
  (redisplay t)
  (sit-for 0))
""" % (begin.decode(), face_spec, end.decode())


def _m58_imp3_color_prelude():
    """Return a PRELUDE that shows a bold RED-ON-BLUE named face."""
    return """
(progn
  (let ((buf (window-buffer (selected-window))))
    (with-current-buffer buf
      (erase-buffer)
      (insert "%s")
      (insert (propertize "X" 'face 'm58-imp3-color-face))
      (insert "%s")
      (goto-char (point-min))))
  (make-face 'm58-imp3-color-face)
  (set-face-attribute 'm58-imp3-color-face nil
                      :weight 'bold :foreground "red" :background "blue")
  (redisplay t)
  (sit-for 0))
""" % (M58_IMP3_COLOR_BEGIN.decode(), M58_IMP3_COLOR_END.decode())


M58_IMP3_PROBE = r"""
"face-emitted"
"""

M58_IMP3_CAPABLE_PROBE = r"""
(let* ((ref (resolve-module '(emacs elisp-ref)))
       (c (module-ref ref '%c))
       (ask (c 'display-supports-face-attributes-p))
       (verdict (lambda (spec) (if (ask spec) 1 0))))
  (format #f "bold:~a italic:~a underline:~a"
          (verdict (list :bold #t))
          (verdict (list :italic #t))
          (verdict (list :underline #t))))
"""


# The fixed xterm entry provides italic mode.
_M58_IMP3_ITALIC_NEEDLE = M58_IMP3_ITALIC
M58_IMP3_ITALIC_CAP = "sitm"

M58_IMP3_CASES = (
    {
        "name": "m58-imp3/face-off-e2e",
        "group": "m58-imp3",
        "probe": M58_IMP3_PROBE,
        "prelude": _m58_imp3_face_prelude(M58_IMP3_OFF_BEGIN,
                                          M58_IMP3_OFF_END, "'bold"),
        "bytes": b"",
        "expect": "face-emitted",
        "pty_contains": M58_IMP3_OFF_END,
        "span_requires": {
            "span": (M58_IMP3_OFF_BEGIN, M58_IMP3_OFF_END),
            "needles": (M58_IMP3_BOLD, M58_IMP3_ME),
            "capability": "bold",
        },
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m58-imp3/face-italic-e2e",
        "group": "m58-imp3",
        "probe": M58_IMP3_PROBE,
        "prelude": _m58_imp3_face_prelude(M58_IMP3_ITALIC_BEGIN,
                                          M58_IMP3_ITALIC_END, "'italic"),
        "bytes": b"",
        "expect": "face-emitted",
        "pty_contains": M58_IMP3_ITALIC_END,
        "span_requires": {
            "span": (M58_IMP3_ITALIC_BEGIN, M58_IMP3_ITALIC_END),
            "needles": (_M58_IMP3_ITALIC_NEEDLE,),
            "capability": M58_IMP3_ITALIC_CAP,
        },
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m58-imp3/face-underline-e2e",
        "group": "m58-imp3",
        "probe": M58_IMP3_PROBE,
        "prelude": _m58_imp3_face_prelude(M58_IMP3_UL_BEGIN,
                                          M58_IMP3_UL_END, "'underline"),
        "bytes": b"",
        "expect": "face-emitted",
        "pty_contains": M58_IMP3_UL_END,
        "span_requires": {
            "span": (M58_IMP3_UL_BEGIN, M58_IMP3_UL_END),
            "needles": (M58_IMP3_UNDERLINE,),
            "capability": "smul",
        },
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m58-imp3/face-color-e2e",
        "group": "m58-imp3",
        "probe": M58_IMP3_PROBE,
        # A NAMED face, set up in the prelude: an anonymous face list
        # did not reach the C hub on this host (no byte changed), so the
        # case uses the same route a user face takes.
        "prelude": _m58_imp3_color_prelude(),
        "bytes": b"",
        "expect": "face-emitted",
        "pty_contains": M58_IMP3_COLOR_END,
        "span_requires": {
            "span": (M58_IMP3_COLOR_BEGIN, M58_IMP3_COLOR_END),
            "needles": (M58_IMP3_SETAF_RED, M58_IMP3_SETAB_BLUE),
            # The ORDER binds the color bytes to the face's OWN
            # turn_on_face run: the bold byte can only come from that run,
            # and the two color steps must follow it.
            "needles_in_order": (M58_IMP3_BOLD, M58_IMP3_SETAF_RED,
                                 M58_IMP3_SETAB_BLUE),
            "capability": "setaf",
        },
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m58-imp3/capable-p-e2e",
        "group": "m58-imp3",
        "probe": M58_IMP3_CAPABLE_PROBE,
        # The answer is a Lisp value, not a byte: the probe reports the
        # verdict of display-supports-face-attributes-p, which reaches
        # tty_capable_p (src/xfaces.c).  The expectation comes from the
        # terminfo entry of the SAME TERM, so a mismatch is a real FAIL.
        # A host with no loadable terminfo is an explicit INFO skip.
        "expect_terminfo": (("bold", "bold"), ("italic", "sitm"),
                            ("underline", "smul")),
        "pty_contains": M58_IMP3_CAP_END,
        "prelude": _m58_imp3_face_prelude(M58_IMP3_CAP_BEGIN,
                                          M58_IMP3_CAP_END, "'bold"),
        "env": {"TERM": "xterm"},
    },
)

# --------------------------------------------------------------------
# M58 imp-4: the Group B color-mode DECISION, after the MOVE.
#
# The MOVE (src/term.c + (emacs tty-output)) puts the DECISION in
# Scheme: tty-color-mode-tag (the canonicalization and the -1 / 0 / 8
# scheme choice of tty_setup_colors) and tty-color-mode-changed-p (the
# change gate of set_tty_color_mode).  C keeps every mechanism.
#
# The trigger is a FRAME SWITCH.  set_tty_color_mode has one caller,
# redisplay_internal, and that call tests the terminal's previous_frame.
# A plain (redisplay t) on the same frame does NOT run the gate, so the
# probe makes a SECOND tty frame on the same terminal and switches.
#
# The case pins a VALUE, not a byte span: ("8 0 8") from
# tty-display-color-cells, the only observable of the scheme choice.
#
#   switch 1  mode 8    the 8-color scheme gives 8 cells
#   switch 2  mode -5   the canonicalization: -5 becomes -1 -> 0 cells
#   switch 3  mode 8    the gate fires a SECOND time (a stuck gate
#                       leaves 0, the value of switch 2)
#
# The 3 values do not depend on the terminfo entry of the host, so the
# case does NOT use expect_terminfo and does NOT use span_requires.
#
# A host that cannot create a second tty frame reports the NARROW
# m58-imp4-skip: prefix.  Every other error reaches the driver as a
# FAIL.
#
# Negative control (measured 2026-10-19 on this tree, then reverted):
# with tty-color-mode-changed-p forced to return 0 always reports
# "8 8 8", not "8 0 8".  The first value repeats, so the SECOND switch
# no longer reaches tty_setup_colors.  The case is green again after the
# revert.
M58_IMP4_END = b"M58I4-END!"

M58_IMP4_PROBE = r"""
(let* ((ref (resolve-module '(emacs elisp-ref)))
       (c (module-ref ref '%c))
       (make-frame (c 'make-frame))
       (select-frame (c 'select-frame))
       (set-param (c 'set-frame-parameter))
       (redisplay (c 'redisplay))
       (cells (c 'tty-display-color-cells))
       (selected (c 'selected-frame))
       (send (c 'send-string-to-terminal))
       (switch (lambda (frame mode)
                 (set-param frame 'tty-color-mode mode)
                 (select-frame frame)
                 (redisplay #t)
                 (cells)))
       (f1 (selected))
       (f2 (catch #t (lambda () (make-frame)) (lambda args #f))))
  (if (not f2)
      (string-append "m58-imp4-skip: cannot make a second tty frame")
      (let ((a (switch f2 8))
            (b (switch f1 -5))
            (d (switch f2 8)))
        (send "M58I4-END!")
        (format #f "~a ~a ~a" a b d))))
"""

M58_IMP4_SKIP = "m58-imp4-skip:"

M58_IMP4_CASES = (
    {
        "name": "m58-imp4/color-mode-e2e",
        "group": "m58-imp4",
        "probe": M58_IMP4_PROBE,
        # Two tty frames on one terminal, 3 frame switches.  The value
        # 8 0 8 proves the canonicalization (-5 gives -1 gives 0 cells)
        # and a gate that fires two times.
        "expect": "8 0 8",
        "pty_contains": M58_IMP4_END,
        # The ONLY skip: the probe's own prefix.  Every other mismatch
        # is a real FAIL.
        "info_report_prefix": M58_IMP4_SKIP,
        "env": {"TERM": "xterm"},
    },
)

# M61 imp-1: the opaque per-TTY handle.  The child runs on a real PTY and
# writes through the ONE ordered output path in three ways: the elisp
# send-string-to-terminal path, the new typed handle leaf, and the normal
# glyph write of a redisplay.  The case pins the byte ORDER inside its own
# BEGIN .. END span, so a byte that arrives in the wrong place FAILS.  No
# source text is read: the bytes at the pty master are the evidence.
M61_IMP1_BEGIN = b"M61-IMP1-BEGIN!"
M61_IMP1_END = b"M61-IMP1-END!"
M61_IMP1_A = b"M61-IMP1-A|"
M61_IMP1_HANDLE = b"M61-IMP1-B|"
M61_IMP1_GLYPH = b"M61-IMP1-GLYPH"
M61_IMP1_C = b"M61-IMP1-C|"

# Take the handle of the newest terminal, then write in one known order.
# The report is "ok" only when the handle path counted every byte it was
# asked to write.
M61_IMP1_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (ref (resolve-module '(emacs elisp-ref)))
       (c (module-ref ref '%c))
       (terms ((force (module-ref gobble '%terminal-list))))
       ;; %terminal-list is oldest-first, so the newest terminal is the
       ;; last element (see READ_PATH_PROBE).
       (term (let ((ts (reverse terms))) (and (pair? ts) (car ts))))
       (handle (and term ((module-ref output 'tty-handle-from-device) term)))
       (write! (module-ref output 'tty-handle-write-all))
       ;; M61 imp-2b: the routed answers are the plain carrier
       ;; #(count errno), so the probe reads the count and the errno with
       ;; the exported accessors (milestone.org findings F1 and F3).
       (ocount (module-ref output 'tty-handle-outcome-count))
       (oerrno (module-ref output 'tty-handle-outcome-errno)))
  (if (not handle)
      "no-tty-handle"
    (let* ((send (lambda (s) ((c 'send-string-to-terminal) s)))
           (_b (send "@@BEGIN@@"))
           (_a (send "@@A@@"))
           ;; Path 1: the typed handle leaf, through the Scheme retry loop.
           (n (write! handle #vu8(@@HANDLEBYTES@@)))
           ;; Path 2: the NORMAL glyph write (tty_write_glyphs), through a
           ;; real redisplay of a real buffer.
           (_g (begin ((c 'goto-char) ((c 'point-max)))
                      ((c 'insert) "@@GLYPH@@")
                      ((c 'redisplay) #t)))
           ;; Path 3: the elisp path again, to prove the order holds AFTER
           ;; a glyph write.
           (_c (send "@@CBYTES@@"))
           (_e (send "@@END@@")))
      (if (and (= (ocount n) @@HANDLEN@@) (= (oerrno n) 0))
          "ok"
          "handle-count"))))
"""

M61_IMP1_LARGE_N = 65536
M61_IMP1_LARGE = bytes(65 + (i % 26) for i in range(M61_IMP1_LARGE_N))

# The same handle path with a payload larger than one pty buffer, so the
# write can be short.  tty-handle-write-all retries through the ONE
# verdict procedure until every byte is out.  The span bytes pin the
# ORDER of the payload, so a lost or reordered byte FAILS.
M61_IMP1_LARGE_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (ref (resolve-module '(emacs elisp-ref)))
       (bvmod (resolve-module '(rnrs bytevectors)))
       (mkbv (module-ref bvmod 'make-bytevector))
       (u8set (module-ref bvmod 'bytevector-u8-set!))
       (c (module-ref ref '%c))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (let ((ts (reverse terms))) (and (pair? ts) (car ts))))
       (handle (and term ((module-ref output 'tty-handle-from-device) term)))
       (write! (module-ref output 'tty-handle-write-all))
       (ocount (module-ref output 'tty-handle-outcome-count))
       (oerrno (module-ref output 'tty-handle-outcome-errno))
       (n @@N@@)
       (payload (let ((bv (mkbv n 0)))
                  (let loop ((i 0))
                    (if (< i n)
                        (begin (u8set bv i (+ 65 (modulo i 26)))
                               (loop (+ i 1)))
                        bv)))))
  (if (not handle)
      "no-tty-handle"
    (let* ((send (lambda (s) ((c 'send-string-to-terminal) s)))
           (_b (send "@@BEGIN@@"))
           (answer (write! handle payload))
           (_e (send "@@END@@")))
      ;; A probe value is a STRING (the report format), so the total count
      ;; leaves as a decimal string.
      (if (and (= 0 (oerrno answer)) (number? (ocount answer)))
          (number->string (ocount answer))
          (if (vector? answer) "write-errno" answer)))))
"""

# The bounded BOOTSTRAP case (cr.org F5).  The ONE leaf of the handle layer
# that still accepts a Lisp DEVICE is --tty-handle.  This probe proves:
#   1. DEVICE -> identity: a terminal object gives a plain positive fixnum.
#   2. the identity is STABLE: a second bootstrap names the same number.
#   3. the state is borrowed: imp-1 moves no ownership.
#   4. the leaf + the Scheme retry loop accept the identity alone: an empty
#      write of the real stream answers 0.
#   5. an identity that the C table does not hold answers -EBADF (-9), as a
#      PLAIN value: no longjmp, no error escape.
M61_IMP1_BOOT_PROBE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (from-device (module-ref output 'tty-handle-from-device))
       (write-all (module-ref output 'tty-handle-write-all-borrowed))
       (ocount (module-ref output 'tty-handle-outcome-count))
       (oerrno (module-ref output 'tty-handle-outcome-errno))
       (id-of (module-ref output 'tty-handle-id))
       (state-of (module-ref output 'tty-handle-state))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (let ((ts (reverse terms))) (and (pair? ts) (car ts))))
       (h (and term (from-device term)))
       (h2 (and term (from-device term))))
  (cond ((not h) "no-tty-handle")
        ((not (and (integer? (id-of h)) (> (id-of h) 0))) "bad-identity")
        ((not (eq? 'borrowed (state-of h))) "bad-state")
        ((not (equal? (id-of h) (id-of h2))) "identity-not-stable")
        ((not (= 0 (ocount (write-all (id-of h) #vu8())))) "empty-write")
        ((not (= 0 (oerrno (write-all (id-of h) #vu8())))) "empty-write-errno")
        ;; -EBADF is 9 on this host, as a POSITIVE errno in the carrier.
        ((not (and (= 0 (ocount (write-all 1000000 #vu8(65))))
                   (= 9 (oerrno (write-all 1000000 #vu8(65))))))
         "closed-not-ebadf")
        (else "ok")))
"""

M61_IMP1_CASES = (
    {
        "name": "m61-imp1/byte-order-e2e",
        "group": "m61-imp1",
        "probe": M61_IMP1_PROBE,
        "subst": {"BEGIN": M61_IMP1_BEGIN.decode(),
                  "A": M61_IMP1_A.decode(),
                  "HANDLEBYTES": " ".join(str(b) for b in M61_IMP1_HANDLE),
                  "HANDLEN": str(len(M61_IMP1_HANDLE)),
                  "GLYPH": M61_IMP1_GLYPH.decode(),
                  "CBYTES": M61_IMP1_C.decode(),
                  "END": M61_IMP1_END.decode()},
        "expect": "ok",
        # A non-numeric report cannot use output_span (the driver parses
        # that report as a byte count), so the END marker proves the probe
        # ran to completion and span_requires pins the order.
        "pty_contains": M61_IMP1_END,
        # The three writes must arrive in THIS order inside the span.
        "span_requires": {
            "span": (M61_IMP1_BEGIN, M61_IMP1_END),
            "needles": (M61_IMP1_HANDLE, M61_IMP1_GLYPH),
            "needles_in_order": (M61_IMP1_A, M61_IMP1_HANDLE,
                                 M61_IMP1_GLYPH, M61_IMP1_C),
        },
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp1/clean-exit-e2e",
        "group": "m61-imp1",
        "probe": M61_IMP1_PROBE,
        "subst": {"BEGIN": M61_IMP1_BEGIN.decode(),
                  "A": M61_IMP1_A.decode(),
                  "HANDLEBYTES": " ".join(str(b) for b in M61_IMP1_HANDLE),
                  "HANDLEN": str(len(M61_IMP1_HANDLE)),
                  "GLYPH": M61_IMP1_GLYPH.decode(),
                  "CBYTES": M61_IMP1_C.decode(),
                  "END": M61_IMP1_END.decode()},
        "expect": "ok",
        "pty_contains": M61_IMP1_END,
        # Exit 0 and the terminal mode restored.  The write path changed,
        # so the restore path is re-proved here, not assumed.
        "capture_mode": True,
        "wait_exit": True,
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp1/large-write-e2e",
        "group": "m61-imp1",
        "probe": M61_IMP1_LARGE_PROBE,
        "subst": {"BEGIN": M61_IMP1_BEGIN.decode(),
                  "END": M61_IMP1_END.decode(),
                  "N": str(M61_IMP1_LARGE_N)},
        # The bare decimal report is the total count of the handle path.
        "expect_decimal": True,
        "output_span": (M61_IMP1_BEGIN, M61_IMP1_END),
        # Every payload byte must arrive in order: a short write that were
        # dropped or reordered fails this compare.
        "output_span_bytes": M61_IMP1_LARGE,
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp1/bootstrap-e2e",
        "group": "m61-imp1",
        "probe": M61_IMP1_BOOT_PROBE,
        # No byte order to compare: this case checks the plain identity
        # contract, so the report is the whole result.
        "expect": "ok",
        "env": {"TERM": "xterm"},
    },
)

# M61 imp-2: 1 private termscript file per case.  The probe opens it with
# open-termscript, reads it back, and the driver never touches it, so a
# stale file can not make a case pass.
def _m61_imp2_tsfile(name):
    directory = tempfile.mkdtemp(prefix="m61-imp2-")
    atexit.register(shutil.rmtree, directory, True)
    return os.path.join(directory, name + ".termscript")


# M61 imp-2: the flush and the termscript copy on the per-TTY handle.
# The child runs on a real PTY and uses the 2 new operations of
# (emacs tty-output).  The proof is real behavior: the probe reads the
# termscript FILE it opened, and the driver reads the pty master.  No
# source text is read.
#
# LIMIT: a termscript file records the COPIED bytes only, so it can not
# observe the order of 2 writes on 2 different streams.  The order check
# below is therefore: the copies reach the termscript stream in the order
# of the operations.  The C order itself (output write first, copy second)
# is a 1-line reading of m61_tty_handle_glyph_run_1 in src/term.c.
M61_IMP2_BEGIN = b"M61-IMP2-BEGIN!"
M61_IMP2_END = b"M61-IMP2-END!"
M61_IMP2_FLUSH = b"M61-IMP2-FLUSH"
M61_IMP2_TS_LEAF = b"M61-IMP2-TSLEAF"
M61_IMP2_TS_GLYPH = b"M61-IMP2-TSGLYPH"
M61_IMP2_TS_A = b"M61-IMP2-TS-A|"
M61_IMP2_TS_B = b"M61-IMP2-TS-B|"
M61_IMP2_ORD_A = b"M61-IMP2-ORD-A|"
M61_IMP2_ORD_B = b"M61-IMP2-ORD-B|"
M61_IMP2_SKIP = "m61-imp2-skip:"

# The shared Scheme helpers: read a whole file as a string, and find the
# first index of NEEDLE in TEXT at or after FROM (-1 when absent).  The
# probe text lands inside ONE (begin ...), so these are internal defines.
M61_IMP2_HELPERS = r"""
(define (m61-imp2-slurp path)
  (call-with-input-file path
    (lambda (port)
      (let loop ((acc '()))
        (let ((ch (read-char port)))
          (if (eof-object? ch)
              (list->string (reverse acc))
              (loop (cons ch acc))))))))
(define (m61-imp2-index text needle from)
  (let ((n (string-length needle)) (m (string-length text)))
    (let loop ((i from))
      (cond ((> (+ i n) m) -1)
            ((string=? (substring text i (+ i n)) needle) i)
            (else (loop (+ i 1)))))))
"""

M61_IMP2_HANDLE_PRELUDE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (ref (resolve-module '(emacs elisp-ref)))
       (c (module-ref ref '%c))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (handle (and term ((module-ref output 'tty-handle-from-device) term)))
       (flush! (and handle (module-ref output 'tty-handle-flush)))
       (copy! (and handle (module-ref output 'tty-handle-termscript)))
       ;; M61 imp-2b: the copy answers the plain carrier #(count errno).
       (ocount (module-ref output 'tty-handle-outcome-count))
       (oerrno (module-ref output 'tty-handle-outcome-errno))
       (open! (c 'open-termscript))
       (ti (c 'insert))
       (goto (c 'goto-char))
       (pmax (c 'point-max))
       (redisplay! (c 'redisplay))
       (send (c 'send-string-to-terminal)))
  (if (not handle)
      "no-tty-handle"
"""

# A glyph run with NO trailing newline.  The bytes can reach the pty master
# only when a flush of the ordered path runs, so their arrival in the pty
# span IS the proof that the flush happened after the display.
M61_IMP2_FLUSH_PROBE = M61_IMP2_HELPERS + M61_IMP2_HANDLE_PRELUDE + r"""
    (begin
      (send "@@BEGIN@@")
      (goto (pmax))
      (ti "@@NEEDLE@@")
      (redisplay! #t)
      (let ((rc (flush! handle))
            ;; No termscript file is open in this case, so the copy leaf
            ;; must answer the carrier #(0 0): a plain count of 0 and NOT
            ;; an error.  A session without a termscript stream is legal.
            (none (copy! handle #vu8(65))))
        (send "@@END@@")
        (cond ((not (= rc 0)) "flush-answer")
              ((not (= 0 (ocount none))) "no-termscript-count")
              ((not (= 0 (oerrno none))) "no-termscript-answer")
              (else "ok"))))))
"""

# The 2 streams must hold the SAME bytes: the leaf copies a known payload
# and must answer its exact count, and the normal glyph write of a real
# redisplay must reach the termscript stream too.  The probe reads the
# termscript FILE back, so a copy that is dropped FAILS.
M61_IMP2_TS_PROBE = M61_IMP2_HELPERS + M61_IMP2_HANDLE_PRELUDE + r"""
    (begin
      (open! "@@TSFILE@@")
      (let ((n (copy! handle #vu8(@@LEAFBYTES@@))))
        (goto (pmax))
        (ti "@@GLYPH@@")
        (redisplay! #t)
        (open! #nil)
        (let* ((text (m61-imp2-slurp "@@TSFILE@@"))
               (i1 (m61-imp2-index text "@@LEAFSTR@@" 0))
               (i2 (m61-imp2-index text "@@GLYPH@@" 0)))
          (cond ((not (= (ocount n) @@LEAFN@@)) "leaf-count")
                ((not (= 0 (oerrno n))) "leaf-errno")
                ((< i1 0) "leaf-bytes-missing")
                ((< i2 0) "glyph-bytes-missing")
                (else "ok")))))))
"""

# The order contract: the termscript copy of one operation sits after the
# copy of the operations that ran before it.  The probe writes A, then a
# glyph run, then B, and reads the indices back from the termscript FILE.
M61_IMP2_TS_ORDER_PROBE = M61_IMP2_HELPERS + M61_IMP2_HANDLE_PRELUDE + r"""
    (begin
      (open! "@@TSFILE@@")
      (let ((na (copy! handle #vu8(@@ABYTES@@))))
        (goto (pmax))
        (ti "@@GLYPH@@")
        (redisplay! #t)
        (let ((nb (copy! handle #vu8(@@BBYTES@@))))
          (open! #nil)
          (let* ((text (m61-imp2-slurp "@@TSFILE@@"))
                 (ia (m61-imp2-index text "@@ASTR@@" 0))
                 (ig (m61-imp2-index text "@@GLYPH@@" 0))
                 (ib (m61-imp2-index text "@@BSTR@@" 0)))
            (cond ((not (and (= (ocount na) @@AN@@) (= (ocount nb) @@BN@@)))
                   "copy-count")
                  ((not (and (= 0 (oerrno na)) (= 0 (oerrno nb)))) "copy-errno")
                  ((< ia 0) "a-missing")
                  ((< ig 0) "glyph-missing")
                  ((< ib 0) "b-missing")
                  ((not (< ia ig)) "glyph-before-a")
                  ((not (< ig ib)) "b-before-glyph")
                  (else "ok"))))))))
"""

# The byte-order contract of section 3 on BOTH streams: 2 glyph runs of 2
# different strings must reach the output stream and the termscript stream
# in the order of the runs.  The driver checks the pty master, the probe
# checks the termscript FILE.
M61_IMP2_BYTE_ORDER_PROBE = M61_IMP2_HELPERS + M61_IMP2_HANDLE_PRELUDE + r"""
    (begin
      (open! "@@TSFILE@@")
      (goto (pmax))
      (ti "@@A@@")
      (redisplay! #t)
      (goto (pmax))
      (ti "@@B@@")
      (redisplay! #t)
      (send "@@END@@")
      (open! #nil)
      (let* ((text (m61-imp2-slurp "@@TSFILE@@"))
             (ia (m61-imp2-index text "@@A@@" 0))
             (ib (m61-imp2-index text "@@B@@" 0)))
        (cond ((not (= 0 (ocount (copy! handle #vu8())))) "empty-copy-count")
              ((not (= 0 (oerrno (copy! handle #vu8())))) "empty-copy-errno")
              ((< ia 0) "a-missing")
              ((< ib 0) "b-missing")
              ((not (< ia ib)) "b-before-a")
              (else "ok"))))))
"""

# The ZERO-PROGRESS copy case (milestone.org findings F3, the review of
# 2026-10-30 CR7).  A SHORT copy of a regular file can not be forced on
# this host, but a copy that moves NO byte CAN: /dev/full answers ENOSPC on
# every write, so =fwrite= answers 0 with the error flag set and
# m61_tty_output_termscript_1 takes its hard-failure branch.  The probe
# pins BOTH values of the carrier, so a lost count and a lost errno each
# FAIL: count 0, and the positive ENOSPC (28 on Linux).
#
# The PARTIAL copy (some bytes, then a hard failure) stays a GAP: no
# bounded file makes the first =fwrite= short and the second one fail.
#
# A host without /dev/full reports the narrow SKIP of this case.
# The payload is LARGER than one stdio buffer, so =fwrite= must flush in
# the middle of the call: /dev/full then answers a SHORT count with ENOSPC.
M61_IMP2_FULL_PAYLOAD = bytes([65]) * 8192

M61_IMP2_SHORT_PROBE = M61_IMP2_HELPERS + M61_IMP2_HANDLE_PRELUDE + r"""
    (if (not (file-exists? "/dev/full"))
        (string-append "m61-imp2-skip: this host has no /dev/full")
        (begin
          (open! "/dev/full")
          (let ((answer (copy! handle #vu8(@@LEAFBYTES@@))))
            (open! #nil)
            ;; MEASURED on this host: a copy of 8192 bytes to /dev/full
            ;; answers the carrier #(0 28) -- ENOSPC (28) and zero
            ;; progress.  Both values are pinned, so a lost errno and a
            ;; lost count each FAIL.
            (cond ((not (= 0 (ocount answer))) "full-copy-count")
                  ((not (= 28 (oerrno answer))) "full-copy-errno")
                  (else "ok")))))))
"""

# The CARRIER SHAPE of the output leaf itself (review cr.org CR2).  No
# fixture is needed: an identity that the C table does not hold answers
# -EBADF before any =fwrite= runs (m61_tty_handle_of_identity_1 answers
# NULL).  The case pins the CARRIER #(0 9): the probe requires a 2-slot
# vector and reads its 2 slots, so a return to the plain fixnum answer
# -9 FAILS.  This is behavior, not a source scan.
M61_IMP2_LEAF_PROBE = r"""
(let* ((ref (resolve-module '(emacs elisp-ref)))
       (c (module-ref ref '%c))
       (leaf (c '--tty-handle-write))
       (answer (leaf 1000000 #vu8(65 66 67))))
  (cond ((not (and (vector? answer) (= 2 (vector-length answer))))
         "not-a-carrier")
        ((not (= 0 (vector-ref answer 0))) "closed-count")
        ;; -EBADF is 9 on this host, as a POSITIVE errno in the carrier.
        ((not (= 9 (vector-ref answer 1))) "closed-errno")
        (else "ok")))
"""

M61_IMP2_CASES = (
    {
        "name": "m61-imp2/byte-order-e2e",
        "group": "m61-imp2",
        "probe": M61_IMP2_BYTE_ORDER_PROBE,
        "subst": {"TSFILE": _m61_imp2_tsfile("byteorder"),
                  "A": M61_IMP2_ORD_A.decode(),
                  "B": M61_IMP2_ORD_B.decode(),
                  "END": M61_IMP2_END.decode()},
        "expect": "ok",
        # The ORDER of the 2 runs on the output stream: A, then B, then the
        # end marker.  A driver that only looked for both needles would
        # accept the wrong order.
        "pty_in_order": (M61_IMP2_ORD_A, M61_IMP2_ORD_B, M61_IMP2_END),
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp2/flush-order-e2e",
        "group": "m61-imp2",
        "probe": M61_IMP2_FLUSH_PROBE,
        "subst": {"BEGIN": M61_IMP2_BEGIN.decode(),
                  "NEEDLE": M61_IMP2_FLUSH.decode(),
                  "END": M61_IMP2_END.decode()},
        "expect": "ok",
        # A glyph run with no trailing newline reaches the pty only after a
        # flush.  The needle is our own text, so pinning it is allowed.
        "pty_contains": M61_IMP2_FLUSH,
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp2/termscript-agreement-e2e",
        "group": "m61-imp2",
        "probe": M61_IMP2_TS_PROBE,
        "subst": {"TSFILE": _m61_imp2_tsfile("agreement"),
                  "LEAFBYTES": " ".join(str(b) for b in M61_IMP2_TS_LEAF),
                  "LEAFSTR": M61_IMP2_TS_LEAF.decode(),
                  "LEAFN": str(len(M61_IMP2_TS_LEAF)),
                  "GLYPH": M61_IMP2_TS_GLYPH.decode()},
        "expect": "ok",
        "pty_contains": M61_IMP2_TS_GLYPH,
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp2/termscript-order-e2e",
        "group": "m61-imp2",
        "probe": M61_IMP2_TS_ORDER_PROBE,
        "subst": {"TSFILE": _m61_imp2_tsfile("order"),
                  "ABYTES": " ".join(str(b) for b in M61_IMP2_TS_A),
                  "ASTR": M61_IMP2_TS_A.decode(),
                  "AN": str(len(M61_IMP2_TS_A)),
                  "BBYTES": " ".join(str(b) for b in M61_IMP2_TS_B),
                  "BSTR": M61_IMP2_TS_B.decode(),
                  "BN": str(len(M61_IMP2_TS_B)),
                  "GLYPH": M61_IMP2_TS_GLYPH.decode()},
        "expect": "ok",
        "pty_contains": M61_IMP2_TS_GLYPH,
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp2/short-write-e2e",
        "group": "m61-imp2",
        "probe": M61_IMP2_SHORT_PROBE,
        "subst": {"LEAFBYTES": " ".join(str(b) for b in M61_IMP2_FULL_PAYLOAD)},
        # The case runs a real copy that fails on /dev/full.
        "expect": "ok",
        # The NARROW skip: only a host WITHOUT /dev/full reports it.
        "info_report_prefix": M61_IMP2_SKIP,
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp2/clean-exit-e2e",
        "group": "m61-imp2",
        "probe": M61_IMP2_FLUSH_PROBE,
        "subst": {"BEGIN": M61_IMP2_BEGIN.decode(),
                  "NEEDLE": M61_IMP2_FLUSH.decode(),
                  "END": M61_IMP2_END.decode()},
        "expect": "ok",
        "pty_contains": M61_IMP2_FLUSH,
        # Exit 0 and the terminal mode restored.  The flush path changed,
        # so the restore path is re-proved here, not assumed.
        "capture_mode": True,
        "wait_exit": True,
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp2/leaf-carrier-e2e",
        "group": "m61-imp2",
        "probe": M61_IMP2_LEAF_PROBE,
        "subst": {},
        # The answer SHAPE of --tty-handle-write is read here: a return to
        # the plain fixnum -9 can not pass the probe (review cr.org CR2).
        "expect": "ok",
        "env": {"TERM": "xterm"},
    },
)

# --- M61 imp-2g: a failed output dispatch is observable (F5) ---------
#
# The ordered output path must ANSWER its result and it must hand the
# measured count to the caller, and the termscript copy of 1 run must
# agree with the output of that run.  The cases run the built src/emacs
# on a real PTY and call the ONE hub (src/term.c
# m61_tty_handle_glyph_run_1) through the leaf --tty-glyph-run, so the
# answer is read from the real C path and not from a Scheme copy of it.
#
# The RECOVERY rule of brief.org section 5.2 is DESIGN 2, and the 3 glyph
# call sites of src/term.c state it: a MEASURED incomplete run sets
# SET_FRAME_GARBAGED, and a run of UNKNOWN progress does not, because that
# state can repeat at every run.  The cases below read the rule with
# --frame-garbaged-p and the report seam with a redefinition of
# tty-glyph-run-policy, which the C hub reads at EACH failed run.
M61_IMP2G_RUN = b"M61-IMP2G-RUN|"          # the clean run, then a newline
M61_IMP2G_RAISE = b"M61-IMP2G-EIORUN|"     # the run whose write raises
M61_IMP2G_NEEDLE = b"M61-IMP2G-REPAINT|"   # the text of the failed redisplay
M61_IMP2G_PREFIX_RUN = b"M61-IMP2G-PREFIX|"  # the run whose write moves 5 bytes
M61_IMP2G_PREFIX_P = 5                     # the measured prefix of that run

# The shared prelude of the probes: the tty of the session, the leaf that
# runs ONE glyph run, the leaf that reads the repaint request, and the
# helper that asks the recorded reports of the seam for an unknown state.
M61_IMP2G_PRELUDE = M61_IMP2_HELPERS + r"""
(define (m61-imp2g-unknown-reported? reports)
  (cond ((null? reports) #f)
        ((eq? #t (list-ref (car reports) 3)) #t)
        (else (m61-imp2g-unknown-reported? (cdr reports)))))
;; M61 imp-3: the byte values of a probe literal and a "holds this run"
;; test.  The capability path now crosses the SAME hub, so a redisplay
;; makes capability runs before its glyph run.  A case that injects a
;; failure must NAME the glyph run of its own text, not the first call.
(define (m61-imp2g-byte-list s)
  (let loop ((i (- (string-length s) 1)) (acc '()))
    (if (< i 0) acc
        (loop (- i 1) (cons (char->integer (string-ref s i)) acc)))))
(define (m61-imp2g-holds? bytes needle)
  (let ((n (bytevector-length bytes)) (k (length needle)))
    (let loop ((i 0))
      (cond ((> (+ i k) n) #f)
            ((let inner ((j 0))
               (cond ((= j k) #t)
                     ((= (bytevector-u8-ref bytes (+ i j)) (list-ref needle j))
                      (inner (+ j 1)))
                     (else #f)))
             #t)
            (else (loop (+ i 1)))))))
""" + r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (ref (resolve-module '(emacs elisp-ref)))
       (c (module-ref ref '%c))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (run (c '--tty-glyph-run))
       (garbaged? (c '--frame-garbaged-p))
       (open! (c 'open-termscript))
       (ti (c 'insert))
       (goto (c 'goto-char))
       (pmax (c 'point-max))
       (redisplay! (c 'redisplay))
       (send (c 'send-string-to-terminal)))
"""

# A clean session: the answer of the run is 0, the count is the whole
# run, the bytes of the 2 streams agree, and the frame is NOT garbaged.
# A hub that drops the answer or the count again can not pass this case,
# and neither can a call site that repaints a complete run (criterion 3
# of brief.org section 9, review cr.org C2).
M61_IMP2G_CLEAN_PROBE = M61_IMP2G_PRELUDE + r"""
  (if (not term)
      "no-terminal"
      (begin
        (open! "@@TSFILE@@")
        (let* ((answer (run term #vu8(@@BYTES@@)))
               (status (vector-ref answer 0))
               (written (vector-ref answer 1))
               (garbaged (garbaged? #nil)))
          (open! #nil)
          (let* ((text (m61-imp2-slurp "@@TSFILE@@"))
                 (i (m61-imp2-index text "@@STR@@" 0)))
            (cond ((not (and (vector? answer) (= 2 (vector-length answer))))
                   "not-an-answer")
                  ((not (= 0 status)) "status-not-0")
                  ((not (= @@N@@ written)) "count-not-the-run")
                  ((< i 0) "termscript-disagrees")
                  (garbaged "clean-run-garbaged-the-frame")
                  (else "ok")))))))
"""

# The PREFIX case: a write that moves P bytes and then answers a hard
# error.  The fixture is injected at the SAME binding that the C hub
# reads (tty-handle-write-all-borrowed), so the REAL C hub
# m61_tty_handle_glyph_run_1 runs: it must answer -ENOSPC with the
# measured prefix 5, and the termscript must hold exactly that prefix and
# NOT the whole run (statement 3 of brief.org section 4, prefix case).
#
# The injected carrier claims the 5 bytes without moving them, so this
# case proves the REPORT and the COPY rule of a measured prefix.  The
# fwrite-level fixture (a real short =fwrite=) stays a GAP: MEASURED HOST
# LIMIT -- =tty->output= is always a pty in a PTY session.  /dev/full as
# the OUTPUT stream answers ENOSPC with count 0, which is the
# ZERO-progress shape and not the prefix shape, and a pty that is full
# BLOCKS instead of answering a short count.  A regular file at its
# RLIMIT_FSIZE does give the shape -- MEASURED with 2 =fwrite= calls of
# 65536 bytes under "ulimit -f 16": n1=16384 e1=27 ferror1=1, then
# n2=4096 e2=27 -- but no elisp or PTY path can make =tty->output= such a
# file.  milestone.org section 5 keeps that row.
M61_IMP2G_PREFIX_PROBE = M61_IMP2G_PRELUDE + r"""
  (if (not term)
      "no-terminal"
      (let* ((injected
              ;; 1 MEASURED prefix of the run, then a hard ENOSPC.  The
              ;; real C hub reads the carrier #(count errno), so it reports
              ;; the errno AND the 5 bytes that moved.  The carrier is built
              ;; here as the plain vector, so the probe needs no import of
              ;; the Scheme helper into the child's toplevel.
              (lambda (identity bytes) (vector @@P@@ @@ERRNO@@))))
        (open! "@@TSFILE@@")
        (module-set! output 'tty-handle-write-all-borrowed injected)
        (let* ((answer (run term #vu8(@@BYTES@@)))
               (status (vector-ref answer 0))
               (written (vector-ref answer 1)))
          (open! #nil)
          (let ((text (m61-imp2-slurp "@@TSFILE@@")))
            (cond ((not (and (vector? answer) (= 2 (vector-length answer))))
                   "not-an-answer")
                  ((not (= @@NEG@@ status)) "status-not-enospc")
                  ((not (= @@P@@ written)) "prefix-count")
                  ((< (m61-imp2-index text "@@P5@@" 0) 0)
                   "termscript-lost-the-prefix")
                  ((>= (m61-imp2-index text "@@STR@@" 0) 0)
                   "termscript-holds-the-run")
                  (else "ok")))))))
"""

# The CR2 LENGTH case (M61 imp-2g, brief.org A1 / review cr.org CR3): a
# PARTIAL glyph run whose measured prefix is 5 of 17 bytes.  The case reads
# the TERMSCRIPT FILE itself and measures the BYTES that the copy added:
# the copy is COPY_LEN = 5 and NOT LEN = 17.  A whole run in a partial copy
# is finding F5 itself, so this case is the proof of the length contract of
# the seam and not an inspection of it.
#
# The injection point is the carrier binding that the C hub reads
# (tty-handle-write-all-borrowed), so the REAL C hub
# m61_tty_handle_glyph_run_1 runs and it decides the copy length.  The
# fwrite-level short write stays a named host limit (milestone.org
# section 5): tty->output is always a pty in a PTY session.
M61_IMP2G_COPYLEN_PROBE = M61_IMP2G_PRELUDE + r"""
  (if (not term)
      "no-terminal"
      (let* ((injected
              (lambda (identity bytes) (vector @@P@@ @@ERRNO@@))))
        (open! "@@TSFILE@@")
        (module-set! output 'tty-handle-write-all-borrowed injected)
        (let* ((before (string-length (m61-imp2-slurp "@@TSFILE@@")))
               (answer (run term #vu8(@@BYTES@@)))
               (status (vector-ref answer 0))
               (written (vector-ref answer 1)))
          (open! #nil)
          (let* ((text (m61-imp2-slurp "@@TSFILE@@")))
            ;; NOTE: `string-length' counts CHARACTERS.  The fixture is
            ;; ASCII, so the count equals the byte count here.  A
            ;; non-ASCII fixture must read the file as a bytevector.
            (let ((delta (- (string-length text) before)))
              (cond ((not (and (vector? answer) (= 2 (vector-length answer))))
                     "not-an-answer")
                    ((not (= @@NEG@@ status)) "status-not-enospc")
                    ((not (= @@P@@ written)) "prefix-count")
                    ;; COPY_LEN = 5 of LEN = 17.  The file must hold the
                    ;; measured prefix and NOT the whole run.
                    ((not (= @@P@@ delta)) "copy-len-not-the-prefix")
                    ((= @@N@@ delta) "termscript-holds-the-run")
                    ((< (m61-imp2-index text "@@P5@@" 0) 0)
                     "termscript-lost-the-prefix")
                    (else "ok"))))))))
"""

# The -EIO case, through the REAL C hub: a raise AFTER 1 measured call.
# The injection point is the module procedure that the retry loop
# resolves: tty-handle-write-all-borrowed.  It answers 1 MEASURED call and
# then raises, so the prefix is on the terminal and the rest of the run is
# not.  The C hub must answer -EIO with the count 0 (progress UNKNOWN, NOT
# a measured 0), the termscript must hold NONE of that run (the 2 streams
# may differ, and a copy of the whole run would be the defect itself), the
# report seam must run with UNKNOWN = #t, and the frame must NOT be
# garbaged: DESIGN 2 of brief.org section 5.2 keeps SET_FRAME_GARBAGED for
# a MEASURED incomplete run only, because a repaint of an unknown state
# can not converge.  The second redisplay shows that nothing is left
# pending.
#
# MEASURED 2026-10-31: a redefinition of the LEAF tty-handle-write does
# NOT reach the hub, because the compiled retry loop calls its leaf
# directly and a declared module is inlined.
M61_IMP2G_RAISE_PROBE = M61_IMP2G_PRELUDE + r"""
  (if (not term)
      "no-terminal"
      (let* ((real-all (module-ref output 'tty-handle-write-all-borrowed))
             (real-policy (module-ref output 'tty-glyph-run-policy))
             (reports '())
             (calls 0)
             (injected
              (lambda (identity bytes)
                (set! calls (+ calls 1))
                (if (= calls 1)
                    (begin
                      ;; 1 measured call: a prefix of the run reaches the
                      ;; terminal, so the rest of the run is NOT known.
                      (real-all identity bytes)
                      (error "m61-imp2g: inject a raise after 1 measured call"))
                    (real-all identity bytes)))))
        ;; The C hub reads the module VARIABLE at each failed run, so this
        ;; redefinition observes the report of the real seam.
        (module-set! output 'tty-glyph-run-policy
                     (lambda (written len err unknown)
                       (set! reports (cons (list written len err unknown)
                                           reports))
                       (real-policy written len err unknown)))
        (open! "@@TSFILE@@")
        (module-set! output 'tty-handle-write-all-borrowed injected)
        (let* ((answer (run term #vu8(@@BYTES@@)))
               (status (vector-ref answer 0))
               (written (vector-ref answer 1)))
          (set! calls 0)
          (send "@@BEGIN@@")
          (goto (pmax))
          (ti "@@NEEDLE@@")
          (redisplay! #t)
          (let ((garbaged (garbaged? #nil)))
            (redisplay! #t)
            (let ((still (garbaged? #nil)))
              (open! #nil)
              (let ((text (m61-imp2-slurp "@@TSFILE@@")))
                (cond ((not (and (vector? answer) (= 2 (vector-length answer))))
                       "not-an-answer")
                      ;; -EIO is 5 on this host: the negated status.
                      ((not (= -5 status)) "status-not-eio")
                      ((not (= 0 written)) "unknown-count")
                      ((>= (m61-imp2-index text "@@STR@@" 0) 0)
                       "termscript-holds-the-run")
                      ((not (m61-imp2g-unknown-reported? reports))
                       "seam-not-reported")
                      (garbaged "unknown-progress-repainted")
                      (still "unknown-progress-repainted")
                      (else "ok")))))))))
"""

# The -EIO case with a raise BEFORE the first byte (brief.org section 6.4,
# review cr.org C6).  NOTHING of the run is on the terminal and nothing is
# on the termscript, so this is a DIFFERENT state from the case above: the
# measured prefix is 0 because there is no prefix, and the progress is
# still UNKNOWN.  The F1 rule applies: no byte is replayed and no byte is
# copied.  The session must survive the raise (the probe reports "ok" and
# the driver reads exit 0), the seam must report UNKNOWN, and the frame
# must not be garbaged.
M61_IMP2G_RAISE_FIRST_PROBE = M61_IMP2G_PRELUDE + r"""
  (if (not term)
      "no-terminal"
      (let* ((real-policy (module-ref output 'tty-glyph-run-policy))
             (reports '())
             (injected
              (lambda (identity bytes)
                (error "m61-imp2g: inject a raise before the first byte"))))
        (module-set! output 'tty-glyph-run-policy
                     (lambda (written len err unknown)
                       (set! reports (cons (list written len err unknown)
                                           reports))
                       (real-policy written len err unknown)))
        (open! "@@TSFILE@@")
        (module-set! output 'tty-handle-write-all-borrowed injected)
        (let* ((answer (run term #vu8(@@BYTES@@)))
               (status (vector-ref answer 0))
               (written (vector-ref answer 1))
               (garbaged (garbaged? #nil)))
          (open! #nil)
          (let ((text (m61-imp2-slurp "@@TSFILE@@")))
            (cond ((not (and (vector? answer) (= 2 (vector-length answer))))
                   "not-an-answer")
                  ((not (= -5 status)) "status-not-eio")
                  ((not (= 0 written)) "unknown-count")
                  ((>= (m61-imp2-index text "@@STR@@" 0) 0)
                   "termscript-holds-the-run")
                  ((not (m61-imp2g-unknown-reported? reports))
                   "seam-not-reported")
                  (garbaged "unknown-progress-repainted")
                  (else "ok")))))))
"""

# The REPAINT case (brief.org section 6.4, last row): a MEASURED
# incomplete run must be observable at a safe boundary, and the repaint
# must CONVERGE.  The injection answers 1 measured prefix and a hard
# ENOSPC on the ONE glyph run of this probe's own text in one redisplay,
# so the real C call site of that run must set the frame garbaged, and the
# next redisplay must clear the request and reach a stable picture.  A call
# site that never sets the flag fails this case; a call site that sets it
# again on every run fails the second read.
#
# M61 imp-3: the capability path crosses the SAME hub, so one redisplay
# makes capability runs BEFORE its glyph run.  The injection therefore
# names the glyph run by the bytes of NEEDLE, and it does not count calls.
# A capability call site ignores the answer (brief.org section 5), so a
# failure on a capability run would never set the flag.
M61_IMP2G_REPAINT_PROBE = M61_IMP2G_PRELUDE + r"""
  (if (not term)
      "no-terminal"
      (let* ((real-all (module-ref output 'tty-handle-write-all-borrowed))
             (needle (m61-imp2g-byte-list "@@NEEDLE@@"))
             (failed #f)
             (injected
              (lambda (identity bytes)
                (if (and (not failed) (m61-imp2g-holds? bytes needle))
                    (begin
                      (set! failed #t)
                      (vector @@P@@ @@ERRNO@@))
                    (real-all identity bytes)))))
        (module-set! output 'tty-handle-write-all-borrowed injected)
        (send "@@BEGIN@@")
        (goto (pmax))
        (ti "@@NEEDLE@@")
        (redisplay! #t)
        (let ((garbaged (garbaged? #nil)))
          (redisplay! #t)
          (let ((cleared (garbaged? #nil)))
            (cond ((not failed) "glyph-run-not-seen")
                  ((not garbaged) "no-repaint")
                  (cleared "repaint-not-cleared")
                  (else "ok")))))))
"""

M61_IMP2G_CASES = (
    {
        "name": "m61-imp2g/clean-run-e2e",
        "group": "m61-imp2g",
        "probe": M61_IMP2G_CLEAN_PROBE,
        "subst": {"TSFILE": _m61_imp2_tsfile("imp2g-clean"),
                  "BYTES": " ".join(str(b) for b in M61_IMP2G_RUN + b"\n"),
                  "STR": M61_IMP2G_RUN.decode(),
                  "N": str(len(M61_IMP2G_RUN + b"\n"))},
        # The negative control: the answer 0, the whole count, the 2
        # streams agree, and the frame is untouched.
        "expect": "ok",
        "pty_contains": M61_IMP2G_RUN,
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp2g/prefix-e2e",
        "group": "m61-imp2g",
        "probe": M61_IMP2G_PREFIX_PROBE,
        # The real C hub reports the injected prefix: -ENOSPC and 5 moved
        # bytes, and the termscript holds those 5 bytes only.
        "subst": {"TSFILE": _m61_imp2_tsfile("imp2g-prefix"),
                  "BYTES": " ".join(str(b) for b in M61_IMP2G_PREFIX_RUN),
                  "STR": M61_IMP2G_PREFIX_RUN.decode(),
                  "P5": M61_IMP2G_PREFIX_RUN[:5].decode(),
                  "P": str(M61_IMP2G_PREFIX_P),
                  "ERRNO": str(errno.ENOSPC),
                  "NEG": str(-errno.ENOSPC)},
        "expect": "ok",
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp2g/copy-len-e2e",
        "group": "m61-imp2g",
        "probe": M61_IMP2G_COPYLEN_PROBE,
        # CR2: the termscript holds COPY_LEN = 5 bytes of a 17-byte run.
        "subst": {"TSFILE": _m61_imp2_tsfile("imp2g-copylen"),
                  "BYTES": " ".join(str(b) for b in M61_IMP2G_PREFIX_RUN),
                  "STR": M61_IMP2G_PREFIX_RUN.decode(),
                  "P5": M61_IMP2G_PREFIX_RUN[:5].decode(),
                  "P": str(M61_IMP2G_PREFIX_P),
                  "N": str(len(M61_IMP2G_PREFIX_RUN)),
                  "ERRNO": str(errno.ENOSPC),
                  "NEG": str(-errno.ENOSPC)},
        "expect": "ok",
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp2g/raise-e2e",
        "group": "m61-imp2g",
        "probe": M61_IMP2G_RAISE_PROBE,
        "subst": {"TSFILE": _m61_imp2_tsfile("imp2g-raise"),
                  "BYTES": " ".join(str(b) for b in M61_IMP2G_RAISE),
                  "STR": M61_IMP2G_RAISE.decode(),
                  "BEGIN": M61_IMP2_BEGIN.decode(),
                  "NEEDLE": M61_IMP2G_NEEDLE.decode()},
        "expect": "ok",
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp2g/raise-first-e2e",
        "group": "m61-imp2g",
        "probe": M61_IMP2G_RAISE_FIRST_PROBE,
        # A raise BEFORE the first byte: no prefix, no copy, and the
        # session survives (C6).
        "subst": {"TSFILE": _m61_imp2_tsfile("imp2g-raise-first"),
                  "BYTES": " ".join(str(b) for b in M61_IMP2G_RAISE),
                  "STR": M61_IMP2G_RAISE.decode()},
        "expect": "ok",
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp2g/repaint-e2e",
        "group": "m61-imp2g",
        "probe": M61_IMP2G_REPAINT_PROBE,
        # A measured incomplete run asks for a repaint, and the next
        # redisplay clears the request: no loop.
        "subst": {"BYTES": " ".join(str(b) for b in M61_IMP2G_PREFIX_RUN),
                  "NEEDLE": M61_IMP2G_NEEDLE.decode(),
                  "BEGIN": M61_IMP2_BEGIN.decode(),
                  "P": str(M61_IMP2G_PREFIX_P),
                  "ERRNO": str(errno.ENOSPC)},
        "expect": "ok",
        "env": {"TERM": "xterm"},
    },
)

# --- M61 imp-3: the capability output runs through the ONE handle ------
#
# brief.org section 3 puts ONE sink in front of the 4 capability macros of
# src/term.c, so a whole capability string crosses the M61 handle ONCE
# instead of one crossing for each byte.
#
# These cases drive a REAL capability from Emacs, so the bytes cross the
# real OUTPUT macro and the real sink.  They do NOT call the Scheme emitter
# tty-emit-cap: that is the M52 path, and it does not cross src/term.c.
#
# The bell route: (ding t) -> ring_bell -> the tty hook tty_ring_bell ->
# OUTPUT (tty, tty->TS_bell) after the Scheme selection
# m52_tty_ring_bell_scheme.  With TERM=xterm and the default visible-bell
# nil the selection answers "bell", and "bl" is 1 byte.  Each probe checks
# FIRST that "bl" is a non-empty string and reports the narrow SKIP below
# when it is not: an empty capability moves no byte, so the case would
# prove nothing.
#
# ORDER CHANGE (brief.org section 6): the termscript copy of a capability
# run now takes the WHOLE string after the output write of that string.
# The C path interleaved the 2 streams per byte.  The bytes do not change;
# the CONTENT ORDER of the termscript does.  The termscript-order case
# below is the proof, and this comment states the change.
M61_IMP3_BEGIN = b"M61-IMP3-BEGIN!"
M61_IMP3_MID = b"M61-IMP3-MID|"
M61_IMP3_END = b"M61-IMP3-END!"
M61_IMP3_BELL = b"\x07"
M61_IMP3_SKIP = "m61-imp3-skip:"
# The exact narrow-skip text of short-write-e2e (cr.org C9).
M61_IMP3_SHORT_SKIP = ("m61-imp3-skip: a full pty BLOCKS, so a short "
                       "capability write can not be forced on this host")

# The measured crossing pair of ONE bell capability run, with 2 crossings
# of headroom in each direction.  MEASURED 2026-10-31 on the built tree
# with the bounds set to 0: the reset, the bell run and the read of the
# counters answer c2s=4 / s2c=3.  A later change that adds a dispatch to
# the run fails cross-count-e2e.  The case comment states the limit.
M61_IMP3_CROSS_MAX_C2S = 6
M61_IMP3_CROSS_MAX_S2C = 6

# The shared prelude: the tty of the session, the "bell" capability string
# that the C path will emit, the elisp routes to the markers and to the
# bell, and the routes that move glyphs.  The cond ends with an OPEN
# "else" clause, so each probe appends 1 expression and the 3 closers of
# the clause, the cond and the let*.
M61_IMP3_PRELUDE = r"""
(let* ((gobble (resolve-module '(emacs gobble)))
       (output (resolve-module '(emacs tty-output)))
       (ref (resolve-module '(emacs elisp-ref)))
       (c (module-ref ref '%c))
       (bell-cap (module-ref output 'tty-ring-bell-cap))
       (terms ((force (module-ref gobble '%terminal-list))))
       (term (and (pair? terms) (car (reverse terms))))
       (bl (and term (bell-cap 0 0)))
       (send (c 'send-string-to-terminal))
       (ding (c 'ding))
       (ti (c 'insert))
       (goto (c 'goto-char))
       (pmax (c 'point-max))
       (redisplay! (c 'redisplay))
       (reset-cross! (c 'debug-reset-guile-cross-count))
       (cross-count (c 'debug-guile-cross-count))
       (open! (c 'open-termscript)))
  (cond ((not term) "no-terminal")
        ((not (and (string? bl) (> (string-length bl) 0)))
         "m61-imp3-skip: TERM gives no non-empty bell capability")
        (else
"""

# ONE capability run between 2 markers.  The driver reads the pty master,
# so the bell byte must sit between the markers and in that order.
M61_IMP3_CAP_PROBE = M61_IMP3_PRELUDE + r"""
          (begin
            (send "@@BEGIN@@")
            (ding #t)
            (send "@@END@@")
            "ok")
        )))
"""

# The control against a sink that eats bytes: a glyph run still moves its
# bytes while the capability sink is in the path.  A capability byte first,
# then the glyph text, then the end marker.
M61_IMP3_GLYPH_PROBE = M61_IMP3_PRELUDE + r"""
          (begin
            (send "@@BEGIN@@")
            (ding #t)
            (goto (pmax))
            (ti "@@NEEDLE@@")
            (redisplay! #t)
            (send "@@END@@")
            "ok")
        )))
"""

# The ORDER of the bell path: 2 capability runs with a marker between
# them.  The bell byte of the first run precedes the mid marker, and the
# bell byte of the second run follows it.
#
# LIMIT (cr.org C4): that order does NOT prove the routed flush.  Both
# streams are stdio streams, and a stdio stream keeps the write order with
# or without fflush.  So this case stays green when the flush of
# tty_ring_bell is removed.  It proves the byte order only.  The flush has
# no isolating PTY case; milestone.org section 4 holds that limit.
M61_IMP3_FLUSH_PROBE = M61_IMP3_PRELUDE + r"""
          (begin
            (send "@@BEGIN@@")
            (ding #t)
            (send "@@MID@@")
            (ding #t)
            (send "@@END@@")
            "ok")
        )))
"""

# The CROSSING COUNT of ONE capability run (cr.org C5).  The act exists to
# replace 1 handle crossing for each capability BYTE with 1 crossing for
# each capability STRING.  Reset the counters of src/eval.c, run 1 bell,
# then read the pair and pin an UPPER bound on it.  This checks behavior,
# not source text.
#
# The "bl" string of xterm is 1 byte, so this run can not show the gain of
# the whole-string sink over a per-byte sink.  It pins the dispatch shape
# of a run (the bell selection, the sink-to-hub write and the flush) and
# turns red when a later change adds a crossing to that shape.
M61_IMP3_CROSS_PROBE = M61_IMP3_PRELUDE + r"""
          (begin
            (reset-cross!)
            (ding #t)
            (let ((counts (cross-count)))
              (let ((c2s (car counts)) (s2c (cdr counts)))
                (if (and (<= c2s @@MAXC2S@@) (<= s2c @@MAXS2C@@))
                    "ok"
                    (string-append
                     "crossing count " (number->string c2s) "/"
                     (number->string s2c) " exceeds the bound "
                     "@@MAXC2S@@/@@MAXS2C@@ of ONE capability run")))))
        )))
"""

# The NEWLINE FALLBACK run (cr1.org 2026-11-01 C2).  tty_set_terminal_modes
# emits N newlines when the terminal carries no termcap mode string:
#   EMACS_INT n = FRAME_TOTAL_LINES (selected frame);
#   m61_tty_emit_cap_repeat_1 (tty, '\n', n);
# The N bytes must collect in the ONE sink and cross the handle ONCE PER
# CHUNK, that is ceil (N / 1024) times.  A per-byte loop crosses n times,
# which is the C2 defect.
#
# The run is NOT reachable from the startup path of TERM=xterm: xterm
# holds smcup, so TS_termcap_modes is set and the newline branch does not
# run.  MEASURED 2026-11-01 on this host: `infocmp ansi | grep -c smcup'
# answers 0 and `infocmp xterm | grep -c smcup' answers 1.  So TERM=ansi
# does run the branch at startup, with tty=/dev/tty.  That startup run
# can not be measured: the counters of src/eval.c can not be reset before
# init_display, and the crossing count of a whole startup is not stable
# enough to hold a line-count delta.
#
# So this case forces ONE later run: the internal leaf
# --init-controlling-tty-sys-modes (src/keyboard.c) wraps init_sys_modes
# on the controlling tty, which calls terminal->set_terminal_modes_hook.
# The counters are reset before that call and read after it, so the delta
# covers ONE newline run and the few crossings of the mode-set itself.
# No new leaf is added for the test.
#
# E6 of cr.org: the probe reads the frame height BEFORE it resets the
# counters, so the crossings of the height read are NOT inside the delta.
# The height read and the N marker sit outside the measured range.  The
# BEGIN marker is INSIDE it, so it adds its 1 crossing to the pair; that
# is the measured reason why the base pair is 9/15 and not 8/15.
#
# The case pins an UPPER bound on the pair and derives that bound from
# the frame line count that it reads, so the bound scales with N
# (cr1.org 2026-11-01 C2).  It ALSO proves that the run HAPPENED: the
# probe sends BEGIN, runs the mode set, sends END, and the driver counts
# the newline bytes of that span on the pty master (E4 of cr.org).  The N
# newlines are visible there, so this is no one-sided bound.
#
# MEASURED 2026-11-01 on the built tree: 9/15 at a frame of 23 lines with
# the ONE-run sink, and 32/38 with the per-byte loop put back (the
# negative control of brief.org 2026-11-01 section 7.3).  The N marker
# and the BEGIN marker of E4 put 1 crossing into the delta, so the base
# pair moved from 8/15 to 9/15 when that proof was added.  The sink pair
# does not grow with N; the per-byte pair grows by N, so a DERIVED bound
# separates them on every frame of 3 lines or more.
#
# LIMIT 1 (cr1.org 2026-11-01 C1): this case does not prove C1.
# current_tty is a C cursor state and no probe can read it.  C1 is
# proven by code and by the unchanged byte order only.  Claim no
# coverage for C1 here.
#
# LIMIT 2 (cr1.org 2026-11-01 C1): the probe reads the Lisp height
# (frame-height, lisp/frame.el), and C passes FRAME_TOTAL_LINES (XFRAME
# (selected_frame)) to the run (src/term.c).  On a tty frame the 2
# values agree, so the bound describes the real N.  A frame with a menu
# bar or a minibuffer difference would separate them, and the bound
# would then describe a different N than the run.
#
# LIMIT 3 (the hollow-pass row of E4 of cr.org): CLOSED on this host, and
# it stays a host value.  `infocmp ansi | grep -c smcup' answers 0 here,
# so the newline branch runs and the span holds N newline bytes.  On a
# host whose `ansi' entry holds smcup the branch does not run, the span
# holds no newline byte, and the case FAILS: it does not pass on an upper
# bound alone.  MEASURE that value before the case is trusted on a new
# host.
#
# LIMIT 4 (cr.org R6): C3 is proven by code, not by a case.  m61_cap_begin
# starts with eassert (!m61_cap_active), so a NESTED emit stops there in a
# development build, and m61_cap_finish restores current_tty.  No nested
# emit occurs today (milestone.org 2026-10-31 section 4, "the sink is not
# reentrant"), so no case can reach that branch.  MEASURED 2026-11-01:
# `grep -c 'define ENABLE_CHECKING' src/config.h' answers 0, so eassert is
# a no-op in the binary under test.
M61_IMP3_NEWLINE_PROBE = r"""
(let* ((ref (resolve-module '(emacs elisp-ref)))
       (c (module-ref ref '%c))
       (reset-cross! (c 'debug-reset-guile-cross-count))
       (cross-count (c 'debug-guile-cross-count))
       (init-modes! (c '--init-controlling-tty-sys-modes))
       (height (c 'frame-height))
       (send (lambda (s) ((c 'send-string-to-terminal) s))))
  ;; E6 of cr.org: the height read comes FIRST, so its crossings are
  ;; outside the delta that the bound describes.
  (let* ((lines (height)))
    (if (<= lines @@SKIP_LINES@@)
        (string-append
         "m61-imp3-skip: the frame holds @@SKIP_LINES@@ lines or fewer, so"
         " ONE newline run can not differ from a per-byte run")
        (begin
          ;; E4 of cr.org: the N marker carries the line count to the
          ;; driver, which counts the newline bytes of the BEGIN .. END
          ;; span on the pty master.  So a run that never happened can not
          ;; pass on the upper bound alone.
          (send (string-append "M61-IMP3-N=" (number->string lines) "|"))
          (reset-cross!)
          (send "@@BEGIN@@")
          (init-modes!)
          (send "@@END@@")
          (let* ((counts (cross-count))
                 (c2s (car counts)) (s2c (cdr counts))
                 ;; The bound is DERIVED from lines, never a constant pin:
                 ;; a per-byte loop answers base + lines, so a constant
                 ;; bound stays green on a short frame (cr1.org
                 ;; 2026-11-01 C2).  MARGIN keeps a slack of 2 crossings
                 ;; even on the shortest gated frame (cr.org R5).
                 (slack (+ @@MARGIN@@ (quotient lines @@SLACK_DIV@@)))
                 (max-c2s (+ @@BASE_C2S@@ slack))
                 (max-s2c (+ @@BASE_S2C@@ slack)))
            (cond ((and (<= c2s max-c2s) (<= s2c max-s2c)) "ok")
                  (else
                   (string-append
                    "crossing count " (number->string c2s) "/"
                    (number->string s2c) " lines " (number->string lines)
                    " exceeds the bound " (number->string max-c2s) "/"
                    (number->string max-s2c) " of ONE newline run"))))))))
"""

# The crossing pair bound of ONE newline run: a CONSTANT base (the
# crossings of the mode-set itself, which does not grow with N) plus a
# fixed MARGIN of 2 crossings and a slack of N / 4.
#
# Why the slack, and not a constant pin (cr1.org 2026-11-01 C2): a
# per-byte loop answers base + N / 15 + N.  A constant pin of 20/28 was
# GREEN on every frame of 12 lines or fewer, so it could not see the
# defect:
#   N = 12: per-byte 20/27, constant pin 20/28 -> PASS, defect unseen.
# Why the MARGIN (cr.org R5): with a slack of N / 4 alone the shortest
# gated frame (3 lines) has no slack, so the bound equals the base pair
# and a jitter of 1 crossing on a CORRECT tree answers RED.  MARGIN = 2
# gives the bound 2 crossings of headroom on every gated frame.
# The bound sits ABOVE the base pair and BELOW the per-byte pair for
# every N above 2, so the case holds on every host:
#   N = 23: bound 16/22, sink 9/15 PASS, per-byte 32/38 RED.
#   N = 12: bound 14/20, sink 9/15 PASS, per-byte 21/27 RED.
#   N =  4: bound 12/18, sink 9/15 PASS, per-byte 13/19 RED.
#   N =  3: bound 11/17, sink 9/15 PASS, per-byte 12/18 RED.
#
# The base pair 9/15 is a HOST VALUE, measured on the TERM=ansi termcap of
# this host.  A different termcap moves it, because the base holds the
# crossings of the mode-set itself (smkx, ke and the other strings).  The
# 2 constants are not a fact about the code.  Re-measure the pair on a new
# host with this command, which sets the 2 constants to 0 in a COPY of the
# driver so that the case reports the raw pair in its FAIL detail:
#   cp test/pty-driver.py /tmp/pd_probe.py
#   # in the COPY only: M61_IMP3_NEWLINE_BASE_C2S = 0, ..._BASE_S2C = 0
#   python3 /tmp/pd_probe.py --emacs src/emacs \
#       --case m61-imp3/newline-run-e2e
# MEASURED that way on 2026-11-01: 9/15 at 23 lines.  The selftest asserts
# the MARGIN and the SEPARATION (the sink pair inside the bound, the
# per-byte pair outside it), so a stale base pair that broke either one
# fails on the host that holds it, and not in the field.
M61_IMP3_NEWLINE_BASE_C2S = 9
M61_IMP3_NEWLINE_BASE_S2C = 15
M61_IMP3_NEWLINE_SLACK_DIV = 4
M61_IMP3_NEWLINE_MARGIN = 2
# The SKIP arm of the case.  A frame of 2 lines or fewer can hold no
# stable measurement of the run (brief.org 2026-11-01 section 6.3).  The
# MARGIN above keeps the bound 2 crossings above the base pair on the
# shortest gated frame, so the skip is a measurement limit, not a hole in
# the derivation (cr.org R5).
M61_IMP3_NEWLINE_SKIP_LINES = 2

# The termscript ORDER: 2 glyph runs with a bell between them.  The
# termscript FILE must hold the whole capability string AFTER the output
# of its run and BEFORE the next run.  This is the declared order change
# of brief.org section 6: the C path interleaved the 2 streams per byte,
# the sink writes the whole string and copies it after.
M61_IMP3_TS_PROBE = M61_IMP2_HELPERS + M61_IMP3_PRELUDE + r"""
          (begin
            (open! "@@TSFILE@@")
            (goto (pmax))
            (ti "@@A@@")
            (redisplay! #t)
            (ding #t)
            (goto (pmax))
            (ti "@@B@@")
            (redisplay! #t)
            (open! #nil)
            (let* ((text (m61-imp2-slurp "@@TSFILE@@"))
                   (bellstr (string (integer->char 7)))
                   (ia (m61-imp2-index text "@@A@@" 0))
                   (ibell (if (< ia 0) -1
                              (m61-imp2-index text bellstr ia)))
                   (ib (m61-imp2-index text "@@B@@" 0)))
              (cond ((< ia 0) "a-missing")
                    ((< ibell 0) "bell-missing")
                    ((< ib 0) "b-missing")
                    ((not (< ia ibell)) "bell-before-a")
                    ((not (< ibell ib)) "b-before-bell")
                    (else "ok"))))
        )))
"""

# LIMIT: a short capability write can not be forced on a host pty.  A pty
# whose buffer is full BLOCKS the write, so no short count comes back.  The
# case runs the real capability and then reports the narrow SKIP with that
# reason: a skip is not a pass.
M61_IMP3_SHORT_PROBE = M61_IMP3_PRELUDE + r"""
          (begin
            (send "@@BEGIN@@")
            (ding #t)
            (send "@@END@@")
            (string-append
             "m61-imp3-skip: a full pty BLOCKS, so a short capability write"
             " can not be forced on this host"))
        )))
"""

M61_IMP3_CASES = (
    {
        "name": "m61-imp3/cap-bytes-e2e",
        "group": "m61-imp3",
        "probe": M61_IMP3_CAP_PROBE,
        "subst": {"BEGIN": M61_IMP3_BEGIN.decode(),
                  "END": M61_IMP3_END.decode()},
        "expect": "ok",
        # The whole capability string of the real OUTPUT call sits between
        # the 2 markers, in this order.
        "pty_in_order": (M61_IMP3_BEGIN, M61_IMP3_BELL, M61_IMP3_END),
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp3/glyph-bytes-e2e",
        "group": "m61-imp3",
        "probe": M61_IMP3_GLYPH_PROBE,
        "subst": {"BEGIN": M61_IMP3_BEGIN.decode(),
                  "NEEDLE": "M61-IMP3-GLYPH|",
                  "END": M61_IMP3_END.decode()},
        "expect": "ok",
        "pty_in_order": (M61_IMP3_BEGIN, M61_IMP3_BELL,
                         b"M61-IMP3-GLYPH|", M61_IMP3_END),
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp3/termscript-order-e2e",
        "group": "m61-imp3",
        "probe": M61_IMP3_TS_PROBE,
        "subst": {"TSFILE": _m61_imp2_tsfile("imp3order"),
                  "A": "M61-IMP3-ORD-A|",
                  "B": "M61-IMP3-ORD-B|"},
        "expect": "ok",
        "pty_in_order": (b"M61-IMP3-ORD-A|", b"M61-IMP3-ORD-B|"),
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp3/flush-e2e",
        "group": "m61-imp3",
        "probe": M61_IMP3_FLUSH_PROBE,
        "subst": {"BEGIN": M61_IMP3_BEGIN.decode(),
                  "MID": M61_IMP3_MID.decode(),
                  "END": M61_IMP3_END.decode()},
        "expect": "ok",
        # The bell byte leads the mid marker, and the second bell byte
        # follows it.  This proves the byte order only.  It does not
        # prove the flush (cr.org C4).
        "pty_in_order": (M61_IMP3_BEGIN, M61_IMP3_BELL, M61_IMP3_MID,
                         M61_IMP3_BELL, M61_IMP3_END),
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp3/cross-count-e2e",
        "group": "m61-imp3",
        "probe": M61_IMP3_CROSS_PROBE,
        "subst": {"MAXC2S": str(M61_IMP3_CROSS_MAX_C2S),
                  "MAXS2C": str(M61_IMP3_CROSS_MAX_S2C)},
        # An upper bound on the crossing pair of ONE bell run: 4/3
        # measured, bound 6/6.  An extra dispatch in the run fails this
        # case.  The 1-byte bell can not show the whole-string gain.
        "expect": "ok",
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp3/newline-run-e2e",
        "group": "m61-imp3",
        "probe": M61_IMP3_NEWLINE_PROBE,
        "subst": {"BASE_C2S": str(M61_IMP3_NEWLINE_BASE_C2S),
                  "BASE_S2C": str(M61_IMP3_NEWLINE_BASE_S2C),
                  "SLACK_DIV": str(M61_IMP3_NEWLINE_SLACK_DIV),
                  "MARGIN": str(M61_IMP3_NEWLINE_MARGIN),
                  "SKIP_LINES": str(M61_IMP3_NEWLINE_SKIP_LINES),
                  "BEGIN": M61_IMP3_BEGIN.decode(),
                  "END": M61_IMP3_END.decode()},
        # An upper bound on the crossing pair of ONE newline run, forced
        # by ONE terminal init.  The bound is derived from the frame line
        # count, so it scales with N.  The per-byte loop of the C2 defect
        # crosses once for each line and exceeds it on every frame.
        "expect": "ok",
        "info_report_prefix": M61_IMP3_SKIP,
        # E4 of cr.org: the N newline bytes of the run MUST appear in the
        # BEGIN .. END span of the pty master.  The probe sends N as the
        # marker M61-IMP3-N=<n>|, so the count comes from the SAME frame
        # that the run uses, and no constant pin is needed.  The fixed
        # ansi entry omits smcup so terminal initialization uses the
        # newline branch.
        "span_requires": {"span": (M61_IMP3_BEGIN, M61_IMP3_END),
                          "newline_count_re": r"M61-IMP3-N=(\d+)\|"},
        "env": {"TERM": "ansi"},
    },
    {
        "name": "m61-imp3/short-write-e2e",
        "group": "m61-imp3",
        "probe": M61_IMP3_SHORT_PROBE,
        "subst": {"BEGIN": M61_IMP3_BEGIN.decode(),
                  "END": M61_IMP3_END.decode()},
        # "expect" holds the same skip text that the probe answers, so no
        # value in the case is dead (cr.org C9).  The harness reads
        # info_report_prefix FIRST, and the NARROW skip is reported for
        # that text only.
        "expect": M61_IMP3_SHORT_SKIP,
        "info_report_prefix": M61_IMP3_SKIP,
        "env": {"TERM": "xterm"},
    },
    {
        "name": "m61-imp3/clean-exit-e2e",
        "group": "m61-imp3",
        "probe": M61_IMP3_CAP_PROBE,
        "subst": {"BEGIN": M61_IMP3_BEGIN.decode(),
                  "END": M61_IMP3_END.decode()},
        "expect": "ok",
        "pty_contains": M61_IMP3_END,
        # Exit 0 and the terminal mode restored.  The capability path
        # changed, so the restore path is re-proved here, not assumed.
        "capture_mode": True,
        "wait_exit": True,
        "env": {"TERM": "xterm"},
    },
)

CASES = (M42_IMP3_CASES + M42_IMP4_CASES + M43_CASES + M53_IMP3_CASES
         + M52_CASES
         + M52_IMP4_CASES + M52_IMP5_CASES + M52_IMP6_CASES + M52_IMP7_CASES
         + M52_IMP8_CASES + M54_IMP2_CASES + M54_IMP3_CASES + M54_IMP4_CASES
         + M56_IMP2_CASES + M58_IMP2_CASES + M58_IMP3_CASES
         + M58_IMP4_CASES + M61_IMP1_CASES + M61_IMP2_CASES
         + M61_IMP2G_CASES + M61_IMP3_CASES)

# These cases check terminal capabilities or their emitted bytes.
_FIXTURE_CASES = {
    "m52-imp3/tty-emit-cap-e2e", "m52-imp3/tty-emit-seq-e2e",
    "m54-imp4/tab-policy-e2e", "m58-imp2/face-appearance-e2e",
}
_FIXTURE_GROUPS = {"m52-imp4", "m52-imp5", "m52-imp6", "m52-imp7",
                   "m58-imp3", "m58-imp4", "m61-imp3"}
CASES = tuple(
    dict(case, terminfo_fixture=case.get("env", {}).get("TERM", "xterm"))
    if case["name"] in _FIXTURE_CASES or case["group"] in _FIXTURE_GROUPS
    else case
    for case in CASES)

GROUPS = ("m42-imp3", "m42-imp4", "m43-imp3", "m43-imp4", "m43-imp5",
          "m53-imp3",
          "m52-imp3", "m52-imp4", "m52-imp5", "m52-imp6", "m52-imp7",
          "m52-imp8",
          "m54-imp2", "m54-imp3", "m54-imp4",
          "m56-imp2",
          "m58-imp2", "m58-imp3", "m58-imp4",
          "m61-imp1", "m61-imp2", "m61-imp2g", "m61-imp3")
