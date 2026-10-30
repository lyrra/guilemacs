#!/usr/bin/env python3
"""pty-driver.py --- the common pty driver for every TTY behaviour test.

One driver for all TTY cases.  It replaces four copies that shared the
same pty scaffolding and differed only in the child probe:

    test/m42/pty-driver.py       -> groups m42-imp3, m42-imp4
    test/m43/pty-driver-imp3.py  -> group  m43-imp3
    test/m43/pty-driver-imp4.py  -> group  m43-imp4
    test/m43/pty-driver-imp5.py  -> group  m43-imp5

M52 imp-3 uses the common driver to check the actual bytes written by
the (emacs tty-output) leaves on the child terminal.

The scaffolding is the hard part and is written once: pty allocation and
the EACCES skip, the forked child, the controlling terminal, the FIFO
gate, the report pipe, the timeout, and the cleanup.

THE REPORT FORMAT IS ONE FORMAT.  A probe is a Scheme expression whose
value is a STRING.  The child prints the elisp `%S' of that value, so
every report is one double-quoted line, and the driver compares the
string with the case's expected string.  There is one regex, one parser
and one comparison for every case.

    probe value "ok"                  case expects "ok"           -> PASS
    probe value "mismatch after=..."  case expects "ok"           -> FAIL

A probe that measures several numbers formats them into that one
string; it does NOT return a structure for the driver to pick apart.
Two rules keep such a string unambiguous:

    an empty list is "-", never the empty string;
    a repeated group is joined with " | ".

So the read-path probe reports "<return> <stored> <order>" per call,
where <order> is "code:mods" pairs joined with ",":

    "0 0 -"                          no input: return 0, stored 0
    "2 2 65:0,66:0"                  two bytes, two events
    "3 1 65:0,7:0 | 0 0 -"           two calls

A case may spell its expectation structurally (see read_path_case) for
readability; expect_string resolves that to the one wire format.

The driver prints one report line per case on its stdout:

    PASS <name>
    FAIL <name> <detail>
    INFO <name> skipped (<reason>)

A host that cannot allocate a pty (/dev/ptmx gives EACCES, errno 13)
prints one INFO line per case and exits 0.  That is an environment-gated
skip: never a PASS and never a FAIL.

ADDING A CASE.  Write a probe whose value is a string, give the case a
`probe`, a `group` and an `expect`, and add it to CASES.  A probe may
carry @@NAME@@ placeholders; the case fills them in through `subst`.
Optional keys: `bytes` to write to the pty master, `close_master` to
take the terminal away after READY, and `env_gate` to turn a value
mismatch into an INFO skip on a host that cannot produce the result.

A case may also carry `info_report_prefix`.  When the probe's OWN value
STARTS WITH that prefix, the driver reports an INFO skip and drops the
prefix from the reason.  This is a NARROW skip: every other value
mismatch stays a real FAIL.  It is not the catch-all `env_gate`.

Python 3 only.  No third-party module.

Usage:
    pty-driver.py --emacs <path-to-src/emacs> [--group <group>] \
                  [--case <name>]... [--timeout <seconds>]
    pty-driver.py --selftest
"""

import argparse
import atexit
import errno
import fcntl
import inspect
import os
import re
import select
import shutil
import signal
import struct
import subprocess
import sys
import tempfile
import time
import termios

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

# --- the M52 imp-8 terminfo fixture -----------------------------------
#
# The imp-8 group has 2 KEY steps only: "delete-mode" and
# "end-delete-mode".  m52_caps maps them to tty->TS_delete_mode and
# tty->TS_end_delete_mode, which C reads from the terminfo strings smdc
# (enter delete mode) and rmdc (exit delete mode).  No terminfo entry in
# a normal installation defines those 2 ("infocmp xterm" holds no smdc /
# rmdc), so on TERM=xterm --tty-emit-cap returns 0 bytes for both keys.
# The zero-count sentinel would then FAIL, and the case could not tell a
# correct m52_caps row from a missing one.
#
# The case therefore runs a controlled terminfo entry that defines the 2
# strings.  The base is the host xterm entry, so the child keeps a normal
# terminal and only the 2 strings are added.  The case still pins NO byte
# span: the driver compares the reported count with the real pty span.
# When tic or infocmp is missing, the case INFO-skips, never a PASS.
M52_IMP8_TERM = "m52-imp8"
M52_IMP8_FIXTURE_CAPS = "\tsmdc=\\E[4h, rmdc=\\E[4l,\n"
# The fallback entry is complete on its own: it is used only when infocmp
# cannot read the host xterm entry.
M52_IMP8_FALLBACK_ENTRY = (
    "m52-imp8|M52 imp-8 delete-mode fixture,\n"
    "\tam, xenl, cols#80, lines#24,\n"
    "\tcsr=\\E[%i%p1%d;%p2%dr, el=\\E[K, clear=\\E[H\\E[2J,\n"
    + M52_IMP8_FIXTURE_CAPS)

_m52_imp8_fixture_env = None
_m52_imp8_fixture_tried = False


def _m52_imp8_entry_source():
    """Return the fixture terminfo source text."""
    infocmp = shutil.which("infocmp")
    if infocmp is None:
        return M52_IMP8_FALLBACK_ENTRY
    try:
        out = subprocess.run([infocmp, "-L", "xterm"],
                             stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                             check=True)
    except (OSError, subprocess.CalledProcessError):
        return M52_IMP8_FALLBACK_ENTRY
    text = out.stdout.decode("utf-8", "replace")
    # Drop infocmp's own comment lines, so the first comma is the one that
    # ends the name field.  Replace that field with the fixture name and
    # insert the 2 strings there; the rest of the entry is untouched.
    text = "\n".join(line for line in text.splitlines()
                     if not line.startswith("#"))
    head, sep, tail = text.partition(",")
    if not sep or "xterm" not in head.split("\n")[0]:
        return M52_IMP8_FALLBACK_ENTRY
    return M52_IMP8_TERM + ",\n" + M52_IMP8_FIXTURE_CAPS + tail.lstrip("\n")


def m52_imp8_env():
    """Return the child env for the imp-8 terminfo fixture, or None.

    Compile M52_IMP8_TERM with tic into a private TERMINFO directory.  A
    missing tic, a tic failure, or a missing compiled entry yields None,
    so the caller reports an explicit INFO skip.
    """
    global _m52_imp8_fixture_env, _m52_imp8_fixture_tried
    if _m52_imp8_fixture_tried:
        return _m52_imp8_fixture_env
    _m52_imp8_fixture_tried = True
    tic = shutil.which("tic")
    if tic is None:
        return None
    source = _m52_imp8_entry_source()
    try:
        outdir = tempfile.mkdtemp(prefix="m52-imp8-terminfo-")
        atexit.register(shutil.rmtree, outdir, True)
        src = os.path.join(outdir, M52_IMP8_TERM + ".src")
        with open(src, "w") as entry_file:
            entry_file.write(source)
        rc = subprocess.run([tic, "-o", outdir, src],
                            stdout=subprocess.DEVNULL,
                            stderr=subprocess.DEVNULL).returncode
        compiled = None
        for root, dirs, files in os.walk(outdir):
            if M52_IMP8_TERM in files:
                compiled = os.path.join(root, M52_IMP8_TERM)
                break
        if rc != 0 or compiled is None:
            return None
        _m52_imp8_fixture_env = {"TERM": M52_IMP8_TERM, "TERMINFO": outdir}
    except OSError:
        return None
    return _m52_imp8_fixture_env


TERMINFO_FIXTURES = {M52_IMP8_TERM: m52_imp8_env}

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
# The xterm "bold" capability, MEASURED on this host with
# terminfo_capability("xterm", "bold"); the selftest pins the equality.
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
#   face-italic-e2e    italic, and the dim fallback when the host holds
#                      no italic capability
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
# The italic capability (terminfo "sitm"), MEASURED on this host with
# terminfo_capability("xterm", "sitm"); the selftest pins the equality.
M58_IMP3_ITALIC = b"\x1b[3m"
# The dim fallback (terminfo "dim"), used when the host holds no italic.
M58_IMP3_DIM = b"\x1b[2m"
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


def _m58_imp3_host_cap(term, cap):
    """Return the host terminfo string CAP for TERM, or None.

    The case tuples are built at import time, before the driver's own
    terminfo_capability helper is defined, so this small query runs here.
    It performs the same lookup: a None answer means the host cannot
    supply the capability.
    """
    try:
        import curses
        curses.setupterm(term)
    except Exception:
        return None
    try:
        return curses.tigetstr(cap)
    except Exception:
        return None


def _m58_imp3_italic_needle():
    """The italic byte when the host holds one, else the dim fallback.

    The C hub emits TS_enter_italic_mode, or TS_enter_dim_mode when the
    host holds no italic capability.  The needle follows the terminfo
    entry of the case's TERM, so the case never hand-copies a byte guess
    (brief.org section 5).
    """
    if _m58_imp3_host_cap("xterm", "sitm") is not None:
        return M58_IMP3_ITALIC, "sitm"
    return M58_IMP3_DIM, "dim"


_M58_IMP3_ITALIC_NEEDLE, M58_IMP3_ITALIC_CAP = _m58_imp3_italic_needle()

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
)

CASES = (M42_IMP3_CASES + M42_IMP4_CASES + M43_CASES + M53_IMP3_CASES
         + M52_CASES
         + M52_IMP4_CASES + M52_IMP5_CASES + M52_IMP6_CASES + M52_IMP7_CASES
         + M52_IMP8_CASES + M54_IMP2_CASES + M54_IMP3_CASES + M54_IMP4_CASES
         + M56_IMP2_CASES + M58_IMP2_CASES + M58_IMP3_CASES
         + M58_IMP4_CASES + M61_IMP1_CASES + M61_IMP2_CASES)

GROUPS = ("m42-imp3", "m42-imp4", "m43-imp3", "m43-imp4", "m43-imp5",
          "m53-imp3",
          "m52-imp3", "m52-imp4", "m52-imp5", "m52-imp6", "m52-imp7",
          "m52-imp8",
          "m54-imp2", "m54-imp3", "m54-imp4",
          "m56-imp2",
          "m58-imp2", "m58-imp3", "m58-imp4",
          "m61-imp1", "m61-imp2")


# The child program.  It is written to a temp file and loaded by the
# emacs under test with -l.  Loading this file means Emacs has completed
# its terminal setup.  The child signals READY on stderr, then blocks in
# Guile on a FIFO gate.  The driver writes the case bytes before releasing
# the gate, so Emacs cannot consume those bytes during an elisp sleep.
# The child writes its report to stderr (the report pipe), never the pty.
CHILD_PROGRAM = r""";;; pty-child.el --- the emacs under test's pty probe.
;;; Written by test/pty-driver.py.  Writes its report to stderr
;;; (the report pipe), never to the pty.
(progn
  ;; Ignore SIGHUP so the driver's terminal-loss step (m42 case 5: close
  ;; the pty master) cannot terminate the child.  Emacs installs its own
  ;; SIGHUP handler (deliver_fatal_signal) at startup, so the ignore must
  ;; be set here, in the child, after startup and before the read -- a
  ;; preexec disposition would be overridden.  Signal 1 is SIGHUP on
  ;; Linux; handler 1 is SIG_IGN.  The report goes to the report pipe
  ;; (fd 2), so it survives the hangup.
  ;;
  ;; FIX-20260928-guilemacs: guard the call so a host without `sigaction'
  ;; cannot error out before the READY signal -- an unguarded failure here
  ;; makes every case report FAIL.  A failure only weakens m42 case 5
  ;; (SIGHUP stays armed); no other case closes the master.
  (condition-case nil (eval-scheme "(sigaction 1 1)") (error nil))
  ;; Emacs has set up the tty before loading this file.  Tell the driver
  ;; it is safe to write input now; the Scheme probe blocks on its FIFO
  ;; gate until the bytes have been written.
  (external-debugging-output ?R)
  (external-debugging-output ?E)
  (external-debugging-output ?A)
  (external-debugging-output ?D)
  (external-debugging-output ?Y)
  (external-debugging-output ?\n)
  ;; FIX-20260928-guilemacs: reading a raw quit byte (C-g) makes the
  ;; store take kbd_buffer_store_event's quit-char branch, which sets
  ;; quit-flag (mod/emacs/kbd-buffer.scm, C 4623-4676 -> handle_interrupt).
  ;; Nothing here is inside read_char, so handle_interrupt does not throw,
  ;; but the next maybe_quit does -- so WITHOUT this binding the pending
  ;; quit aborts this load before the report is written, and m42 cases 4
  ;; and 6 time out instead of reporting.  inhibit-quit keeps the probe
  ;; observable.  It does not touch the read path under test; the child is
  ;; a probe host, not the product.  A probe that cannot raise a quit (the
  ;; m43 mode and size cases) is unaffected by the binding.
  ;;
  ;; This binding alone is not enough for m42 cases 4 and 6: the driver
  ;; must also clear ISIG on the pty (deliver_raw), else the line
  ;; discipline eats the raw 0x07 as VQUIT and flushes the queue before
  ;; the store ever sees it.
  ;; M58 imp-2: a case may supply a PRELUDE.  It runs in the child AFTER
  ;; the READY letters and BEFORE the gate read, so a case that must
  ;; reach a C path the Scheme probe cannot reach (the face-appearance
  ;; policy: only a real redisplay of text that carries a face attribute
  ;; calls turn_on_face / turn_off_face) can drive it here.  The default
  ;; is the empty string, so every earlier case is unchanged.  A prelude
  ;; value is spliced in as a VALUE by the Python `%%' operator, so its
  ;; own text is not re-scanned for placeholders.
%(prelude)s
  (let ((inhibit-quit t))
    (let ((res (condition-case err
                   (eval-scheme %(probe)s)
                 (error (format "%%S" err)))))
      (let ((line (format "%%S\n" res)))
        (dotimes (i (length line))
          (external-debugging-output (aref line i))))))
  (kill-emacs 0))
"""

# The report is the elisp %S of the probe's string value: one line, in
# double quotes.  There is one report shape, so there is one regex.
REPORT_RE = re.compile(r'^"(.*)"$')


def emit(kind, name, detail=None):
    """Print one report line on stdout."""
    if kind == "INFO":
        print("INFO %s skipped (%s)" % (name, detail))
    elif kind == "PASS":
        print("PASS %s" % name)
    else:
        print("FAIL %s %s" % (name, detail))


def skip_all(cases, reason):
    """Print one INFO line per case.  Never a PASS, never a FAIL."""
    for case in cases:
        emit("INFO", case["name"], reason)


def _tty_error_text(err):
    """Format an OSError or a termios.error as "errno N <text>".

    FIX-20260928-guilemacs: termios raises termios.error, which is *not* an
    OSError subclass and carries no .errno/.strerror attributes (only
    .args = (errno, text)).  Read the pair from .args, so both error types
    format the same way and the guard below catches both.
    """
    args = getattr(err, "args", ())
    if len(args) >= 2:
        return "errno %s %s" % (args[0], args[1])
    if args:
        return "errno %s" % (args[0],)
    return str(err)


def deliver_raw(fd):
    """Deliver the case bytes as raw data on the pty (FIX-20260928-guilemacs).

    A raw quit byte (C-g, 0x07) must reach the read path under test.  Emacs
    arms the tty with ISIG on and c_cc[VQUIT] equal to quit_char
    (src/sysdep.c, init_sys_modes).  The line discipline then reads a written
    0x07 as VQUIT: it flushes the whole input queue and raises SIGQUIT.  The
    bytes up to and including the quit byte never arrive, and the child can
    be signalled into a quit.

    Measured evidence, from the earlier failing run (before this clear):
    m42 case 4 gave "2 2 67:0,68:0" instead of "5 2 65:0,66:0,7:0", and
    case 6 gave "1 1 66:0" instead of "3 1 65:0,7:0".  Each measured order
    holds exactly the bytes that follow the quit byte, so the queue was
    flushed at the 0x07.

    Clear ISIG, so the kernel delivers every case byte unchanged, then read
    the attributes back and confirm the clear took effect.  The child also
    binds inhibit-quit, so the stored quit byte cannot abort the report.

    Return None when the clear is confirmed.  Return a reason string,
    otherwise: a tcgetattr/tcsetattr error, or a read-back that still shows
    ISIG.  The caller turns a reason into an environment-gated INFO skip.
    A harness gap must never be reported as a product FAIL, and it must
    not be silent either.
    """
    try:
        attrs = termios.tcgetattr(fd)
    except (OSError, termios.error) as err:
        return "tcgetattr on the pty failed: %s" % _tty_error_text(err)
    # attrs[3] is c_lflag.  With ISIG clear the kernel does not interpret
    # VINTR, VQUIT or VSUSP at all, so a written 0x07 stays data.
    attrs[3] &= ~termios.ISIG
    try:
        termios.tcsetattr(fd, termios.TCSANOW, attrs)
    except (OSError, termios.error) as err:
        return "tcsetattr on the pty failed: %s" % _tty_error_text(err)
    # A text pin proves only that the clear line is present.  Read the
    # attributes back and prove the kernel took the clear, so a host where
    # it does not stick reports an INFO skip instead of a false FAIL.
    try:
        after = termios.tcgetattr(fd)
    except (OSError, termios.error) as err:
        return "tcgetattr read-back on the pty failed: %s" % _tty_error_text(err)
    if after[3] & termios.ISIG:
        return "ISIG clear did not take effect on the pty"
    return None


def group_cases(group):
    """Return the cases of GROUP, or every case when GROUP is None."""
    if group is None:
        return list(CASES)
    return [c for c in CASES if c["group"] == group]


def build_probe(case):
    """Return CASE's probe text, with every @@NAME@@ placeholder filled in.

    The case's `subst` maps a placeholder name to its text.  EMPTY and
    JOIN are supplied to every probe, so a probe formats its report with
    the same tokens the driver expects.  An unresolved placeholder is a
    programming error, not a silent mismatch.
    """
    text = case["probe"]
    subst = dict(case.get("subst", {}))
    subst.setdefault("HELPERS", REPORT_HELPERS)
    subst.setdefault("EMPTY", EMPTY)
    subst.setdefault("JOIN", JOIN)
    for key, value in subst.items():
        text = text.replace("@@%s@@" % key, value)
    left = re.search(r"@@[A-Z_]+@@", text)
    if left:
        raise AssertionError("case %s leaves %s unresolved"
                             % (case["name"], left.group(0)))
    return text


def build_child_source(case, gate_path="/tmp/pty-driver-selftest-gate"):
    """Return child elisp that waits on GATE_PATH before probing CASE."""
    # Embed the probe as an elisp string literal.  Escape backslash and
    # double quote; a probe uses double-quoted strings (the report
    # tokens) but no backslash.
    gate = '"%s"' % gate_path.replace("\\", "\\\\").replace('"', '\\"')
    # A probe may load a real Elisp fixture (M53 imp-3): the driver
    # writes it next to the gate file, and its path is spliced in as the
    # BODY of a Scheme string literal (the probe supplies the quotes).
    load_path = gate_path + ".load.el"
    load_literal = load_path.replace("\\", "\\\\").replace('"', '\\"')
    subst = dict(case.get("subst", {}))
    subst.setdefault("LOADFILE", load_literal)
    # M58 imp-2: a case may supply a child PRELUDE that runs before the
    # gate read.  It is spliced into CHILD_PROGRAM as a VALUE, so the
    # `%' operator does not re-scan its text.  The default is the empty
    # string, so every earlier case is byte-for-byte unchanged.
    subst.setdefault("PRELUDE", case.get("prelude", ""))
    # A probe may open a real termscript file (M54 imp-3): its path is
    # spliced in as the BODY of a Scheme string literal, like LOADFILE.
    if case.get("termscript"):
        ts_literal = (gate_path + ".termscript").replace(
            "\\", "\\\\").replace('"', '\\"')
        subst.setdefault("TSPATH", ts_literal)
    case = dict(case, subst=subst)
    scheme_probe = "(begin (call-with-input-file %s read-char) %s)" % (
        gate, build_probe(case).strip())
    probe = scheme_probe.replace("\\", "\\\\").replace('"', '\\"')
    return CHILD_PROGRAM % {"probe": '"%s"' % probe,
                            "prelude": subst["PRELUDE"]}


def parse_report(text):
    """Return the probe's string value from the child's output, or None."""
    for line in text.splitlines():
        m = REPORT_RE.match(line.strip())
        if m:
            return m.group(1)
    return None


def verdict(case, got):
    """Compare the report GOT with CASE's expectation.

    Return (kind, detail) where kind is "PASS", "FAIL" or "INFO".
    """
    if case.get("expect_decimal"):
        try:
            value = int(got)
        except (TypeError, ValueError):
            return ("FAIL", "measured %r, want a decimal byte count" % got)
        if value >= 0:
            return ("PASS", "measured %r" % got)
        return ("FAIL", "measured negative byte count %r" % got)
    if case.get("expect_terminfo"):
        # M58 imp-3: the answer is a Lisp value, so the expectation is
        # derived from the terminfo entry of the case's OWN TERM.  A
        # mismatch is a real FAIL.  A host that cannot load the terminfo
        # entry is an explicit INFO skip, never a pass.
        want = terminfo_report(case["expect_terminfo"],
                               (case.get("env") or {}).get("TERM"))
        if want is None:
            return ("INFO",
                    "host terminfo unavailable for TERM %r: cannot derive "
                    "the capability verdict" % ((case.get("env") or {}).get("TERM"),))
        if got == want:
            return ("PASS", "measured %r" % got)
        return ("FAIL", "measured %r want %r (terminfo)" % (got, want))
    want = expect_string(case)
    # M58 imp-4: a NARROW skip.  Only the probe's own prefix is an INFO
    # skip; every other value mismatch stays a real FAIL.  This is not
    # the catch-all env_gate.
    skip = case.get("info_report_prefix")
    if skip is not None and isinstance(got, str) and got.startswith(skip):
        return ("INFO", got[len(skip):].strip())
    if got == want:
        return ("PASS", "measured %r" % got)
    if case.get("env_gate"):
        # An environment-gated skip.  m42 case 5 expects the -2 (EIO)
        # arm; a host that cannot give EIO measures another value.  Report
        # INFO with the measured value -- not a FAIL and not an
        # unconditional skip.
        return ("INFO", "%s (measured %r)" % (case["env_gate"], got))
    return ("FAIL", "measured %r want %r" % (got, want))


def output_complete(case, output):
    """Whether every output marker requested by CASE reached the pty."""
    needle = case.get("pty_contains")
    if needle is not None and needle not in output:
        return False
    order = case.get("pty_in_order")
    if order is not None and pty_order_index(output, order) is None:
        return False
    span = case.get("output_span")
    if span is not None:
        start, end = span
        a = output.find(start)
        return a >= 0 and output.find(end, a + len(start)) >= 0
    return True


def pty_order_index(output, needles):
    """The position of the last needle when OUTPUT holds every needle of
    NEEDLES in this order, else None.  M61 imp-2: the ORDER of the bytes
    is a contract of section 3 of milestone.org, so a case that pins an
    order must not accept the reverse order."""
    pos = -1
    for needle in needles:
        pos = output.find(needle, pos + 1)
        if pos < 0:
            return None
    return pos


def check_output(case, got, output):
    """Check exact byte output or the reported size of a marked span."""
    needle = case.get("pty_contains")
    if needle is not None and needle not in output:
        return "pty output did not contain %r" % needle
    order = case.get("pty_in_order")
    if order is not None and pty_order_index(output, order) is None:
        return "pty output did not hold %r in this order" % (order,)
    span = case.get("output_span")
    if span is not None:
        start, end = span
        a = output.find(start)
        b = output.find(end, a + len(start)) if a >= 0 else -1
        if a < 0 or b < 0:
            return "pty output did not contain ordered markers %r %r" % (start, end)
        # A composite report (M53 imp-3) embeds its byte count in a
        # larger string; `output_count_re' extracts it.  A bare-count
        # report (m52) has no regex and is parsed whole.
        count_re = case.get("output_count_re")
        if count_re is not None:
            match = re.search(count_re, got)
            if match is None:
                return "probe did not report a byte count: %r" % got
            reported = int(match.group(1))
        else:
            try:
                reported = int(got)
            except (TypeError, ValueError):
                return "probe did not report a byte count: %r" % got
        actual = b - (a + len(start))
        expected = case.get("output_span_bytes")
        if expected is not None and output[a + len(start):b] != expected:
            return "pty output span was %r; want %r" % (
                output[a + len(start):b], expected)
        if actual != reported:
            return "pty output span was %d bytes; leaf reported %d" % (actual, reported)
    return None


def check_termscript(case, output, ts_bytes):
    """Compare the termscript FILE bytes with the pty master span (M54 imp-3).

    A termscript is a COPY of the terminal output (src/termchar.h :61),
    so the bytes of the opened termscript file MUST equal the bytes the
    terminal received between the case's span markers.  TS_BYTES is the
    termscript file content (None when it could not be read).  Return a
    reason string on a mismatch, or None on success.
    """
    span = case.get("output_span")
    if span is None:
        return "case has no output_span to compare the termscript with"
    start, end = span
    a = output.find(start)
    b = output.find(end, a + len(start)) if a >= 0 else -1
    if a < 0 or b < 0:
        return "pty output did not contain ordered markers %r %r" % (start, end)
    master_span = output[a + len(start):b]
    if ts_bytes is None:
        return "could not read the termscript file"
    if ts_bytes != master_span:
        return "termscript bytes %r != pty master span %r" % (ts_bytes, master_span)
    return None


def terminfo_capability(term, cap):
    """Return the terminfo string CAP for TERM, or None when undefined.

    Load the terminfo entry for TERM and read one capability through the
    standard-library curses binding.  Return None when the entry defines
    no CAP, when TERM is empty, or when terminfo cannot be loaded at all.
    A None result means the host cannot supply the capability, so no byte
    that CAP describes can appear.
    """
    if not term:
        return None
    try:
        import curses
    except ImportError:
        return None
    try:
        curses.setupterm(term)
    except (curses.error, OSError):
        return None
    return curses.tigetstr(cap)


def terminfo_readable(term):
    """True when the host terminfo entry of TERM can be loaded."""
    if not term:
        return False
    try:
        import curses
    except ImportError:
        return False
    try:
        curses.setupterm(term)
    except (curses.error, OSError):
        return False
    return True


def terminfo_report(pairs, term):
    """Build the expected report of a terminfo-derived Lisp verdict.

    PAIRS is a sequence of (LABEL, CAP).  Return "<label>:<0|1> ..." as
    the child reports it, or None when the host terminfo entry cannot be
    read at all -- a missing database is not a missing capability.
    """
    if not terminfo_readable(term):
        return None
    return " ".join("%s:%d" % (label,
                               0 if terminfo_capability(term, cap) is None else 1)
                    for label, cap in pairs)


def terminfo_parameterized(term, cap, arg):
    """Return the byte string CAP formatted with ARG, or None."""
    if not terminfo_readable(term):
        return None
    try:
        import curses
        return curses.tparm(terminfo_capability(term, cap), arg)
    except Exception:
        return None


def span_required_problem(case, output):
    """Check a case's required bytes INSIDE its own marked span.

    A case's `span_requires' names a BEGIN / END marker pair, a set of
    needles, and the terminfo capability the host needs to emit them.
    Return (kind, detail): ("INFO", evidence) when the host terminfo
    cannot supply the capability (so no byte can appear), ("FAIL", reason)
    when the span or a needle is missing, or None when the span holds
    every needle.  The needle is scoped to the span, so a byte elsewhere
    in the transcript does NOT satisfy the check.
    """
    spec = case.get("span_requires")
    if spec is None:
        return None
    term = (case.get("env") or {}).get("TERM")
    cap = spec.get("capability")
    if cap is not None and terminfo_capability(term, cap) is None:
        return ("INFO",
                "terminfo %s holds no %r capability: no byte can appear"
                % (term, cap))
    start, end = spec["span"]
    a = output.find(start)
    b = output.find(end, a + len(start)) if a >= 0 else -1
    if a < 0 or b < 0:
        return ("FAIL", "pty output did not contain ordered markers %r %r"
                % (start, end))
    inner = output[a + len(start):b]
    for needle in spec["needles"]:
        if needle not in inner:
            return ("FAIL", "pty span held no %r (measured %r)"
                    % (needle, inner))
    # An ORDERED needle run pins the SEQUENCE, not the presence alone: a
    # byte that also appears elsewhere in the span cannot satisfy it.
    ordered = spec.get("needles_in_order")
    if ordered:
        pos = 0
        for needle in ordered:
            found = inner.find(needle, pos)
            if found < 0:
                return ("FAIL", "pty span held no ordered run %r after "
                        "offset %d (measured %r)" % (ordered, pos, inner))
            pos = found + len(needle)
    return None


def child_session():
    """Start a session and make the pty slave the controlling terminal."""
    os.setsid()
    # Popen has already connected the slave to stdin.  Acquiring it here
    # makes /dev/tty refer to the same terminal inside Emacs.
    fcntl.ioctl(0, termios.TIOCSCTTY, 0)


def resize_pty(fd, rows, cols):
    """Resize the pty FD to ROWS x COLS through TIOCSWINSZ.

    A `struct winsize' holds 4 unsigned shorts: rows, cols, xpixel,
    ypixel.  The driver resizes the MASTER after READY; the kernel
    shares the size with the slave, so the child's tty-size call sees
    the new value -- a live resize (brief.org section 4(e)).
    """
    packed = struct.pack("HHHH", rows, cols, 0, 0)
    fcntl.ioctl(fd, termios.TIOCSWINSZ, packed)


def modes_equal(a, b):
    """Whether two termios.tcgetattr lists hold the same terminal mode.

    The list is [iflag, oflag, cflag, lflag, ispeed, ospeed, cc]; the
    mode is the four flags plus the control-char array.  The speeds are
    not part of the restore check.
    """
    if a is None or b is None:
        return False
    return (a[0] == b[0] and a[1] == b[1] and a[2] == b[2] and a[3] == b[3]
            and list(a[6]) == list(b[6]))


def run_case(case, emacs, timeout):
    """Run one case on a fresh pty.  Return (name, kind, detail)."""
    name = case["name"]
    # A case may ask for a controlled terminfo entry (see
    # TERMINFO_FIXTURES).  Resolve it before the pty and the temp files,
    # so a missing fixture tool exits here with an explicit INFO skip.
    fixture = None
    if case.get("terminfo_fixture") is not None:
        builder = TERMINFO_FIXTURES.get(case["terminfo_fixture"])
        if builder is None:
            return (name, "INFO", "unknown terminfo fixture %r"
                    % case["terminfo_fixture"])
        fixture = builder()
        if fixture is None:
            return (name, "INFO", "no terminfo fixture %r: tic or infocmp missing"
                    % case["terminfo_fixture"])
    try:
        master, slave = os.openpty()
    except OSError as err:
        # No pty on this host.  Report and stop; the caller turns this
        # into the INFO skip path.
        return (name, "INFO", "no pty: errno %d %s" % (err.errno, err.strerror))

    # Capture the pty mode BEFORE Popen (brief.org section 5).  Emacs
    # saves the startup tty mode and restores it on exit, so the
    # before/after compare holds even when the case delivers bytes and
    # deliver_raw later clears ISIG.  Reading the mode back only AFTER
    # the clear would report a false FAIL.
    mode_before = None
    if case.get("capture_mode"):
        try:
            mode_before = termios.tcgetattr(master)
        except (OSError, termios.error):
            mode_before = None

    rpipe, wpipe = os.pipe()
    tmp = tempfile.NamedTemporaryFile(
        mode="w", suffix="-pty-child.el", delete=False)
    tmp_path = tmp.name
    tmp.close()
    gate_path = tmp_path + ".gate"
    gate_fd = None
    os.mkfifo(gate_path)
    with open(tmp_path, "w") as child_file:
        child_file.write(build_child_source(case, gate_path))
    # Keep both FIFO ends open.  This makes the driver's write immediate
    # even if the child has not reached call-with-input-file yet.
    gate_fd = os.open(gate_path, os.O_RDWR | os.O_NONBLOCK)

    # A case may load a real Elisp fixture (M53 imp-3).
    # build_child_source splices its path (GATE_PATH + ".load.el"); write
    # the fixture there so the child's `load' finds it.
    load_path = gate_path + ".load.el"
    if case.get("load_fixture"):
        with open(load_path, "w") as fixture_file:
            fixture_file.write(case["load_fixture"])

    # A case may open a real termscript file (M54 imp-3).
    # build_child_source splices its path (GATE_PATH + ".termscript"); the
    # child opens it with open-termscript.
    termscript_path = gate_path + ".termscript"
    if case.get("termscript") and os.path.exists(termscript_path):
        os.unlink(termscript_path)

    child = None
    try:
        cmd = [emacs, "-Q", "-nw", "-l", tmp.name]
        child_env = os.environ.copy()
        child_env.update(case.get("env", {}))
        child_env.update(fixture or {})
        child = subprocess.Popen(
            cmd, stdin=slave, stdout=slave, stderr=wpipe,
            close_fds=True, preexec_fn=child_session, env=child_env)
        os.close(slave)
        os.close(wpipe)
        slave = wpipe = None

        # Wait for the child to confirm that Emacs has finished setting
        # up the tty before sending bytes.  A fixed delay after Popen is
        # not sufficient: startup can still be flushing terminal input.
        report = b""
        pty_output = b""
        ready_seen = False
        input_sent = False
        timed_out = False
        report_done = False
        pty_eof = False
        mode_after = None
        exit_status = None
        ts_bytes = None
        deadline = time.monotonic() + timeout
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                timed_out = True
                break
            readers = [rpipe]
            if master is not None and not pty_eof:
                readers.append(master)
            ready, _, _ = select.select(readers, [], [], min(0.5, remaining))
            if master is not None and not pty_eof and master in ready:
                try:
                    chunk = os.read(master, 4096)
                    if chunk:
                        pty_output += chunk
                    else:
                        pty_eof = True
                        if not case.get("capture_mode"):
                            os.close(master)
                            master = None
                except OSError as err:
                    # Linux pty masters report EIO after the slave closes.
                    if err.errno != errno.EIO:
                        raise
                    pty_eof = True
                    if not case.get("capture_mode"):
                        os.close(master)
                        master = None
            if rpipe in ready:
                chunk = os.read(rpipe, 4096)
                if not chunk:
                    break
                report += chunk
                if not ready_seen and b"READY\n" in report:
                    ready_seen = True
                    if case.get("close_master") and master is not None:
                        # m42 case 5: take the tty away.  The child
                        # ignores SIGHUP, so it survives; the slave read
                        # then fails with EIO -> the close-terminal
                        # result -2.
                        os.close(master)
                        master = None
                    if case.get("bytes") and master is not None:
                        # Deliver the bytes raw, so the line discipline
                        # cannot eat a quit byte (see deliver_raw).  A
                        # failed clear is a harness gap, not a product bug:
                        # route it to an environment-gated INFO skip, never
                        # a FAIL.
                        raw_reason = deliver_raw(master)
                        if raw_reason is not None:
                            return (name, "INFO",
                                    "ISIG clear on the pty failed: %s" % raw_reason)
                        os.write(master, case["bytes"])
                    if case.get("resize") and master is not None:
                        # M53 imp-3 step (e): resize the pty AFTER READY and
                        # BEFORE the gate, so the child reads the new size
                        # -- a live resize (brief.org section 4(e)).
                        try:
                            resize_pty(master, *case["resize"])
                        except (OSError, termios.error):
                            pass
                    os.write(gate_fd, b"G")
                    input_sent = True
                # The result is complete once its line arrives.  Do not
                # require Emacs shutdown or pipe EOF after a valid report;
                # cleanup below will stop a child that remains alive.
                # A wait_exit case (M53 imp-3 step (f)) keeps reading until
                # the child exits, so the driver can assert its status.
                if ready_seen and parse_report(
                        report.decode("utf-8", "replace")) is not None \
                        and output_complete(case, pty_output):
                    report_done = True
                    if not case.get("wait_exit"):
                        break
            elif child.poll() is not None:
                break
        # Read the pty mode back after the run, while the master is still
        # open (a capture_mode case keeps it open past EOF).  Emacs
        # restores the mode it saved at startup on exit.
        if case.get("capture_mode") and master is not None:
            try:
                mode_after = termios.tcgetattr(master)
            except (OSError, termios.error):
                mode_after = None
        # M53 imp-3 step (f): wait for the real exit status.
        if case.get("wait_exit") and report_done:
            try:
                exit_status = child.wait(
                    timeout=max(0.0, deadline - time.monotonic()))
            except subprocess.TimeoutExpired:
                exit_status = None
        # M54 imp-3: read the termscript file before cleanup unlinks it.
        # The probe closes the termscript before it reports, so the file
        # is complete by the time the report arrives.
        if case.get("termscript") and report_done:
            try:
                with open(termscript_path, "rb") as ts_file:
                    ts_bytes = ts_file.read()
            except OSError:
                ts_bytes = None
    except OSError as err:
        # openpty already succeeded, so this is a live tty whose read or
        # write failed -- a harness error, not an environment gap.  Report
        # it as a FAIL; the case-5 EIO arm is measured through the child's
        # report, not through a driver-side errno.
        return (name, "FAIL", "tty i/o error: errno %d %s" % (err.errno, err.strerror))
    finally:
        for fd in (master, slave, rpipe, wpipe, gate_fd):
            if fd is not None:
                try:
                    os.close(fd)
                except OSError:
                    pass
        if child is not None and child.poll() is None:
            try:
                os.killpg(os.getpgid(child.pid), signal.SIGKILL)
            except OSError:
                pass
            child.wait()
        for path in (tmp_path, gate_path, load_path, termscript_path):
            try:
                os.unlink(path)
            except OSError:
                pass

    if timed_out:
        stage = "waiting for report" if ready_seen else "waiting for PTY-ready signal"
        captured = report.decode("utf-8", "replace")[-200:]
        return (name, "FAIL", "child timed out after %.1f seconds (%s; output %r)"
                % (timeout, stage, captured))
    if not ready_seen:
        return (name, "FAIL", "child exited without PTY-ready signal")
    if not input_sent:
        return (name, "FAIL", "case input was not sent")

    got = parse_report(report.decode("utf-8", "replace"))
    if got is None:
        return (name, "FAIL", "no child report (raw %r)" % report[:200])

    kind, detail = verdict(case, got)
    if kind == "PASS":
        # M54 imp-4: a case may require a byte only a capable host can
        # produce (the hard-tab 0x09 needs a tab-capable TERM).  The byte
        # is scoped to the case's own BEGIN .. END span: a capable host
        # that emits no byte FAILS.  Only a host whose terminfo holds no
        # capability for the byte is an explicit INFO skip.
        span_problem = span_required_problem(case, pty_output)
        if span_problem is not None:
            return (name,) + span_problem
        output_problem = check_output(case, got, pty_output)
        if output_problem:
            return (name, "FAIL", output_problem)
        # M54 imp-3: the termscript file bytes MUST equal the pty master
        # span (a termscript is a copy of the terminal output).
        if case.get("termscript"):
            ts_problem = check_termscript(case, pty_output, ts_bytes)
            if ts_problem:
                return (name, "FAIL", ts_problem)
        # M53 imp-3 step (f): the real exit status.
        if case.get("wait_exit") and exit_status != 0:
            return (name, "FAIL", "child exit status %r (want 0)" % (exit_status,))
        # M53 imp-3 step (f): the pty mode read-back.
        if case.get("capture_mode"):
            if mode_before is None or mode_after is None:
                return (name, "FAIL", "could not capture/read back the pty mode")
            if not modes_equal(mode_before, mode_after):
                return (name, "FAIL",
                        "pty mode not restored: before=%r after=%r"
                        % (mode_before, mode_after))
    return (name, kind, detail)


def _case(name):
    """Return the case called NAME.  Used by the selftest."""
    return next(c for c in CASES if c["name"] == name)


def scheme_report_program():
    """Return a guile program that prints every case's expected report.

    It defines the real REPORT_HELPERS and drives `fmt-call' with each
    read-path case's expected (return, stored, order) triples, exactly
    as the probe does.  Running it proves that the Scheme formatter and
    the Python renderer produce the same string -- the one thing a host
    with no pty cannot otherwise check, because the formatter only ever
    runs inside the child.
    """
    helpers = REPORT_HELPERS.replace("@@EMPTY@@", EMPTY)
    lines = ["(let ()", helpers]
    for case in CASES:
        if "expect_calls" not in case:
            continue
        calls = " ".join(
            '(fmt-call %s %d (list %s))'
            % (ret, stored,
               " ".join("(cons %d %d)" % (c, m) for c, m in order))
            for ret, stored, order in case["expect_calls"])
        lines.append('  (format #t "~a\\t~a\\n" "%s" (join "%s" (list %s)))'
                     % (case["name"], JOIN, calls))
    lines.append("  #t)")
    return "\n".join(lines)


def scheme_mode_program():
    """Return a guile program that exercises the shared mode comparison.

    MODE_HELPERS only ever runs inside the child, on a pty host, so
    drive `mode=?' here over crafted modes instead.  A mode is
    (IFLAG OFLAG CFLAG LFLAG CC-BYTEVECTOR).
    """
    # The bytevector procedures live in (rnrs bytevectors).  Inside the
    # child they are already bound, because the probe runs in Emacs's
    # Guile; a bare `guile -c' needs the import.
    return "\n".join([
        "(use-modules (rnrs bytevectors))",
        "(let ()",
        MODE_HELPERS,
        '  (define (m a cc) (list a 1 2 3 cc))',
        '  (format #t "mode-equal\\t~a\\n"'
        ' (mode=? (m 9 #vu8(1 2)) (m 9 #vu8(1 2))))',
        '  (format #t "mode-flag-differs\\t~a\\n"'
        ' (mode=? (m 9 #vu8(1 2)) (m 8 #vu8(1 2))))',
        '  (format #t "mode-cc-differs\\t~a\\n"'
        ' (mode=? (m 9 #vu8(1 2)) (m 9 #vu8(1 3))))',
        '  (format #t "mode-cc-length-differs\\t~a\\n"'
        ' (mode=? (m 9 #vu8(1 2)) (m 9 #vu8(1 2 3))))',
        "  #t)",
    ])


def selftest_scheme():
    """Check the Scheme helpers against their Python twins.

    Needs guile on PATH.  Returns a list of problems; an absent guile
    returns a single INFO-style note, not a failure, because the check
    is a cross-check of two implementations and guile may be missing on
    a packaging host.
    """
    problems = _scheme_report_check()
    problems.extend(_scheme_mode_check())
    return problems


def _run_guile(program):
    """Run PROGRAM under guile.  Return (stdout, problem-or-None)."""
    try:
        proc = subprocess.run(["guile", "-c", program],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              timeout=60)
    except (OSError, subprocess.SubprocessError) as err:
        return ("", "INFO scheme cross-check skipped (no runnable guile: %s)"
                % err)
    if proc.returncode != 0:
        return ("", "scheme helpers failed to run: %s"
                % proc.stderr.decode("utf-8", "replace").strip()[-300:])
    return (proc.stdout.decode("utf-8", "replace"), None)


def _scheme_mode_check():
    """Drive the shared mode comparison under guile."""
    out, problem = _run_guile(scheme_mode_program())
    if problem:
        return [problem]
    want = {"mode-equal": "#t",
            "mode-flag-differs": "#f",
            "mode-cc-differs": "#f",
            "mode-cc-length-differs": "#f"}
    problems = []
    seen = {}
    for line in out.splitlines():
        if "\t" in line:
            label, got = line.split("\t", 1)
            seen[label] = got
    for label, expected in want.items():
        if seen.get(label) != expected:
            problems.append("scheme mode=? %s: got %r want %r"
                            % (label, seen.get(label), expected))
    return problems


def _scheme_report_check():
    """Check the Scheme report formatter against the Python renderer."""
    program = scheme_report_program()
    try:
        proc = subprocess.run(["guile", "-c", program],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              timeout=60)
    except (OSError, subprocess.SubprocessError) as err:
        return ["INFO scheme cross-check skipped (no runnable guile: %s)" % err]
    if proc.returncode != 0:
        return ["scheme helpers failed to run: %s"
                % proc.stderr.decode("utf-8", "replace").strip()[-300:]]
    problems = []
    seen = set()
    for line in proc.stdout.decode("utf-8", "replace").splitlines():
        if "\t" not in line:
            continue
        name, got = line.split("\t", 1)
        seen.add(name)
        want = expect_string(_case(name))
        if got != want:
            problems.append("scheme fmt-call for %s: got %r want %r"
                            % (name, got, want))
    for case in CASES:
        if "expect_calls" in case and case["name"] not in seen:
            problems.append("scheme cross-check produced no line for %s"
                            % case["name"])
    return problems


def selftest():
    """Exercise the parser, the case tables and the source builder.

    Runs on any host: it never allocates a pty and never starts a child.
    Returns 0 when every check passes, 1 otherwise.  The ERT wrappers
    drive this with --selftest.
    """
    problems = []

    def check(label, got, want):
        if got != want:
            problems.append("%s: got %r want %r" % (label, got, want))

    # --- the case tables ---------------------------------------------
    names = [c["name"] for c in CASES]
    check("case-names-unique", len(names), len(set(names)))
    for case in CASES:
        if case["group"] not in GROUPS:
            problems.append("case %s has an unknown group %r"
                            % (case["name"], case["group"]))
        if not case.get("probe"):
            problems.append("case %s has no probe" % case["name"])
        if ("expect" not in case and "expect_calls" not in case
                and not case.get("expect_decimal")
                and not case.get("expect_terminfo")):
            problems.append("case %s declares no expectation" % case["name"])
    for group in GROUPS:
        if not group_cases(group):
            problems.append("group %s has no case" % group)
    # The merge must not drop a case: 2 + 7 from M42, 3 from M43,
    # 3 M52 imp-3 output-path cases, 1 M52 imp-4 policy case,
    # 1 M52 imp-5 bell / cursor policy case, and 1 M54 imp-2
    # output-write-verdict case.
    check("m42-imp3-case-count", len(group_cases("m42-imp3")), 2)
    check("m42-imp4-case-count", len(group_cases("m42-imp4")), 7)
    check("m43-imp3-case-count", len(group_cases("m43-imp3")), 1)
    check("m43-imp4-case-count", len(group_cases("m43-imp4")), 1)
    check("m43-imp5-case-count", len(group_cases("m43-imp5")), 1)
    check("m52-imp3-case-count", len(group_cases("m52-imp3")), 3)
    check("m52-imp4-case-count", len(group_cases("m52-imp4")), 1)
    check("m52-imp5-case-count", len(group_cases("m52-imp5")), 1)
    check("m52-imp6-case-count", len(group_cases("m52-imp6")), 1)
    check("m52-imp7-case-count", len(group_cases("m52-imp7")), 1)
    check("m52-imp8-case-count", len(group_cases("m52-imp8")), 1)
    check("m53-imp3-case-count", len(group_cases("m53-imp3")), 1)
    check("m54-imp2-case-count", len(group_cases("m54-imp2")), 1)
    check("m54-imp3-case-count", len(group_cases("m54-imp3")), 1)
    check("m54-imp4-case-count", len(group_cases("m54-imp4")), 1)
    check("m56-imp2-case-count", len(group_cases("m56-imp2")), 1)
    check("m58-imp2-case-count", len(group_cases("m58-imp2")), 1)
    check("m58-imp3-case-count", len(group_cases("m58-imp3")), 5)
    check("m58-imp4-case-count", len(group_cases("m58-imp4")), 1)
    check("m61-imp1-case-count", len(group_cases("m61-imp1")), 4)
    check("m61-imp2-case-count", len(group_cases("m61-imp2")), 6)
    check("total-case-count", len(CASES), 42)
    write_case = _case("m52-imp3/tty-write-bytes-e2e")
    for name, markers in (("m52-imp3/tty-write-bytes-e2e",
                           (b"M52-WRITE-BEGIN!", b"M52-WRITE-END!")),
                          ("m52-imp3/tty-emit-cap-e2e",
                           (b"M52-CAP-BEGIN!", b"M52-CAP-END!")),
                          ("m52-imp3/tty-emit-seq-e2e",
                           (b"M52-SEQ-BEGIN!", b"M52-SEQ-END!")),
                          ("m52-imp4/policy-key-e2e",
                           (b"M52-IMP4-BEGIN!", b"M52-IMP4-END!")),
                          ("m52-imp5/policy-key-e2e",
                           (b"M52-IMP5-BEGIN!", b"M52-IMP5-END!")),
                          ("m52-imp6/policy-key-e2e",
                           (b"M52-IMP6-BEGIN!", b"M52-IMP6-END!")),
                          ("m52-imp7/policy-key-e2e",
                           (b"M52-IMP7-BEGIN!", b"M52-IMP7-END!")),
                          ("m52-imp8/policy-key-e2e",
                           (b"M52-IMP8-BEGIN!", b"M52-IMP8-END!")),
                          ("m54-imp2/output-write-verdict-e2e",
                           (b"M54-IMP2-BEGIN!", b"M54-IMP2-END!")),
                          ("m54-imp3/termscript-copy-e2e",
                           (M54_IMP3_BEGIN, M54_IMP3_END)),
                          ("m56-imp2/tty-init-e2e",
                           (M56_IMP2_BEGIN, M56_IMP2_END))):
        case = _case(name)
        check("%s-output-span" % name, case.get("output_span"), markers)
        # A bare-count report declares `expect_decimal'; a composite report
        # (m56-imp2, like m53-imp3) extracts its count with `output_count_re'.
        # Either way the case checks a reported byte count.
        if not (case.get("expect_decimal") or case.get("output_count_re")):
            problems.append("%s does not check a reported byte count" % name)
    check("m54-imp2-output-bytes",
          _case("m54-imp2/output-write-verdict-e2e").get("output_span_bytes"),
          b"M54-IMP2-WRITEOK!")
    check("m54-imp3-output-bytes",
          _case("m54-imp3/termscript-copy-e2e").get("output_span_bytes"),
          b"M54-IMP3-WRITEOK!")
    check("m56-imp2-output-bytes",
          _case("m56-imp2/tty-init-e2e").get("output_span_bytes"),
          M56_IMP2_OUT_BYTES)
    # M56 imp-2 (brief.org section 4.2): the case must resize the pty so a
    # size that follows the resize proves a LIVE size query, and its probe
    # must resolve the size, read, and write paths.  These pins hold the
    # wiring on a host with no pty.
    m56 = _case("m56-imp2/tty-init-e2e")
    check("m56-imp2-resize", m56.get("resize"),
          (M56_IMP2_ROWS, M56_IMP2_COLS))
    m56_src = build_child_source(m56)
    for needle, label in (
            ("tty-size", "probe reads the tty size"),
            ("tty-read-avail-input!", "probe runs the read path"),
            ("tty-write-bytes", "probe runs the write path")):
        if needle not in m56_src:
            problems.append("m56-imp2 probe does not %s" % label)
    if "@@OUTBYTES@@" in m56_src:
        problems.append("m56-imp2 probe left the OUTBYTES placeholder unresolved")
    # M57 (cr.org F1): the m56-imp2 probe reports the ACCOUNTED input as
    # ONE race-proof number -- the stored kbd_buffer count after the read,
    # not the racy (ret, delta) pair.  Emacs's own input poll can drain
    # the pending tty bytes into kbd_buffer before the probe runs, and the
    # old delta pair then read 0 and 0.  These pins hold the ABSOLUTE
    # (not delta) decision on a host with no pty.
    check("m56-imp2-expect-accounted", expect_string(m56),
          "read:2 out:%d size:%dx%d"
          % (len(M56_IMP2_OUT_BYTES), M56_IMP2_COLS, M56_IMP2_ROWS))
    if "(number->string stored)" not in m56_src:
        problems.append("m56-imp2 probe does not report the stored count")
    if "(- n1 prev)" in m56_src:
        problems.append("m56-imp2 probe still holds the racy (- n1 prev) pair")
    if m56_src.count("force nr)") != 1:
        problems.append("m56-imp2 probe reads the stored count not exactly once")
    # M58 imp-2 (brief.org section 4.3): the face-appearance case drives
    # the C hub through a REAL redisplay, so the prelude must be spliced
    # into the built child source, the two markers must reach it, and the
    # span must name the MEASURED bold byte plus the terminfo capability.
    # These pins hold the wiring on a host with no pty.
    face_case = _case("m58-imp2/face-appearance-e2e")
    check("m58-imp2-span-requires", face_case.get("span_requires"),
          {"span": (M58_IMP2_BEGIN, M58_IMP2_END),
           "needles": (M58_IMP2_BOLD,),
           "capability": "bold"})
    # A hand-copied `output_span_bytes' would pin a GUESS: the honest pin
    # is the span plus its needles and capability (brief.org section 4.3).
    check("m58-imp2-no-span-bytes-guess",
          "output_span_bytes" in face_case, False)
    for needle, label in (
            ("propertize", "prelude applies a face attribute"),
            ("redisplay", "prelude forces a redisplay"),
            ("'face 'bold", "prelude sets the bold face")):
        if needle not in face_case.get("prelude", ""):
            problems.append("m58-imp2 prelude does not %s" % label)
    face_src = build_child_source(face_case)
    for marker in (M58_IMP2_BEGIN, M58_IMP2_END):
        if marker.decode() not in face_src:
            problems.append("m58-imp2 built child source lost the marker %r"
                            % (marker,))
    if re.search(r"@@[A-Z_]+@@", face_src):
        problems.append("m58-imp2 built child source leaves a placeholder")
    # M58 imp-3 (brief.org sections 5 and 8): the 5 real-path cases of the
    # MOVED decision.  Each case carries its OWN marker pair, a prelude
    # that inserts a face attribute and forces a redisplay, and needles
    # scoped to that span.  The needle constants are pinned against the
    # terminfo entry of the same TERM, so a copied byte guess fails here.
    for name, needles, cap in (
            ("m58-imp3/face-off-e2e",
             (M58_IMP3_BOLD, M58_IMP3_ME), "bold"),
            ("m58-imp3/face-italic-e2e",
             (_M58_IMP3_ITALIC_NEEDLE,), M58_IMP3_ITALIC_CAP),
            ("m58-imp3/face-underline-e2e",
             (M58_IMP3_UNDERLINE,), "smul"),
            ("m58-imp3/face-color-e2e",
             (M58_IMP3_SETAF_RED, M58_IMP3_SETAB_BLUE), "setaf")):
        case = _case(name)
        spec = case.get("span_requires")
        if spec is None:
            problems.append("%s declares no span_requires" % name)
            continue
        check("%s-needles" % name, spec.get("needles"), needles)
        check("%s-capability" % name, spec.get("capability"), cap)
        src = build_child_source(case)
        for marker in spec["span"]:
            if marker.decode() not in src:
                problems.append("%s built child source lost the marker %r"
                                % (name, marker))
        for needle, label in (("propertize", "applies a face attribute"),
                              ("redisplay", "forces a redisplay")):
            if needle not in case.get("prelude", ""):
                problems.append("%s prelude does not %s" % (name, label))
        if spec["span"][0] == spec["span"][1]:
            problems.append("%s span markers are not distinct" % name)
    # The span of every imp-3 case is its OWN marker pair: two cases must
    # never share one, or a byte of one case could satisfy the other.
    spans = [tuple(_case(c)["span_requires"]["span"])
             for c in ("m58-imp3/face-off-e2e", "m58-imp3/face-italic-e2e",
                       "m58-imp3/face-underline-e2e", "m58-imp3/face-color-e2e")]
    check("m58-imp3-distinct-spans", len(set(spans)), len(spans))
    # The measured needle constants MUST equal the terminfo entry of the
    # same TERM.  The exception is the "me" byte: this host's emacs
    # terminfo lookup and the Python curses binding disagree on it, so it
    # is measured from the imp-2 span instead (a host-independent pin
    # cannot express that; the PTY case is the authority).
    check("m58-imp3-bold-needle-eq-terminfo", M58_IMP3_BOLD,
          terminfo_capability("xterm", "bold"))
    check("m58-imp3-italic-needle-eq-terminfo", M58_IMP3_ITALIC,
          terminfo_capability("xterm", "sitm"))
    check("m58-imp3-underline-needle-eq-terminfo", M58_IMP3_UNDERLINE,
          terminfo_capability("xterm", "smul"))
    # This host's tty color map resolves every color NAME to index 0, so
    # the measured color bytes are setaf 0 / setab 0.  The pin is the
    # terminfo STRING with that measured index: the case proves the two
    # color step routes, not the numeric color value (an honest limit).
    check("m58-imp3-setaf-needle-eq-terminfo", M58_IMP3_SETAF_RED,
          terminfo_parameterized("xterm", "setaf", 0))
    check("m58-imp3-setab-needle-eq-terminfo", M58_IMP3_SETAB_BLUE,
          terminfo_parameterized("xterm", "setab", 0))
    # The capable-p case reports a Lisp value, so it holds no needle: the
    # expectation comes from terminfo (a mismatch FAILS) and a host with
    # no loadable terminfo is an explicit INFO skip.
    cap_case = _case("m58-imp3/capable-p-e2e")
    check("m58-imp3-capable-p-expectation", cap_case.get("expect_terminfo"),
          (("bold", "bold"), ("italic", "sitm"), ("underline", "smul")))
    if "span_requires" in cap_case:
        problems.append("m58-imp3/capable-p-e2e must not pin a byte span")
    if "display-supports-face-attributes-p" not in cap_case.get("probe", ""):
        problems.append("m58-imp3/capable-p-e2e does not query "
                        "display-supports-face-attributes-p")
    # The prelude hook must not change an earlier case: its prelude is the
    # empty string, so the built source holds no face prelude.
    if "propertize" in build_child_source(_case("m56-imp2/tty-init-e2e")):
        problems.append("m58-imp2 prelude leaked into an earlier case")
    # The needle is MEASURED, then pinned: the host terminfo must agree.
    bold_cap = terminfo_capability("xterm", "bold")
    if bold_cap is not None and bold_cap != M58_IMP2_BOLD:
        problems.append("xterm bold capability is %r, want %r"
                        % (bold_cap, M58_IMP2_BOLD))
    # The m54-imp3 case must open a termscript file, and run_case must
    # compare the termscript file bytes with the pty master span.  These
    # pins hold the wiring on a host with no pty.
    if not _case("m54-imp3/termscript-copy-e2e").get("termscript"):
        problems.append("m54-imp3 does not open a termscript file")
    if "check_termscript" not in inspect.getsource(run_case):
        problems.append("m54-imp3 run_case does not compare the termscript file")
    if "@@TSPATH@@" in build_child_source(_case("m54-imp3/termscript-copy-e2e")):
        problems.append("m54-imp3 probe left the TSPATH placeholder unresolved")
    # M54 imp-4 (cr.org F2): the hard-tab byte is scoped to the case's own
    # BEGIN .. END span and the case FAILS when a tab-capable host emits no
    # byte.  Only a host whose terminfo holds no "ht" string INFO-skips.
    # These pins hold the wiring on a host with no pty.
    tab_case = _case("m54-imp4/tab-policy-e2e")
    check("m54-imp4-span-requires", tab_case.get("span_requires"),
          {"span": (M54_IMP4_BEGIN, M54_IMP4_END),
           "needles": (b"\x09",),
           "capability": "ht"})
    if "info_if_missing" in tab_case:
        problems.append("m54-imp4 still uses the weak info_if_missing key")
    if "span_required_problem" not in inspect.getsource(run_case):
        problems.append("m54-imp4 run_case does not check the required span byte")
    # The check has teeth: a missing in-span byte is a FAIL, a byte OUTSIDE
    # the span is a FAIL, the span with the byte passes, and only an absent
    # capability is an INFO skip.
    span_case = {"name": "span-probe",
                 "span_requires": {"span": (M54_IMP4_BEGIN, M54_IMP4_END),
                                   "needles": (b"\x09",)}}
    check("m54-imp4-span-missing-fails",
          span_required_problem(span_case, M54_IMP4_BEGIN + M54_IMP4_END)[0],
          "FAIL")
    check("m54-imp4-span-outside-fails",
          span_required_problem(
              span_case, b"\x09" + M54_IMP4_BEGIN + M54_IMP4_END)[0],
          "FAIL")
    check("m54-imp4-span-present-passes",
          span_required_problem(span_case,
                                M54_IMP4_BEGIN + b"\x09" + M54_IMP4_END),
          None)
    check("m54-imp4-capability-absent-skips",
          span_required_problem(
              {"name": "cap-probe",
               "span_requires": {"span": (M54_IMP4_BEGIN, M54_IMP4_END),
                                 "needles": (b"\x09",),
                                 "capability": "zzzz"},
               "env": {"TERM": "xterm"}},
              M54_IMP4_BEGIN + M54_IMP4_END)[0],
          "INFO")
    tab_cap = terminfo_capability("xterm", "ht")
    if tab_cap is not None and tab_cap != b"\t":
        problems.append("xterm ht capability is %r, want b'\\t'" % (tab_cap,))
    check("m52-cap-output-bytes",
          _case("m52-imp3/tty-emit-cap-e2e").get("output_span_bytes"),
          b"\x1b[3;11r")
    check("m52-seq-output-bytes",
          _case("m52-imp3/tty-emit-seq-e2e").get("output_span_bytes"),
          b"\x1b[3;11r\x1b[5;9r")
    check("m52-write-output-bytes",
          write_case.get("output_span_bytes"), b"M52-IMP3-WRITE-OK!")
    check("m52-imp4-output-bytes",
          _case("m52-imp4/policy-key-e2e").get("output_span_bytes"),
          b"\x1b[4h\x1b[4l\x1b[27m\x1b[7m\x1b[7m\x1b[27m")
    check("m52-imp5-output-bytes",
          _case("m52-imp5/policy-key-e2e").get("output_span_bytes"),
          b"\x07\x1b[?25l\x1b[?12l\x1b[?25h"
          b"\x1b[?12l\x1b[?25h\x1b[?12;25h"
          b"\x1b[27m\x1b[7m\x1b[27m\x1b[7m")
    # m52-imp6 pins NO output_span_bytes (brief.org section 9): the span
    # must come from a real pty run or INFO-skip, so assert its absence.
    check("m52-imp6-output-bytes-unpinned",
          "output_span_bytes" in _case("m52-imp6/policy-key-e2e"), False)
    # m52-imp7 pins NO output_span_bytes (brief.org section 5): same rule.
    check("m52-imp7-output-bytes-unpinned",
          "output_span_bytes" in _case("m52-imp7/policy-key-e2e"), False)
    # m52-imp8 pins NO output_span_bytes (brief.org section 5): same rule.
    check("m52-imp8-output-bytes-unpinned",
          "output_span_bytes" in _case("m52-imp8/policy-key-e2e"), False)
    # A zero byte count must FAIL, not pass as the count "0".
    # The probe returns the sentinel "no-bytes" on a zero count, and the
    # expect_decimal verdict rejects a non-decimal value.  This pins that
    # wiring, because the pty case itself INFO-skips on this host.
    check("m52-imp8-zero-count-fails",
          verdict(_case("m52-imp8/policy-key-e2e"), "no-bytes")[0], "FAIL")
    # The imp-8 case needs a live smdc / rmdc terminfo string for its 2
    # KEY steps, so it names a controlled terminfo fixture.  A typo here
    # would silently run TERM=xterm and measure the same 0 bytes as a
    # missing m52_caps row.
    check("m52-imp8-terminfo-fixture",
          _case("m52-imp8/policy-key-e2e").get("terminfo_fixture")
          in TERMINFO_FIXTURES, True)

    # --- the M53 imp-3 vertical slice ----------------------------------
    # The slice carries the resize, the mode capture/read-back, the exit
    # wait, and the load fixture.  These pins hold the wiring on a host
    # with no pty.
    m53 = _case("m53-imp3/vertical-slice-e2e")
    check("m53-imp3-expect", expect_string(m53),
          "load:OK read:2,2 out:18 size:100x30 mode:RESTORED")
    check("m53-imp3-output-span", m53.get("output_span"),
          (M53_IMP3_BEGIN, M53_IMP3_END))
    check("m53-imp3-output-bytes", m53.get("output_span_bytes"),
          M53_IMP3_OUT_BYTES)
    check("m53-imp3-resize", m53.get("resize"),
          (M53_IMP3_ROWS, M53_IMP3_COLS))
    if not m53.get("wait_exit"):
        problems.append("m53-imp3 does not wait for the child exit status")
    if not m53.get("capture_mode"):
        problems.append("m53-imp3 does not capture the pty mode")
    m53_src = build_child_source(m53)
    for needle, label in (
            ("TIOCSWINSZ", "resize uses TIOCSWINSZ"),
            ("tcgetattr", "run_case reads the pty mode back"),
            ("resize_pty(master", "run_case resizes the pty"),
            ("child.wait(", "run_case waits for the child exit status"),
            ("modes_equal", "run_case compares the pty modes")):
        if needle not in inspect.getsource(run_case) \
                and needle not in inspect.getsource(resize_pty) \
                and needle not in inspect.getsource(modes_equal):
            problems.append("m53-imp3 wiring missing: %s" % label)
    if "symbol-value" not in m53_src:
        problems.append("m53-imp3 probe does not read the load side effect")
    if "tty-read-avail-input!" not in m53_src:
        problems.append("m53-imp3 probe does not run the read path")
    if "tty-write-bytes" not in m53_src:
        problems.append("m53-imp3 probe does not run the write path")
    if "tty-size" not in m53_src:
        problems.append("m53-imp3 probe does not read the tty size")
    if "@@LOADFILE@@" in m53_src or "@@OUTBYTES@@" in m53_src:
        problems.append("m53-imp3 probe left a placeholder unresolved")

    # --- the one parser ------------------------------------------------
    check("parse-ok", parse_report('"ok"'), "ok")
    check("parse-mismatch", parse_report('"mismatch after=(1 . 2)"'),
          "mismatch after=(1 . 2)")
    check("parse-read-path", parse_report('"2 2 65:0,66:0"'), "2 2 65:0,66:0")
    check("parse-two-calls", parse_report('"3 1 65:0,7:0 | 0 0 -"'),
          "3 1 65:0,7:0 | 0 0 -")
    check("parse-noise", parse_report('garbage\n"ok"\ntrailing'), "ok")
    check("parse-no-report", parse_report("no report here"), None)
    # An elisp error report is the %S of a string, so it is a quoted line
    # too; the parser must return a non-"ok" value that becomes a FAIL.
    check("parse-error-string", parse_report('"#<error>"'), "#<error>")
    # Regression pin: the old structured form is not a report any more.
    # A probe whose value is a list prints unquoted, so it must not parse
    # -- that is a probe bug, and a FAIL, never a silent pass.
    check("rejects-unquoted-list", parse_report('(0 0 0 "")'), None)
    check("rejects-opaque-empty", parse_report("#<scheme ()>"), None)

    # --- the report renderer -------------------------------------------
    check("render-empty-order", render_call(0, 0, []), "0 0 -")
    check("render-one-event", render_call(2, 2, [(65, 0)]), "2 2 65:0")
    check("render-two-events", render_call(2, 2, [(65, 0), (66, 0)]),
          "2 2 65:0,66:0")
    check("render-negative-return", render_call(-2, 0, []), "-2 0 -")
    check("render-meta", render_call(2, 2, [(1, META)]), "2 2 1:134217728")
    # An empty order must never render as the empty string: two adjacent
    # separators would make the report ambiguous.
    if render_call(0, 0, []).endswith(" "):
        problems.append("render_call leaves a trailing separator")

    # --- the expected strings of every case ----------------------------
    check("expect-case-1", expect_string(_case("m42-imp3/case-1-no-input")),
          "0 0 -")
    check("expect-case-2", expect_string(_case("m42-imp3/case-2-short-read")),
          "2 2 65:0,66:0")
    check("expect-meta-key-1",
          expect_string(_case("m42-imp4/case-3-meta-key-1")),
          "2 2 1:134217728,97:134217728")
    check("expect-meta-key-2",
          expect_string(_case("m42-imp4/case-3-meta-key-2")),
          "2 2 129:0,225:0")
    check("expect-meta-key-0",
          expect_string(_case("m42-imp4/case-3-meta-key-0")),
          "2 2 1:0,97:0")
    check("expect-quit-byte", expect_string(_case("m42-imp4/case-4-quit-byte")),
          "5 2 65:0,66:0,7:0")
    check("expect-meta-quit-guard",
          expect_string(_case("m42-imp4/case-4-meta-quit-guard")),
          "2 2 65:0,7:134217728")
    check("expect-terminal-loss",
          expect_string(_case("m42-imp4/case-5-terminal-loss")), "-2 0 -")
    check("expect-continuation",
          expect_string(_case("m42-imp4/case-6-continuation")),
          "3 1 65:0,7:0 | 0 0 -")
    check("expect-mode", expect_string(_case("m43-imp3/pty-e2e")), "ok")
    check("expect-restore", expect_string(_case("m43-imp4/pty-e2e")), "ok")
    # The size case expects its measurement, not a verdict word.  tty-size
    # returns (WIDTH . HEIGHT) while set-tty-size takes (fd HEIGHT WIDTH),
    # so the order is swapped between the call and the report; pin it.
    check("expect-size", expect_string(_case("m43-imp5/pty-e2e")), "100 30")

    # --- the verdict ----------------------------------------------------
    check("ok-passes", verdict(_case("m43-imp3/pty-e2e"), "ok")[0], "PASS")
    check("other-fails",
          verdict(_case("m43-imp3/pty-e2e"), "mismatch x=1")[0], "FAIL")
    check("read-path-match-passes",
          verdict(_case("m42-imp3/case-1-no-input"), "0 0 -")[0], "PASS")
    check("read-path-mismatch-fails",
          verdict(_case("m42-imp3/case-1-no-input"), "1 1 65:0")[0], "FAIL")
    # The env_gate case reports INFO on a mismatch, never a FAIL.
    check("env-gate-mismatch-is-info",
          verdict(_case("m42-imp4/case-5-terminal-loss"), "0 0 -")[0], "INFO")
    # ... but it still PASSes on the expected value.
    check("env-gate-match-passes",
          verdict(_case("m42-imp4/case-5-terminal-loss"), "-2 0 -")[0], "PASS")

    # M58 imp-4: the info_report_prefix skip is NARROW.  The probe's own
    # prefix is an INFO skip; a WRONG value is a real FAIL, and a value
    # that merely contains the prefix is not a skip.
    imp4 = _case("m58-imp4/color-mode-e2e")
    check("m58-imp4-explicit-skip-is-info",
          verdict(imp4, M58_IMP4_SKIP + " cannot make a second tty frame")[0],
          "INFO")
    check("m58-imp4-wrong-value-fails", verdict(imp4, "8 8 8")[0], "FAIL")
    check("m58-imp4-prefix-must-lead",
          verdict(imp4, "x" + M58_IMP4_SKIP)[0], "FAIL")
    check("m58-imp4-value-passes", verdict(imp4, "8 0 8")[0], "PASS")

    # --- the M42 case-table models --------------------------------------
    # The case-6 continuation must match the code under test: the first
    # read consumes the whole FIONREAD batch, so the byte after the quit
    # char is dropped and call 2 sees an empty tty (return 0, stored 0, no
    # events).  A return of 1 with event 66 would be a false FAIL on a
    # host with a pty.
    check("case-6-continuation-model",
          _case("m42-imp4/case-6-continuation")["expect_calls"],
          [(3, 1, [(0x41, 0), (0x07, 0)]), (0, 0, [])])

    # FIX-20260928-guilemacs: the chosen model: a raw C-g is decoded but
    # its folded code (7) equals quit_char, so the quit-char branch
    # handles it and never ring-appends it.  The rejected option is that a
    # raw C-g must occupy one kbd_buffer slot.  The passing
    # case-4-meta-quit-guard case corroborates the chosen model: its meta
    # byte folds to code 7 with the meta modifier, which is not equal to
    # quit_char, so it IS stored.  Pin both the guard and the case-4
    # stored counts, so a regression in either is a SELFTEST FAIL on any
    # host (no pty needed).
    check("case-4-meta-quit-guard-model",
          _case("m42-imp4/case-4-meta-quit-guard")["expect_calls"],
          [(2, 2, [(0x41, 0), (0x07, META)])])
    check("case-4-quit-byte-stored-model",
          _case("m42-imp4/case-4-quit-byte")["expect_calls"],
          [(5, 2, [(0x41, 0), (0x42, 0), (0x07, 0)])])

    # Case 5 is a measured case, not an unconditional skip: it closes the
    # pty master and expects the -2 (EIO) arm.
    term_loss = _case("m42-imp4/case-5-terminal-loss")
    if term_loss.get("skip"):
        problems.append("case-5-terminal-loss is an unconditional skip")
    if not term_loss.get("close_master"):
        problems.append("case-5-terminal-loss does not close the pty master")
    check("case-5-terminal-loss-model", term_loss["expect_calls"],
          [(-2, 0, [])])

    # --- the child source: shared parts ---------------------------------
    src = build_child_source(_case("m42-imp3/case-1-no-input"))
    if "eval-scheme" not in src:
        problems.append("child source lost the eval-scheme call")
    if "(external-debugging-output ?R)" not in src:
        problems.append("child source lost the PTY-ready signal")
    if "call-with-input-file \\\"/tmp/pty-driver-selftest-gate\\\" read-char" \
            not in src:
        problems.append("child source lost the blocking FIFO gate")
    # The child binds inhibit-quit, so a stored quit byte (m42 cases 4 and
    # 6) cannot abort the load before the report is written.
    if "(let ((inhibit-quit t))" not in src:
        problems.append("child source does not bind inhibit-quit")
    # The child ignores SIGHUP before the read, so the driver can close
    # the pty master for the case-5 terminal-loss measurement without
    # terminating the child.  The call must be guarded so a host without
    # `sigaction' still reaches the READY signal.
    if '(condition-case nil (eval-scheme "(sigaction 1 1)") (error nil))' not in src:
        problems.append("child source does not guard the SIGHUP ignore call")
    # Every case must build a child source with no placeholder left.
    # build_probe raises on an unresolved @@NAME@@, so this also proves
    # each case fills in every placeholder its probe declares.
    for case in CASES:
        try:
            if "eval-scheme" not in build_child_source(case):
                problems.append("case %s builds no child source" % case["name"])
        except AssertionError as err:
            problems.append(str(err))
    # The guard has teeth: an unfilled placeholder must raise.
    try:
        build_probe({"name": "probe-guard", "probe": "@@NOPE@@", "subst": {}})
        problems.append("build_probe accepts an unresolved placeholder")
    except AssertionError:
        pass

    # --- the child source: the M42 read-path probe ------------------------
    if "module-ref mod 'tty-read-avail-input!" not in src:
        problems.append("probe does not resolve tty-read-avail-input! via module-ref")
    if "(tty-read-avail-input! term)" in src:
        problems.append("probe still calls tty-read-avail-input! unqualified")
    # %terminal-list and %--kbd-buffer-nr-stored force to procedures that
    # must be called: a single (force ...) reads the procedure, not its
    # value, and the report would carry a procedure instead of a count.
    if "((force (module-ref mod '%terminal-list)))" not in src:
        problems.append("probe does not call the forced %terminal-list procedure")
    if "((force nr))" not in src:
        problems.append("probe does not call the forced %--kbd-buffer-nr-stored procedure")
    probe = build_probe(_case("m42-imp3/case-1-no-input"))
    # The probe records (code . mods) and reports "code:mods" tokens.
    if "(cons code mods)" not in probe:
        problems.append("probe does not record the modifier with the code")
    if '":"' not in probe:
        problems.append("probe does not build a code:mods order token")
    # The probe computes the STORED count itself, as a difference.  An
    # absolute count would depend on what the buffer held at startup.
    if "(- n1 prev)" not in probe:
        problems.append("probe does not report stored as a difference")
    # The probe builds the one wire format: the EMPTY token for no events
    # and the JOIN separator between calls.
    if '"%s"' % EMPTY not in probe:
        problems.append("probe does not emit the EMPTY token for an empty order")
    if '"%s"' % JOIN not in probe:
        problems.append("probe does not join the calls with the JOIN separator")
    # The probe takes the newest terminal.  %terminal-list is oldest-first,
    # so the head is the oldest; the probe must reverse it.
    if "(and (pair? terms) (car terms))" in probe:
        problems.append("probe takes the oldest terminal, not the newest")
    if "(reverse terms)" not in probe:
        problems.append("probe does not select the newest terminal")
    # The call count comes from the length of the expected call list, so a
    # case cannot ask for two calls and expect one report field.
    if "(calls 1)" not in probe:
        problems.append("single-call case does not set calls to 1")
    two = build_probe(_case("m42-imp4/case-6-continuation"))
    if "(calls 2)" not in two:
        problems.append("continuation case does not set calls to 2")

    # Stubs appear only when a case asks for them, and restore after.
    if "%--tty-meta-key (delay (lambda (t)" in src:
        problems.append("probe stubs the meta key when no case asked")
    stubbed = build_child_source(_case("m42-imp4/case-4-meta-quit-guard"))
    if "%--tty-meta-key (delay (lambda (t) 1))" not in stubbed:
        problems.append("probe does not stub %--tty-meta-key")
    if "%--quit-char (delay (lambda () 7))" not in stubbed:
        problems.append("probe does not stub %--quit-char")
    if "(module-set! mod '%--tty-meta-key meta-o)" not in stubbed:
        problems.append("probe does not restore %--tty-meta-key")

    # --- the child source: the M43 probes ---------------------------------
    mode_src = build_child_source(_case("m43-imp3/pty-e2e"))
    if "module-ref mod 'tty-mode-wanted" not in mode_src:
        problems.append("mode probe does not resolve tty-mode-wanted via module-ref")
    if "init 0 base flags" not in mode_src:
        problems.append("mode probe does not apply the mode through init-tty-mode")
    restore_src = build_child_source(_case("m43-imp4/pty-e2e"))
    if "module-ref mod 'reset-tty-mode" not in restore_src:
        problems.append("restore probe does not resolve reset-tty-mode via module-ref")
    if "module-ref mod 'init-tty-mode" not in restore_src:
        problems.append("restore probe does not resolve init-tty-mode via module-ref")
    if "reset 0 saved" not in restore_src:
        problems.append("restore probe does not restore through reset-tty-mode")
    size_src = build_child_source(_case("m43-imp5/pty-e2e"))
    if "module-ref mod 'tty-size" not in size_src:
        problems.append("size probe does not resolve tty-size via module-ref")
    if "module-ref mod 'set-tty-size" not in size_src:
        problems.append("size probe does not resolve set-tty-size via module-ref")
    if "set-size 0 %d %d" % (SIZE_HEIGHT, SIZE_WIDTH) not in size_src:
        problems.append("size probe does not apply the case size through set-tty-size")
    # The size probe REPORTS its measurement; it must not judge.  A
    # literal "ok" there would mean the verdict crept back into Scheme.
    if '"ok"' in SIZE_PROBE:
        problems.append("size probe judges instead of reporting its measurement")
    # The two mode probes do judge, and must keep the literal their case
    # expects; a probe that lost it could never pass.
    for case in (_case("m43-imp3/pty-e2e"), _case("m43-imp4/pty-e2e")):
        if '"ok"' not in case["probe"]:
            problems.append("probe of %s cannot report ok" % case["name"])
    # The case data left the probes: the flags and the size are spliced
    # in, so neither probe holds a literal of its own.
    for name, probe in (("mode", MODE_PROBE), ("restore", RESTORE_PROBE)):
        if "@@FLAGS@@" not in probe:
            problems.append("%s probe hardcodes its flags" % name)
        if "@@MODE_HELPERS@@" not in probe:
            problems.append("%s probe does not splice the shared mode helpers"
                            % name)
    if "@@HEIGHT@@" not in SIZE_PROBE or "@@WIDTH@@" not in SIZE_PROBE:
        problems.append("size probe hardcodes its size")
    # The shared comparison really is shared: one definition, two users.
    for name, src in (("mode", mode_src), ("restore", restore_src)):
        if "(define (mode=? a b)" not in src:
            problems.append("%s probe lost the shared mode comparison" % name)
        if "bytevector-u8-ref" not in src:
            problems.append("%s probe lost the cc bytevector walk" % name)
    # The flags reach both probes with the quit char the policy needs.
    for name, src in (("mode", mode_src), ("restore", restore_src)):
        if "'quit-char 7" not in src:
            problems.append("%s probe did not receive the case flags" % name)
    # A probe must not carry another family's body: a swapped probe would
    # report the wrong string and never match.
    if "tty-read-avail-input!" in mode_src:
        problems.append("the mode case carries the read-path probe")
    if "tty-mode-wanted" in src:
        problems.append("the read-path case carries the mode probe")

    # --- the ISIG clear ---------------------------------------------------
    # FIX-20260928-guilemacs: run_case must clear ISIG on the pty before it
    # writes the case bytes.  Emacs arms the tty with ISIG and
    # c_cc[VQUIT] = quit_char (src/sysdep.c, init_sys_modes), so the line
    # discipline reads a written raw quit byte as VQUIT, flushes the queue
    # and raises SIGQUIT.  The failing run measured "2 2 67:0,68:0" for
    # case 4 and "1 1 66:0" for case 6 -- the bytes after the quit byte
    # only.  Without the clear, both cases fail on a pty host.
    deliver_src = inspect.getsource(deliver_raw)
    run_src = inspect.getsource(run_case)
    if "~termios.ISIG" not in deliver_src:
        problems.append("deliver_raw does not clear ISIG")
    if deliver_src.count("tcgetattr") < 2:
        problems.append("deliver_raw does not read the attributes back")
    if "deliver_raw(master)" not in run_src:
        problems.append("run_case does not deliver the case bytes raw")
    if "ISIG clear on the pty failed" not in run_src:
        problems.append("run_case does not route a deliver_raw failure to an INFO skip")

    # deliver_raw must report its own failure, not swallow it.  Stand in
    # for the termios calls -- no pty is needed, because only tcgetattr
    # and tcsetattr are replaced.  tcgetattr returns a 7-item list
    # [iflag, oflag, cflag, lflag, ispeed, ospeed, cc]; index 3 is c_lflag.
    def _attrs(lflag):
        return [0, 0, 0, lflag, 0, 0, []]

    saved_getattr = termios.tcgetattr
    saved_setattr = termios.tcsetattr
    try:
        def _raise(errno, msg):
            # termios raises termios.error, not OSError: the stand-in must
            # match, or this check has no teeth (F1).  termios.error is not
            # an OSError subclass and carries no .errno/.strerror.
            raise termios.error(errno, msg)

        # A failing termios call must be caught.  termios.error proves the
        # guard catches the real error type, not just OSError.
        if "termios.error" not in deliver_src:
            problems.append("deliver_raw does not catch termios.error")

        # tcgetattr itself fails.
        termios.tcgetattr = lambda fd: _raise(9, "Bad file descriptor")
        got = deliver_raw(0)
        check("deliver_raw reports a tcgetattr failure",
              isinstance(got, str) and "tcgetattr" in got, True)
        # tcsetattr fails.
        termios.tcgetattr = lambda fd: _attrs(termios.ISIG)
        termios.tcsetattr = lambda fd, how, attrs: _raise(5, "I/O error")
        got = deliver_raw(0)
        check("deliver_raw reports a tcsetattr failure",
              isinstance(got, str) and "tcsetattr" in got, True)
        # The clear does not stick: the read-back still shows ISIG.
        termios.tcgetattr = lambda fd: _attrs(termios.ISIG)
        termios.tcsetattr = lambda fd, how, attrs: None
        got = deliver_raw(0)
        check("deliver_raw reports a clear that did not take effect",
              isinstance(got, str) and "did not take effect" in got, True)
        # The clear sticks: the read-back shows ISIG gone, return None.
        state = {"lflag": termios.ISIG}

        def _set(fd, how, attrs):
            state["lflag"] = attrs[3]

        termios.tcgetattr = lambda fd: _attrs(state["lflag"])
        termios.tcsetattr = _set
        got = deliver_raw(0)
        check("deliver_raw returns None when the clear takes effect", got, None)
    finally:
        termios.tcgetattr = saved_getattr
        termios.tcsetattr = saved_setattr

    # --- the Scheme formatter against the Python renderer ---------------
    # The probe's fmt-call only ever runs inside the child, on a pty
    # host.  This drives the same helpers under guile and compares them
    # with render_call, so a formatter that disagrees with the expected
    # string is caught here instead of on a pty host.
    for problem in selftest_scheme():
        if problem.startswith("INFO "):
            print("SELFTEST %s" % problem)
        else:
            problems.append(problem)

    if problems:
        for problem in problems:
            print("SELFTEST FAIL %s" % problem)
        return 1
    print("SELFTEST OK")
    return 0


def main(argv):
    ap = argparse.ArgumentParser(
        description="the common pty driver for the TTY behaviour tests")
    ap.add_argument("--emacs", help="path to the emacs under test")
    ap.add_argument("--group", choices=list(GROUPS), default=None,
                    help="run only this case group (default: all cases)")
    ap.add_argument("--case", action="append", default=None,
                    help="run only this case name (repeatable)")
    ap.add_argument("--timeout", type=float, default=20.0,
                    help="seconds to wait for a child report")
    ap.add_argument("--selftest", action="store_true",
                    help="run the pty-free parser/source checks and exit")
    opts = ap.parse_args(argv)

    if opts.selftest:
        return selftest()

    if not opts.emacs:
        ap.error("--emacs is required unless --selftest is given")

    cases = group_cases(opts.group)
    if opts.case:
        wanted = set(opts.case)
        cases = [c for c in cases if c["name"] in wanted]

    if not (os.path.isfile(opts.emacs) and os.access(opts.emacs, os.X_OK)):
        skip_all(cases, "no built src/emacs at %s" % opts.emacs)
        return 0

    # Probe the pty before spawning anything: a host that refuses a pty
    # denies every case in the same way, so one look is enough, and the
    # child never starts when there is no pty to give it.
    try:
        m, s = os.openpty()
        os.close(m)
        os.close(s)
    except OSError as err:
        skip_all(cases, "no pty: errno %d %s" % (err.errno, err.strerror))
        return 0

    for case in cases:
        name, kind, detail = run_case(case, opts.emacs, opts.timeout)
        emit(kind, name, detail)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
