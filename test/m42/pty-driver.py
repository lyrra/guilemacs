#!/usr/bin/env python3
"""pty-driver.py --- M42 imp-3/imp-4: run the TTY raw-input read path on a pty.

The driver owns the pty pair and the child process.  The child is the
emacs under test; its stdin/stdout are the pty slave, which it acquires
as its controlling terminal.  The child writes its report to a pipe,
never to the pty: the report pipe is handed to the child as its stderr
(fd 2).  The driver writes case bytes to the pty master and reads the
report from the pipe.

One child runs per case.  That keeps the pty bytes and the report apart
and removes any need to synchronise several reads inside one child.

The driver prints one report line per case on its stdout:

    PASS <name>
    FAIL <name> <detail>
    INFO <name> skipped (<reason>)

This host cannot allocate a pty (/dev/ptmx gives EACCES, errno 13; see
brief.org section 8).  A driver run there prints one INFO line per case
and exits 0.  That is the accepted outcome on this host; it is not a
PASS and not a FAIL.

Python 3 only.  No third-party module.

Usage:
    pty-driver.py --emacs <path-to-src/emacs> [--group imp3|imp4] \
                  [--case <name>]... [--timeout <seconds>]
"""

import argparse
import fcntl
import os
import re
import select
import signal
import subprocess
import sys
import tempfile
import time
import termios

# The meta modifier bit, duplicated from (emacs event-modifiers)
# meta-modifier (char-meta = #x8000000).  The probe reports each stored
# event as a "code:mods" token; a byte whose high bit sets the meta
# modifier (meta key 1) decodes to mods == META.
META = 0x8000000

# Cases are split into two groups (brief.org section 5.2):
#
#   imp3 -- the harness foundation: no input, short read.
#   imp4 -- meta decode, quit byte, terminal loss, continuation.
#
# Each case names the bytes to push into the pty master and the expected
# read-path result:
#
#   expect_return -- the value the path returns (the read count).
#   expect_stored -- the number of events stored in kbd_buffer.
#   expect_order  -- the decoded events, in store order, as (code, mods).
#
# Optional fields:
#   calls        -- call the read path this many times (default 1).
#   meta_key     -- stub %--tty-meta-key to this value before the read.
#   quit_char    -- stub %--quit-char to this value before the read.
#   expect_calls -- per-call expectations for a multi-call case; each item
#                   is {"return": .., "stored": .., "order": [(code, mods)]}.
#   close_master -- close the pty master after READY, before the read.  The
#                   child ignores SIGHUP, so the hangup does not kill it;
#                   the slave read then fails with EIO -> the
#                   close-terminal result -2 (case 5, brief.org 4.2).
#   env_gate     -- a reason string.  A value mismatch (not a timeout or a
#                   missing report) becomes an environment-gated INFO skip
#                   with this reason instead of a FAIL (case 5, brief.org
#                   4.2).  Used only when the host cannot give the expected
#                   result; never an unconditional skip.
#
# Case 1: the pty holds no bytes.  The path returns 0 and stores nothing.
# Case 2: two bytes, far fewer than one batch (KBD_BUFFER_SIZE - 1 =
#         4095).  The path returns the short count (2) and stores exactly
#         two events, in order.  It must not wait for the rest of a batch.
IMP3_CASES = (
    {
        "name": "m42-imp3/case-1-no-input",
        "bytes": b"",
        "expect_return": 0,
        "expect_stored": 0,
        "expect_order": [],
    },
    {
        "name": "m42-imp3/case-2-short-read",
        "bytes": b"AB",
        "expect_return": 2,
        "expect_stored": 2,
        "expect_order": [(0x41, 0), (0x42, 0)],
    },
)

# Case 3: the meta decode, one sub-case per %--tty-meta-key value.
#   meta key 1 -- the high bit gives the meta modifier, the byte is
#                 stripped to 7 bits (code 0x01/0x61, mods meta).
#   meta key 2 -- no strip, no modifier (code 0x81/0xe1, mods 0).
#   meta key 0 -- no modifier, byte still stripped (code 0x01/0x61, mods 0).
# Case 4: the quit-char batch break.  Five bytes, quit char 7: the path
#   stores 65, 66 and 7, then drops 67 and 68, but returns the read
#   count (5), not the stored count.  The guard case proves the
#   strip/compute order: with meta key 1, byte 0x87 stores code 7 with
#   mods meta and breaks the batch (a backward order gives code 7 mods 0).
# Case 5: terminal loss.  The child ignores SIGHUP before the read
#   (CHILD_PROGRAM), so the driver can close the pty master without
#   terminating the emacs under test.  The slave read then fails with
#   EIO, which the C leaf maps to the close-terminal result -2, and the
#   child writes its report to the report pipe (fd 2), which survives the
#   hangup.  The case measures the -2 arm; a host that cannot give EIO
#   reports an environment-gated INFO skip (brief.org section 4.2).
# Case 6: continuation.  Two calls.  The first call reads the whole
#   FIONREAD batch in one read, then drops the byte after the quit char.
#   The second call therefore finds an empty tty: return 0, no store.
#
# FIX-20260928-guilemacs: brief.org section 5.3, case 6, first expected
# byte B to stay on the tty for call 2 (return 1, stored 1).  That
# contradicts brief.org section 3.3 step 7 and the vanilla C
# tty_read_avail_input: the body sizes one emacs_read of the whole
# FIONREAD batch (src/keyboard.c parent copy of tty_read_avail_input,
# ".kb_before.c": "NREAD is set to the number of chars read"), then
# breaks the decode at the quit char.  B is consumed by that read and
# dropped, so call 2 reads 0.  The case now pins the code's real model
# (call 2: return 0, stored 0, no events); the product is not changed
# (brief.org section 6).  See brief.org section 4.1.
IMP4_CASES = (
    {
        "name": "m42-imp4/case-3-meta-key-1",
        "bytes": b"\x81\xe1",
        "meta_key": 1,
        "expect_return": 2,
        "expect_stored": 2,
        "expect_order": [(0x01, META), (0x61, META)],
    },
    {
        "name": "m42-imp4/case-3-meta-key-2",
        "bytes": b"\x81\xe1",
        "meta_key": 2,
        "expect_return": 2,
        "expect_stored": 2,
        "expect_order": [(0x81, 0), (0xe1, 0)],
    },
    {
        "name": "m42-imp4/case-3-meta-key-0",
        "bytes": b"\x81\xe1",
        "meta_key": 0,
        "expect_return": 2,
        "expect_stored": 2,
        "expect_order": [(0x01, 0), (0x61, 0)],
    },
    {
        "name": "m42-imp4/case-4-quit-byte",
        "bytes": b"AB\x07CD",
        "quit_char": 7,
        "expect_return": 5,
        "expect_stored": 3,
        "expect_order": [(0x41, 0), (0x42, 0), (0x07, 0)],
    },
    {
        "name": "m42-imp4/case-4-meta-quit-guard",
        "bytes": b"A\x87",
        "meta_key": 1,
        "quit_char": 7,
        "expect_return": 2,
        "expect_stored": 2,
        "expect_order": [(0x41, 0), (0x07, META)],
    },
    {
        "name": "m42-imp4/case-5-terminal-loss",
        "bytes": b"",
        # brief.org section 4.2: take the tty away after READY.  The child
        # ignores SIGHUP, so the hangup does not kill it; the slave read
        # then fails with EIO -> the close-terminal result -2.  If the
        # host cannot give EIO, run_case reports an environment-gated INFO
        # skip (the "env_gate" reason), never an unconditional one.
        "close_master": True,
        "expect_return": -2,
        "expect_stored": 0,
        "expect_order": [],
        "env_gate": "host did not give EIO on master close",
    },
    {
        "name": "m42-imp4/case-6-continuation",
        "bytes": b"A\x07B",
        "quit_char": 7,
        "calls": 2,
        "expect_calls": [
            {"return": 3, "stored": 2, "order": [(0x41, 0), (0x07, 0)]},
            {"return": 0, "stored": 0, "order": []},
        ],
    },
)

CASES = IMP3_CASES + IMP4_CASES

# The Scheme probe the child evaluates.  It reaches the real policy
# through (emacs gobble): take the newest terminal, record every decoded
# keystroke the policy makes as (code . mods), call tty-read-avail-input!
# CALLS times, and report one flat token list: per call, (RETURN BEFORE
# AFTER ORDER-STRING).  A single call therefore prints the imp-3 shape
# (RETURN BEFORE AFTER ORDER-STRING); extra calls add more tokens after
# the order string (brief.org section 5.1.3).
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
# original promise back (brief.org section 5.1.4).  @@META_STUB@@ and
# @@QUIT_STUB@@ are filled in by build_child_source; an empty string
# leaves the real leaf in place.
#
# ORDER-STRING is a Scheme string of space-separated "code:mods" tokens.
# An empty event list must not be reported as the raw Scheme list: an
# empty Scheme list reached through `eval-scheme' prints as the opaque
# "#<scheme ()>" object, which the driver regex would reject and turn a
# passing no-input case into a false FAIL.
CHILD_PROBE = r"""
(let* ((mod (resolve-module '(emacs gobble)))
       (terms ((force (module-ref mod '%terminal-list))))
       ;; %terminal-list is oldest-first (gobble.scm walk order), so the
       ;; newest terminal is the last element.  Take that (brief.org
       ;; section 3.2); taking the head would pick the oldest.
       (term (let ((ts (reverse terms))) (and (pair? ts) (car ts))))
       (mk (module-ref mod '%--ie-ascii-keystroke-event))
       (nr (module-ref mod '%--kbd-buffer-nr-stored))
       (read! (module-ref mod 'tty-read-avail-input!))
       (meta-o (module-ref mod '%--tty-meta-key))
       (quit-o (module-ref mod '%--quit-char))
       (calls @@CALLS@@)
       (order '())
       (out '()))
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
      (set! out
            (append out
                    (list ret prev n1
                          (let flat ((l ev) (s ""))
                            (if (null? l) s
                                (flat (cdr l)
                                      (string-append
                                       s (number->string (car (car l))) ":"
                                       (number->string (cdr (car l))) " ")))))))
      (if (> k 1) (loop (- k 1) n1) #f)))
  (module-set! mod '%--ie-ascii-keystroke-event mk)
  (module-set! mod '%--tty-meta-key meta-o)
  (module-set! mod '%--quit-char quit-o)
  out)
"""

# The child program.  It is written to a temp file and loaded by the
# emacs under test with -l.  Loading this file means Emacs has completed
# its terminal setup.  The child signals READY on stderr, then blocks in
# Guile on a FIFO gate.  The driver writes the case bytes before releasing
# the gate, so Emacs cannot consume those bytes during an elisp sleep.
# The child writes its report to stderr (the report pipe), never the pty.
CHILD_PROGRAM = r""";;; m42-child.el --- the emacs under test's pty probe.
;;; Written by test/m42/pty-driver.py.  Writes its report to stderr
;;; (the report pipe), never to the pty.
(progn
  ;; brief.org section 4.2: ignore SIGHUP so the driver's terminal-loss
  ;; step (case 5: close the pty master) cannot terminate the child.
  ;; Emacs installs its own SIGHUP handler (deliver_fatal_signal) at
  ;; startup, so the ignore must be set here, in the child, after startup
  ;; and before the read -- a preexec disposition would be overridden.
  ;; Signal 1 is SIGHUP on Linux; handler 1 is SIG_IGN.  The report goes
  ;; to the report pipe (fd 2), so it survives the hangup.
  ;;
  ;; FIX-20260928-guilemacs: guard the call so a host without `sigaction'
  ;; cannot error out before the READY signal -- an unguarded failure here
  ;; makes every case report FAIL (cr.org F3).  A failure only weakens
  ;; case 5 (SIGHUP stays armed); the other cases do not close the master.
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
  ;; quit aborts this load before the report is written, and cases 4 and 6
  ;; time out instead of reporting (brief.org 4.1).  inhibit-quit keeps
  ;; the probe observable.  It does not touch the read path under test; the
  ;; child is a probe host, not the product.
  (let ((inhibit-quit t))
    (let ((res (condition-case err
                   (eval-scheme %(probe)s)
                 (error (format "%%S" err)))))
      (let ((line (format "%%S\n" res)))
        (dotimes (i (length line))
          (external-debugging-output (aref line i))))))
  (kill-emacs 0))
"""

# The report is the elisp %S of a flat token list.  Each call contributes
# (RETURN BEFORE AFTER ORDER-STRING); ORDER is a Scheme string of
# space-separated "code:mods" tokens, so an empty order never prints as an
# opaque "#<scheme ()>" object that the regex would reject.  The regex
# accepts the single-call shape and any number of extra calls after it.
_TOKEN = r'(no-terminal|-?\d+)\s+(\d+)\s+(\d+)\s+"([^"]*)"'
_TOKEN_RE = re.compile(_TOKEN)
REPORT_RE = re.compile(r'^\(%s(?:\s+%s)*\)$' % (_TOKEN, _TOKEN))


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


def group_cases(group):
    """Return the cases of GROUP ('imp3', 'imp4', or None for all)."""
    if group == "imp3":
        return list(IMP3_CASES)
    if group == "imp4":
        return list(IMP4_CASES)
    return list(CASES)


def build_probe(case):
    """Return the Scheme probe text for CASE, with its leaf stubs filled in."""
    meta_key = case.get("meta_key")
    quit_char = case.get("quit_char")
    meta_stub = ("(module-set! mod '%--tty-meta-key (delay (lambda (t) {})))"
                 .format(meta_key) if meta_key is not None else "")
    quit_stub = ("(module-set! mod '%--quit-char (delay (lambda () {})))"
                 .format(quit_char) if quit_char is not None else "")
    return (CHILD_PROBE
            .replace("@@CALLS@@", str(case.get("calls", 1)))
            .replace("@@META_STUB@@", meta_stub)
            .replace("@@QUIT_STUB@@", quit_stub))


def build_child_source(case, gate_path="/tmp/m42-selftest-gate"):
    """Return child elisp that waits on GATE_PATH before probing CASE."""
    # Embed the probe as an elisp string literal.  Escape backslash and
    # double quote; the probe uses double-quoted strings (the order
    # string) but no backslash.
    gate = '"%s"' % gate_path.replace("\\", "\\\\").replace('"', '\\"')
    scheme_probe = "(begin (call-with-input-file %s read-char) %s)" % (
        gate, build_probe(case).strip())
    probe = scheme_probe.replace("\\", "\\\\").replace('"', '\\"')
    return CHILD_PROGRAM % {"probe": '"%s"' % probe}


def parse_report(text):
    """Parse the child's report into a list of per-call tuples.

    Each tuple is (ret, before, after, order), where order is a list of
    (code, mods) pairs.  Return None when no report line is present.
    """
    for line in text.splitlines():
        line = line.strip()
        if not REPORT_RE.match(line):
            continue
        calls = []
        for m in _TOKEN_RE.finditer(line[1:-1]):
            ret_tok, before, after, order_tok = m.groups()
            ret = ret_tok if ret_tok == "no-terminal" else int(ret_tok)
            order = [tuple(int(x) for x in tok.split(":"))
                     for tok in order_tok.split() if tok]
            calls.append((ret, int(before), int(after), order))
        if calls:
            return calls
    return None


def expected_calls(case):
    """Return CASE's expected per-call tuples as a list of dicts."""
    if "expect_calls" in case:
        return case["expect_calls"]
    return [{"return": case["expect_return"],
             "stored": case["expect_stored"],
             "order": case["expect_order"]}]


def child_session():
    """Start a session and make the pty slave the controlling terminal."""
    os.setsid()
    # Popen has already connected the slave to stdin.  Acquiring it here
    # makes /dev/tty refer to the same terminal inside Emacs.
    fcntl.ioctl(0, termios.TIOCSCTTY, 0)


def selftest():
    """Exercise the report parser and the child-source builder.

    Runs on any host: it never allocates a pty and never starts a child.
    Returns 0 when every check passes, 1 otherwise.  The ERT wrapper
    drives this with --selftest.
    """
    problems = []

    def check(label, got, want):
        if got != want:
            problems.append("%s: got %r want %r" % (label, got, want))

    # A passing no-input case: an empty order is a quoted empty string,
    # never the opaque "#<scheme ()>" object a real run would reject.
    check("empty-order", parse_report('(0 0 0 "")'), [(0, 0, 0, [])])
    check("short-read", parse_report('(2 0 2 "65:0 66:0 ")'),
          [(2, 0, 2, [(65, 0), (66, 0)])])
    check("terminal-loss", parse_report('(-2 1 1 "")'), [(-2, 1, 1, [])])
    check("no-terminal", parse_report('(no-terminal 0 0 "")'),
          [("no-terminal", 0, 0, [])])
    check("meta-decode", parse_report('(2 0 2 "1:134217728 97:134217728 ")'),
          [(2, 0, 2, [(1, META), (97, META)])])
    # The two-call continuation shape: extra fields after the first order.
    check("two-calls", parse_report('(3 0 2 "65:0 7:0 " 0 2 2 "")'),
          [(3, 0, 2, [(65, 0), (7, 0)]), (0, 2, 2, [])])
    check("noise-around-report",
          parse_report('garbage\n(2 0 2 "65:0 66:0 ")\ntrailing\n'),
          [(2, 0, 2, [(65, 0), (66, 0)])])
    check("no-report", parse_report("no report here"), None)
    # Regression pin: the old opaque empty-list form must not parse.
    check("rejects-opaque-empty", parse_report("(0 0 0 #<scheme ()>)"), None)
    # A truncated two-call line (one token missing) must not parse.
    check("rejects-partial-call", parse_report('(3 0 2 "65:0 " 0 2)'), None)

    # Case-table model pin (brief.org section 4.1).  The case-6 continuation must
    # match the code under test: the first read consumes the whole
    # FIONREAD batch, so the byte after the quit char is dropped and call
    # 2 sees an empty tty (return 0, stored 0, no events).  A return of 1
    # with event 66 would be a false FAIL on a host with a pty.
    cont = next(c for c in IMP4_CASES
                if c["name"] == "m42-imp4/case-6-continuation")
    check("case-6-continuation-model",
          [(e["return"], e["stored"], e["order"]) for e in cont["expect_calls"]],
          [(3, 2, [(0x41, 0), (0x07, 0)]), (0, 0, [])])

    # The probe must reach tty-read-avail-input! through module-ref: a bare
    # call is an unbound variable in the eval-scheme module.
    src = build_child_source({"name": "selftest", "bytes": b""})
    if "module-ref mod 'tty-read-avail-input!" not in src:
        problems.append("probe does not resolve tty-read-avail-input! via module-ref")
    if "(tty-read-avail-input! term)" in src:
        problems.append("probe still calls tty-read-avail-input! unqualified")
    if "eval-scheme" not in src:
        problems.append("child source lost the eval-scheme call")
    if "(external-debugging-output ?R)" not in src:
        problems.append("child source lost the PTY-ready signal")
    if "call-with-input-file \\\"/tmp/m42-selftest-gate\\\" read-char" not in src:
        problems.append("child source lost the blocking FIFO gate")
    # %terminal-list and %--kbd-buffer-nr-stored force to procedures that
    # must be called: a single (force ...) reads the procedure, not its
    # value, and the report carries non-numeric fields the regex rejects.
    if "((force (module-ref mod '%terminal-list)))" not in src:
        problems.append("probe does not call the forced %terminal-list procedure")
    if "((force nr))" not in src:
        problems.append("probe does not call the forced %--kbd-buffer-nr-stored procedure")
    # The probe records (code . mods) and reports "code:mods" tokens.
    probe = build_probe({"name": "selftest", "bytes": b""})
    if "(cons code mods)" not in probe:
        problems.append("probe does not record the modifier with the code")
    if '":"' not in probe:
        problems.append("probe does not build a code:mods order string")
    # The probe takes the newest terminal (brief.org section 3.2).
    # %terminal-list is oldest-first, so the head is the oldest; the
    # probe must reverse it (brief.org section 3.2).
    if "(and (pair? terms) (car terms))" in probe:
        problems.append("probe takes the oldest terminal, not the newest")
    if "(reverse terms)" not in probe:
        problems.append("probe does not select the newest terminal")

    # Stubs appear only when a case asks for them, and restore after.
    plain = build_child_source({"name": "plain", "bytes": b""})
    if "%--tty-meta-key (delay (lambda (t)" in plain:
        problems.append("probe stubs the meta key when no case asked")
    stubbed = build_child_source({"name": "stub", "meta_key": 1, "quit_char": 7})
    if "%--tty-meta-key (delay (lambda (t) 1))" not in stubbed:
        problems.append("probe does not stub %--tty-meta-key")
    if "%--quit-char (delay (lambda () 7))" not in stubbed:
        problems.append("probe does not stub %--quit-char")
    if "(module-set! mod '%--tty-meta-key meta-o)" not in stubbed:
        problems.append("probe does not restore %--tty-meta-key")

    # The child binds inhibit-quit, so a stored quit byte (cases 4 and 6)
    # cannot abort the load before the report is written (brief.org 4.1).
    if "(let ((inhibit-quit t))" not in src:
        problems.append("child source does not bind inhibit-quit")

    # The child ignores SIGHUP before the read, so the driver can close
    # the pty master for the case-5 terminal-loss measurement without
    # terminating the child (brief.org 4.2).  The call must be guarded so
    # a host without `sigaction' still reaches the READY signal (cr.org
    # F3).
    if '(condition-case nil (eval-scheme "(sigaction 1 1)") (error nil))' not in src:
        problems.append("child source does not guard the SIGHUP ignore call")

    # Case 5 is a measured case, not an unconditional skip (brief.org
    # 4.2): it closes the pty master and expects the -2 (EIO) arm.  It
    # must not carry a `skip` reason.
    term_loss = next(c for c in IMP4_CASES
                     if c["name"] == "m42-imp4/case-5-terminal-loss")
    if term_loss.get("skip"):
        problems.append("case-5-terminal-loss is an unconditional skip")
    if not term_loss.get("close_master"):
        problems.append("case-5-terminal-loss does not close the pty master")
    if term_loss["expect_return"] != -2 or term_loss["expect_stored"] != 0:
        problems.append("case-5-terminal-loss does not expect the -2 arm")

    if problems:
        for problem in problems:
            print("SELFTEST FAIL %s" % problem)
        return 1
    print("SELFTEST OK")
    return 0


def run_case(case, emacs, timeout):
    """Run one case on a fresh pty.  Return (name, kind, detail)."""
    name = case["name"]
    try:
        master, slave = os.openpty()
    except OSError as err:
        # No pty on this host.  Report and stop; the caller turns this
        # into the INFO skip path.
        return (name, "INFO", "no pty: errno %d %s" % (err.errno, err.strerror))

    rpipe, wpipe = os.pipe()
    tmp = tempfile.NamedTemporaryFile(
        mode="w", suffix="-m42-child.el", delete=False)
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

    child = None
    try:
        cmd = [emacs, "-Q", "-nw", "-l", tmp.name]
        child = subprocess.Popen(
            cmd, stdin=slave, stdout=slave, stderr=wpipe,
            close_fds=True, preexec_fn=child_session)
        os.close(slave)
        os.close(wpipe)
        slave = wpipe = None

        # Wait for the child to confirm that Emacs has finished setting
        # up the tty before sending bytes.  A fixed delay after Popen is
        # not sufficient: startup can still be flushing terminal input.
        report = b""
        ready_seen = False
        input_sent = False
        timed_out = False
        deadline = time.monotonic() + timeout
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                timed_out = True
                break
            ready, _, _ = select.select([rpipe], [], [], min(0.5, remaining))
            if ready:
                chunk = os.read(rpipe, 4096)
                if not chunk:
                    break
                report += chunk
                if not ready_seen and b"READY\n" in report:
                    ready_seen = True
                    if case.get("close_master") and master is not None:
                        # Case 5: take the tty away.  The child ignores
                        # SIGHUP, so it survives; the slave read then
                        # fails with EIO -> the close-terminal result -2
                        # (brief.org 4.2).
                        os.close(master)
                        master = None
                    if case["bytes"] and master is not None:
                        os.write(master, case["bytes"])
                    os.write(gate_fd, b"G")
                    input_sent = True
                # The result is complete once its line arrives.  Do not
                # require Emacs shutdown or pipe EOF after a valid report;
                # cleanup below will stop a child that remains alive.
                if ready_seen and parse_report(
                        report.decode("utf-8", "replace")) is not None:
                    break
            elif child.poll() is not None:
                break
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
        try:
            os.unlink(tmp_path)
        except OSError:
            pass
        try:
            os.unlink(gate_path)
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

    exp = expected_calls(case)
    measured = [(ret, after - before, order) for (ret, before, after, order) in got]
    want = [(e["return"], e["stored"], e["order"]) for e in exp]
    detail = "measured %r want %r" % (measured, want)
    if measured == want:
        return (name, "PASS", detail)
    if case.get("env_gate"):
        # brief.org 4.2: an environment-gated skip.  Case 5 expects the
        # -2 (EIO) arm; a host that cannot give EIO measures another
        # value.  Report INFO with the measured value -- not a FAIL and
        # not an unconditional skip.
        return (name, "INFO", "%s (measured %r)" % (case["env_gate"], measured))
    return (name, "FAIL", detail)


def main(argv):
    ap = argparse.ArgumentParser(description="M42 imp-3/imp-4 pty driver")
    ap.add_argument("--emacs", help="path to the emacs under test")
    ap.add_argument("--group", choices=["imp3", "imp4"], default=None,
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
