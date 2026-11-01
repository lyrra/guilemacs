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
import errno
import fcntl
import inspect
import os
import re
import select
import signal
import struct
import subprocess
import sys
import tempfile
import time
import termios

from pty_cases import *  # Case tables, probes, and their shared constants.
from pty_cases import _M58_IMP3_ITALIC_NEEDLE


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
    for needle in spec.get("needles", ()):
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
    # E4 of cr.org: prove that a run HAPPENED, not only that it stayed
    # under an upper bound.  `newline_count_re' extracts the line count N
    # that the probe sent as a marker before the span, and the span must
    # then hold at least N newline bytes.  A branch that never ran holds
    # no newline in the span, and this is a FAIL, not a pass.
    count_re = spec.get("newline_count_re")
    if count_re is not None:
        # The pty output is BYTES, so the marker pattern must be bytes too.
        pattern = count_re.encode() if isinstance(count_re, str) else count_re
        match = re.search(pattern, output)
        if match is None:
            return ("FAIL", "pty output held no line-count marker %r"
                    % (count_re,))
        want = int(match.group(1))
        held = inner.count(b"\n")
        if held < want:
            return ("FAIL", "pty span held %d newline bytes, want at least "
                    "the %d lines of the frame: the newline run did not "
                    "happen (measured %r)" % (held, want, inner))
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
    check("m61-imp2-case-count", len(group_cases("m61-imp2")), 7)
    check("m61-imp2g-case-count", len(group_cases("m61-imp2g")), 6)
    check("m61-imp3-case-count", len(group_cases("m61-imp3")), 8)
    check("total-case-count", len(CASES), 57)
    # --- the DERIVED crossing bound of ONE newline run ---------------
    # The case m61-imp3/newline-run-e2e pins an upper bound of
    #   base + lines / M61_IMP3_NEWLINE_SLACK_DIV
    # on the crossing pair.  The derivation is the point: the sink
    # answers the base pair (it does not grow with N), and the per-byte
    # loop of the C2 defect answers base + N.  This block asserts the
    # SEPARATION that the case depends on, for a wide span of line
    # counts, and the 3 rows that the brief records.  It is plain
    # arithmetic: it runs on a host with no pty and no build.
    def newline_bound(lines):
        slack = (M61_IMP3_NEWLINE_MARGIN
                 + lines // M61_IMP3_NEWLINE_SLACK_DIV)
        return (M61_IMP3_NEWLINE_BASE_C2S + slack,
                M61_IMP3_NEWLINE_BASE_S2C + slack)

    for lines, want in ((23, (16, 22)), (12, (14, 20)), (4, (12, 18)),
                        (3, (11, 17))):
        check("newline-bound-derivation-lines-%d" % lines,
              newline_bound(lines), want)
    for lines in range(M61_IMP3_NEWLINE_SKIP_LINES + 1, 501):
        bound = newline_bound(lines)
        # R5 of cr.org: the bound MUST keep a fixed margin above the base
        # pair, so a jitter of 1 crossing on a CORRECT tree stays green on
        # the shortest gated frame.  With a slack of N / 4 alone the frame
        # of 3 lines had no slack at all.
        margin = bound[0] - M61_IMP3_NEWLINE_BASE_C2S
        if margin < M61_IMP3_NEWLINE_MARGIN:
            problems.append(
                "newline bound of %d lines %r keeps a margin of %d "
                "crossings above the base pair, want at least %d"
                % (lines, bound, margin, M61_IMP3_NEWLINE_MARGIN))
        if (M61_IMP3_NEWLINE_BASE_C2S > bound[0]
                or M61_IMP3_NEWLINE_BASE_S2C > bound[1]):
            problems.append(
                "newline bound of %d lines %r rejects the ONE-run sink "
                "pair %r" % (lines, bound, (M61_IMP3_NEWLINE_BASE_C2S,
                                           M61_IMP3_NEWLINE_BASE_S2C)))
        per_byte = (M61_IMP3_NEWLINE_BASE_C2S + lines,
                    M61_IMP3_NEWLINE_BASE_S2C + lines)
        if per_byte[0] <= bound[0] or per_byte[1] <= bound[1]:
            problems.append(
                "newline bound of %d lines %r does not separate the "
                "per-byte pair %r, so the case can not see the C2 defect"
                % (lines, bound, per_byte))
    # The MARGIN costs separation on the shortest frames, so the SKIP arm
    # must cover every frame where the bound does NOT separate the 2
    # shapes (cr.org R5).  The selftest DERIVES that threshold from the
    # constants; it does not pin it.
    def newline_separates(lines):
        bound = newline_bound(lines)
        per_byte = (M61_IMP3_NEWLINE_BASE_C2S + lines,
                    M61_IMP3_NEWLINE_BASE_S2C + lines)
        return per_byte[0] > bound[0] and per_byte[1] > bound[1]

    first_gated = next(n for n in range(1, 100) if newline_separates(n))
    check("newline-skip-covers-the-blind-frames",
          M61_IMP3_NEWLINE_SKIP_LINES + 1, first_gated)
    # E4 of cr.org: the case proves that the run HAPPENED, so its span
    # spec MUST carry the line-count marker check.  A spec without it
    # would leave the case on an upper bound alone.
    newline_case = _case("m61-imp3/newline-run-e2e")
    newline_span = newline_case.get("span_requires") or {}
    check("newline-run-e2e-span-markers", newline_span.get("span"),
          (M61_IMP3_BEGIN, M61_IMP3_END))
    check("newline-run-e2e-newline-count-re",
          newline_span.get("newline_count_re"), r"M61-IMP3-N=(\d+)\|")

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
