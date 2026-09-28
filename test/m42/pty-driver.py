#!/usr/bin/env python3
"""pty-driver.py --- M42 imp-3: run the TTY raw-input read path on a pty.

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
and exits 0.  That is the accepted imp-3 outcome on this host; it is not
a PASS and not a FAIL.

Python 3 only.  No third-party module.

Usage:
    pty-driver.py --emacs <path-to-src/emacs> [--case <name>]... \
                  [--timeout <seconds>]
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

# The two imp-3 cases (brief.org section 7).  Each case names the bytes
# to push into the pty master and the expected read-path result.
#
#   expect_return -- the value the path returns (the read count).
#   expect_stored -- the number of events stored in kbd_buffer.
#   expect_order  -- the decoded key codes, in store order.
#
# Case 1: the pty holds no bytes.  The path returns 0 and stores nothing.
# Case 2: two bytes, far fewer than one batch (KBD_BUFFER_SIZE - 1 =
#         4095).  The path returns the short count (2) and stores exactly
#         two events, in order.  It must not wait for the rest of a batch.
CASES = (
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
        "expect_order": [0x41, 0x42],
    },
)

# The Scheme probe the child evaluates.  It reaches the real policy
# through (emacs gobble): take the newest terminal, record every decoded
# keystroke the policy makes, call tty-read-avail-input!, and report
# (RETURN STORED-BEFORE STORED-AFTER ORDER-STRING).
#
# `eval-scheme' evaluates its string in the current module, not in
# (emacs gobble), so every binding the probe needs -- including
# tty-read-avail-input! -- is taken with `module-ref'.  A bare
# (tty-read-avail-input! ...) is an unbound variable there and makes the
# child error out before it reports.
#
# The four (emacs gobble) leaves are `defelisp' promises.  Three of them
# force to a PROCEDURE that is then called -- %terminal-list and
# %--kbd-buffer-nr-stored take no argument, %--ie-ascii-keystroke-event
# takes (CODE MODS FRAME); see gobble.scm:195, :256, :290.  A single
# (force ...) yields the procedure, not its value, so those three need
# double parentheses: ((force %terminal-list)).  tty-read-avail-input! is
# a plain (define ...) procedure, so a single force-then-call is right.
#
# ORDER-STRING is a Scheme string of space-separated key codes.  An empty
# key-code list must not be reported as the raw Scheme list: an empty
# Scheme list reached through `eval-scheme' prints as the opaque
# "#<scheme ()>" object, which the driver regex would reject and turn a
# passing no-input case into a false FAIL.
#
# The probe reads the terminal list and the two C leaves as they are at
# run time.  It changes no module and restores the one shim it overrides.
CHILD_PROBE = r"""
(let* ((mod (resolve-module '(emacs gobble)))
       (terms ((force (module-ref mod '%terminal-list))))
       (term (and (pair? terms) (car terms)))
       (mk (module-ref mod '%--ie-ascii-keystroke-event))
       (nr (module-ref mod '%--kbd-buffer-nr-stored))
       (read! (module-ref mod 'tty-read-avail-input!))
       (n0 ((force nr)))
       (order '()))
  (module-set!
   mod '%--ie-ascii-keystroke-event
   (delay (let ((f (force mk)))
            (lambda (code mods frame)
              (set! order (append order (list code)))
              (f code mods frame)))))
  (let* ((ret (if term (read! term) 'no-terminal))
         (order-str (let loop ((l order) (s ""))
                      (if (null? l) s
                          (loop (cdr l)
                                (string-append s (number->string (car l)) " ")))))
         (n1 ((force nr))))
    (module-set! mod '%--ie-ascii-keystroke-event mk)
    (list ret n0 n1 order-str)))
"""

# The child program.  It is written to a temp file and loaded by the
# emacs under test with -l.  Loading this file means Emacs has completed
# its terminal setup.  The child signals READY on stderr, then blocks in
# Guile on a FIFO gate.  The driver writes the case bytes before releasing
# the gate, so Emacs cannot consume those bytes during an elisp sleep.
# The child writes its report to stderr (the report pipe), never the pty.
CHILD_PROGRAM = r""";;; m42-imp3-child.el --- the emacs under test's pty probe.
;;; Written by test/m42/pty-driver.py.  Writes its report to stderr
;;; (the report pipe), never to the pty.
(progn
  ;; Emacs has set up the tty before loading this file.  Tell the driver
  ;; it is safe to write input now; the Scheme probe blocks on its FIFO
  ;; gate until the bytes have been written.
  (external-debugging-output ?R)
  (external-debugging-output ?E)
  (external-debugging-output ?A)
  (external-debugging-output ?D)
  (external-debugging-output ?Y)
  (external-debugging-output ?\n)
  (let ((res (condition-case err
                 (eval-scheme %(probe)s)
               (error (format "%%S" err)))))
    (let ((line (format "%%S\n" res)))
      (dotimes (i (length line))
        (external-debugging-output (aref line i)))))
  (kill-emacs 0))
"""

# The report is the elisp %S of (RETURN BEFORE AFTER ORDER-STRING).  ORDER
# is a Scheme string of space-separated key codes, so an empty order never
# prints as an opaque "#<scheme ()>" object that the regex would reject.
REPORT_RE = re.compile(r'^\((no-terminal|-?\d+)\s+(\d+)\s+(\d+)\s+"([^"]*)"\)$')


def emit(kind, name, detail=None):
    """Print one report line on stdout."""
    if kind == "INFO":
        print("INFO %s skipped (%s)" % (name, detail))
    elif kind == "PASS":
        print("PASS %s" % name)
    else:
        print("FAIL %s %s" % (name, detail))


def skip_all(reason):
    """Print one INFO line per case.  Never a PASS, never a FAIL."""
    for case in CASES:
        emit("INFO", case["name"], reason)


def build_child_source(gate_path="/tmp/m42-imp3-selftest-gate"):
    """Return child elisp that waits on GATE_PATH before probing."""
    # Embed the probe as an elisp string literal.  Escape backslash and
    # double quote; the probe uses double-quoted strings (the order
    # string) but no backslash.
    gate = '"%s"' % gate_path.replace("\\", "\\\\").replace('"', '\\"')
    scheme_probe = "(begin (call-with-input-file %s read-char) %s)" % (
        gate, CHILD_PROBE.strip())
    probe = scheme_probe.replace("\\", "\\\\").replace('"', '\\"')
    return CHILD_PROGRAM % {"probe": '"%s"' % probe}


def parse_report(text):
    """Parse the child's report line into (ret, before, after, order)."""
    for line in text.splitlines():
        m = REPORT_RE.match(line.strip())
        if not m:
            continue
        ret_tok, before, after, order_tok = m.groups()
        ret = ret_tok if ret_tok == "no-terminal" else int(ret_tok)
        order = [int(x) for x in order_tok.split() if x]
        return ret, int(before), int(after), order
    return None


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
    check("empty-order", parse_report('(0 0 0 "")'), (0, 0, 0, []))
    check("short-read", parse_report('(2 0 2 "65 66 ")'), (2, 0, 2, [65, 66]))
    check("terminal-loss", parse_report('(-2 1 1 "")'), (-2, 1, 1, []))
    check("no-terminal", parse_report('(no-terminal 0 0 "")'),
          ("no-terminal", 0, 0, []))
    check("noise-around-report",
          parse_report('garbage\n(2 0 2 "65 66 ")\ntrailing\n'),
          (2, 0, 2, [65, 66]))
    check("no-report", parse_report("no report here"), None)
    # Regression pin: the old opaque empty-list form must not parse.
    check("rejects-opaque-empty", parse_report("(0 0 0 #<scheme ()>)"), None)

    src = build_child_source()
    # The probe must reach tty-read-avail-input! through module-ref: a bare
    # call is an unbound variable in the eval-scheme module.
    if "module-ref mod 'tty-read-avail-input!" not in src:
        problems.append("probe does not resolve tty-read-avail-input! via module-ref")
    if "(tty-read-avail-input! term)" in src:
        problems.append("probe still calls tty-read-avail-input! unqualified")
    if "eval-scheme" not in src:
        problems.append("child source lost the eval-scheme call")
    if "(external-debugging-output ?R)" not in src:
        problems.append("child source lost the PTY-ready signal")
    if "call-with-input-file \\\"/tmp/m42-imp3-selftest-gate\\\" read-char" not in src:
        problems.append("child source lost the blocking FIFO gate")
    # %terminal-list and %--kbd-buffer-nr-stored force to procedures that
    # must be called: a single (force ...) reads the procedure, not its
    # value, and the report carries non-numeric fields the regex rejects.
    if "((force (module-ref mod '%terminal-list)))" not in src:
        problems.append("probe does not call the forced %terminal-list procedure")
    if "((force nr))" not in src:
        problems.append("probe does not call the forced %--kbd-buffer-nr-stored procedure")

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
        mode="w", suffix="-m42-imp3-child.el", delete=False)
    tmp_path = tmp.name
    tmp.close()
    gate_path = tmp_path + ".gate"
    gate_fd = None
    os.mkfifo(gate_path)
    with open(tmp_path, "w") as child_file:
        child_file.write(build_child_source(gate_path))
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
                    if case["bytes"]:
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
        # write failed -- a harness error, not an environment gap.  A
        # terminal-loss EIO maps to the close-terminal result -2 (D2);
        # report the measured errno so case 5 (imp-4) can assert it.
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

    ret, before, after, order = got
    stored = after - before
    detail = ("return %r stored %d order %r (want return %r stored %d "
              "order %r)" % (ret, stored, order,
                             case["expect_return"], case["expect_stored"],
                             case["expect_order"]))
    if (ret == case["expect_return"]
            and stored == case["expect_stored"]
            and order == case["expect_order"]):
        return (name, "PASS", detail)
    return (name, "FAIL", detail)


def main(argv):
    ap = argparse.ArgumentParser(description="M42 imp-3 pty driver")
    ap.add_argument("--emacs", help="path to the emacs under test")
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

    cases = CASES
    if opts.case:
        wanted = set(opts.case)
        cases = [c for c in CASES if c["name"] in wanted]

    if not (os.path.isfile(opts.emacs) and os.access(opts.emacs, os.X_OK)):
        skip_all("no built src/emacs at %s" % opts.emacs)
        return 0

    # Probe the pty before spawning anything: a host that refuses a pty
    # denies every case in the same way, so one look is enough, and the
    # child never starts when there is no pty to give it.
    try:
        m, s = os.openpty()
        os.close(m)
        os.close(s)
    except OSError as err:
        skip_all("no pty: errno %d %s" % (err.errno, err.strerror))
        return 0

    for case in cases:
        name, kind, detail = run_case(case, opts.emacs, opts.timeout)
        emit(kind, name, detail)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
