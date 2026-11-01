"""Run a child on a PTY and return its observations."""

from dataclasses import dataclass, field
import errno
import fcntl
import os
import select
import signal
import struct
import subprocess
import tempfile
import termios
import time
from typing import Optional


@dataclass(frozen=True)
class SessionOptions:
    input_bytes: bytes = b""
    resize: Optional[tuple] = None
    close_master: bool = False
    capture_mode: bool = False
    wait_exit: bool = False
    termscript: bool = False
    load_fixture: Optional[str] = None
    env: dict = field(default_factory=dict)


@dataclass
class SessionResult:
    report: bytes = b""
    output: bytes = b""
    ready_seen: bool = False
    input_sent: bool = False
    timed_out: bool = False
    mode_before: object = None
    mode_after: object = None
    exit_status: Optional[int] = None
    termscript: Optional[bytes] = None
    error: Optional[tuple] = None


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


def run_session(emacs, timeout, options, fixture_env, build_child_source, is_complete):
    """Run a PTY session.  Callbacks build the child and detect completion."""
    try:
        master, slave = os.openpty()
    except OSError as err:
        # No pty on this host.  Report and stop; the caller turns this
        # into the INFO skip path.
        return SessionResult(error=("INFO", "no pty: errno %d %s" % (err.errno, err.strerror)))

    # Capture the pty mode BEFORE Popen (brief.org section 5).  Emacs
    # saves the startup tty mode and restores it on exit, so the
    # before/after compare holds even when the case delivers bytes and
    # deliver_raw later clears ISIG.  Reading the mode back only AFTER
    # the clear would report a false FAIL.
    mode_before = None
    if options.capture_mode:
        try:
            mode_before = termios.tcgetattr(master)
        except (OSError, termios.error):
            mode_before = None

    rpipe = wpipe = gate_fd = None
    tmp_path = gate_path = load_path = termscript_path = None
    child = None
    try:
        rpipe, wpipe = os.pipe()
        tmp = tempfile.NamedTemporaryFile(
            mode="w", suffix="-pty-child.el", delete=False)
        tmp_path = tmp.name
        tmp.close()
        gate_path = tmp_path + ".gate"
        os.mkfifo(gate_path)
        with open(tmp_path, "w") as child_file:
            child_file.write(build_child_source(gate_path))
        # Keep both FIFO ends open.  This makes the driver's write immediate
        # even if the child has not reached call-with-input-file yet.
        gate_fd = os.open(gate_path, os.O_RDWR | os.O_NONBLOCK)

        # A case may load a real Elisp fixture (M53 imp-3).
        # build_child_source splices its path (GATE_PATH + ".load.el"); write
        # the fixture there so the child's `load' finds it.
        load_path = gate_path + ".load.el"
        if options.load_fixture:
            with open(load_path, "w") as fixture_file:
                fixture_file.write(options.load_fixture)

        # A case may open a real termscript file (M54 imp-3).
        # build_child_source splices its path (GATE_PATH + ".termscript"); the
        # child opens it with open-termscript.
        termscript_path = gate_path + ".termscript"
        if options.termscript and os.path.exists(termscript_path):
            os.unlink(termscript_path)

        cmd = [emacs, "-Q", "-nw", "-l", tmp.name]
        child_env = os.environ.copy()
        child_env.update(options.env)
        child_env.update(fixture_env or {})
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
                        if not options.capture_mode:
                            os.close(master)
                            master = None
                except OSError as err:
                    # Linux pty masters report EIO after the slave closes.
                    if err.errno != errno.EIO:
                        raise
                    pty_eof = True
                    if not options.capture_mode:
                        os.close(master)
                        master = None
            if rpipe in ready:
                chunk = os.read(rpipe, 4096)
                if not chunk:
                    break
                report += chunk
                if not ready_seen and b"READY\n" in report:
                    ready_seen = True
                    if options.close_master and master is not None:
                        # m42 case 5: take the tty away.  The child
                        # ignores SIGHUP, so it survives; the slave read
                        # then fails with EIO -> the close-terminal
                        # result -2.
                        os.close(master)
                        master = None
                    if options.input_bytes and master is not None:
                        # Deliver the bytes raw, so the line discipline
                        # cannot eat a quit byte (see deliver_raw).  A
                        # failed clear is a harness gap, not a product bug:
                        # route it to an environment-gated INFO skip, never
                        # a FAIL.
                        raw_reason = deliver_raw(master)
                        if raw_reason is not None:
                            return SessionResult(error=("INFO",
                                    "ISIG clear on the pty failed: %s" % raw_reason))
                        os.write(master, options.input_bytes)
                    if options.resize and master is not None:
                        # M53 imp-3 step (e): resize the pty AFTER READY and
                        # BEFORE the gate, so the child reads the new size
                        # -- a live resize (brief.org section 4(e)).
                        try:
                            resize_pty(master, *options.resize)
                        except (OSError, termios.error):
                            pass
                    os.write(gate_fd, b"G")
                    input_sent = True
                # The result is complete once its line arrives.  Do not
                # require Emacs shutdown or pipe EOF after a valid report;
                # cleanup below will stop a child that remains alive.
                # A wait_exit case (M53 imp-3 step (f)) keeps reading until
                # the child exits, so the driver can assert its status.
                if ready_seen and is_complete(report, pty_output):
                    report_done = True
                    if not options.wait_exit:
                        break
            elif child.poll() is not None:
                break
        # Read the pty mode back after the run, while the master is still
        # open (a capture_mode case keeps it open past EOF).  Emacs
        # restores the mode it saved at startup on exit.
        if options.capture_mode and master is not None:
            try:
                mode_after = termios.tcgetattr(master)
            except (OSError, termios.error):
                mode_after = None
        # M53 imp-3 step (f): wait for the real exit status.
        if options.wait_exit and report_done:
            try:
                exit_status = child.wait(
                    timeout=max(0.0, deadline - time.monotonic()))
            except subprocess.TimeoutExpired:
                exit_status = None
        # M54 imp-3: read the termscript file before cleanup unlinks it.
        # The probe closes the termscript before it reports, so the file
        # is complete by the time the report arrives.
        if options.termscript and report_done:
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
        return SessionResult(error=("FAIL", "tty i/o error: errno %d %s" % (err.errno, err.strerror)))
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
            if path is None:
                continue
            try:
                os.unlink(path)
            except OSError:
                pass


    return SessionResult(report=report, output=pty_output, ready_seen=ready_seen,
                         input_sent=input_sent, timed_out=timed_out,
                         mode_before=mode_before, mode_after=mode_after,
                         exit_status=exit_status, termscript=ts_bytes)
