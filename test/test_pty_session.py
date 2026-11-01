"""Behavior tests for the PTY session independent of an Emacs build."""

import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import pty_session


CHILD = '''#!/usr/bin/env python3
import fcntl, os, struct, sys, termios, time
mode, gate, pidfile = open(sys.argv[-1]).read().splitlines()
open(pidfile, "w").write(str(os.getpid()))
if mode == "timeout":
    time.sleep(30)
else:
    os.write(2, b"READY\\n")
    with open(gate) as fifo:
        fifo.read(1)
    data = os.read(0, 6)
    rows, cols, _, _ = struct.unpack("HHHH", fcntl.ioctl(0, termios.TIOCGWINSZ, b"\\0" * 8))
    os.write(1, b"OUTPUT:" + data + ("%d,%d" % (rows, cols)).encode())
    time.sleep(0.1)
    os.write(2, b"REPORT\\n")
    time.sleep(30)
'''


class SessionTests(unittest.TestCase):
    def test_input_resize_completion_and_child_cleanup(self):
        with tempfile.TemporaryDirectory() as directory:
            child = Path(directory, "child")
            child.write_text(CHILD)
            child.chmod(0o755)
            pidfile = str(Path(directory, "pid"))
            result = pty_session.run_session(
                str(child), 5,
                pty_session.SessionOptions(input_bytes=b"A\x07BC\n", resize=(30, 100)),
                None, lambda gate: "run\n%s\n%s\n" % (gate, pidfile),
                lambda report, output: b"REPORT\n" in report and b"30,100" in output)
            self.assertIsNone(result.error)
            self.assertTrue(result.ready_seen and result.input_sent)
            self.assertFalse(result.timed_out)
            self.assertIn(b"OUTPUT:A\x07BC", result.output)
            self.assertIn(b"30,100", result.output)
            with self.assertRaises(ProcessLookupError):
                os.kill(int(Path(pidfile).read_text()), 0)

    def test_raw_input_failure_is_a_skip_and_cleans_up(self):
        with tempfile.TemporaryDirectory() as directory:
            child = Path(directory, "child")
            child.write_text(CHILD)
            child.chmod(0o755)
            pidfile = str(Path(directory, "pid"))
            with mock.patch.object(pty_session, "deliver_raw", return_value="test error"):
                result = pty_session.run_session(
                    str(child), 5, pty_session.SessionOptions(input_bytes=b"x"),
                    None, lambda gate: "run\n%s\n%s\n" % (gate, pidfile),
                    lambda report, output: False)
            self.assertEqual(result.error,
                             ("INFO", "ISIG clear on the pty failed: test error"))
            with self.assertRaises(ProcessLookupError):
                os.kill(int(Path(pidfile).read_text()), 0)

    def test_timeout_kills_child(self):
        with tempfile.TemporaryDirectory() as directory:
            child = Path(directory, "child")
            child.write_text(CHILD)
            child.chmod(0o755)
            pidfile = str(Path(directory, "pid"))
            result = pty_session.run_session(
                str(child), 0.5, pty_session.SessionOptions(), None,
                lambda gate: "timeout\n%s\n%s\n" % (gate, pidfile),
                lambda report, output: False)
            self.assertTrue(result.timed_out)
            self.assertFalse(result.ready_seen)
            with self.assertRaises(ProcessLookupError):
                os.kill(int(Path(pidfile).read_text()), 0)

    def test_setup_failure_releases_descriptors_and_file(self):
        with tempfile.TemporaryDirectory() as directory:
            original_openpty = os.openpty
            descriptors = []

            def openpty():
                pair = original_openpty()
                descriptors.extend(pair)
                return pair

            with mock.patch.object(pty_session.os, "openpty", side_effect=openpty), \
                 mock.patch.object(pty_session.os, "mkfifo", side_effect=OSError(5, "failure")), \
                 mock.patch.object(pty_session.tempfile, "tempdir", directory):
                result = pty_session.run_session(
                    "unused", 1, pty_session.SessionOptions(), None,
                    lambda gate: "", lambda report, output: False)
            self.assertEqual(result.error[0], "FAIL")
            self.assertEqual(list(Path(directory).iterdir()), [])
            for fd in descriptors:
                with self.assertRaises(OSError):
                    os.fstat(fd)


if __name__ == "__main__":
    unittest.main()
