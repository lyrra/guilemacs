"""Behavior tests for PTY case verdicts."""

import importlib.util
import contextlib
import io
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest import mock

from pty_session import SessionResult


spec = importlib.util.spec_from_file_location(
    "pty_driver", Path(__file__).with_name("pty-driver.py"))
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)


class CaseVerdictTests(unittest.TestCase):
    def test_termscript_must_match_terminal_output(self):
        case = {"name": "copy", "probe": "", "expect": "5",
                "termscript": True, "output_span": (b"BEGIN", b"END")}
        result = SessionResult(report=b'"5"\n', output=b"BEGINbytesEND",
                               ready_seen=True, input_sent=True, termscript=b"bytes")
        with mock.patch.object(driver, "run_session", return_value=result):
            self.assertEqual(driver.run_case(case, "emacs", 1)[1], "PASS")
            result.termscript = b"wrong"
            self.assertEqual(driver.run_case(case, "emacs", 1)[1], "FAIL")
            result.termscript = None
            self.assertEqual(driver.run_case(case, "emacs", 1)[1], "FAIL")

    def test_required_byte_is_scoped_to_span(self):
        case = {"name": "span", "probe": "", "expect": "ok",
                "span_requires": {"span": (b"BEGIN", b"END"),
                                  "needles": (b"X",)}}
        result = SessionResult(report=b'"ok"\n', output=b"XBEGINEND",
                               ready_seen=True, input_sent=True)
        with mock.patch.object(driver, "run_session", return_value=result):
            self.assertEqual(driver.run_case(case, "emacs", 1)[1], "FAIL")
            result.output = b"BEGINXEND"
            self.assertEqual(driver.run_case(case, "emacs", 1)[1], "PASS")


class DriverStatusTests(unittest.TestCase):
    def test_case_results_control_status_and_all_are_reported(self):
        cases = [{"name": "first"}, {"name": "second"}, {"name": "third"}]
        for results, expected_status in (
                ([("first", "PASS", None), ("second", "INFO", "unavailable"),
                  ("third", "PASS", None)], 0),
                ([("first", "PASS", None), ("second", "FAIL", "bad result"),
                  ("third", "INFO", "unavailable")], 1),
                ([("first", "INFO", "unavailable"), ("second", "INFO", "unavailable"),
                  ("third", "INFO", "unavailable")], 0)):
            with self.subTest(results=results):
                output = io.StringIO()
                with mock.patch.object(driver, "group_cases", return_value=cases), \
                     mock.patch.object(driver.os, "openpty", side_effect=os.pipe), \
                     mock.patch.object(driver, "run_case", side_effect=results), \
                     contextlib.redirect_stdout(output):
                    status = driver.main(["--emacs", sys.executable])
                self.assertEqual(status, expected_status)
                self.assertEqual(len(output.getvalue().splitlines()), 3)
                for name, kind, _ in results:
                    self.assertIn("%s %s" % (kind, name), output.getvalue())

    def test_missing_pty_is_a_successful_skip(self):
        output = io.StringIO()
        with mock.patch.object(driver, "group_cases", return_value=[{"name": "case"}]), \
             mock.patch.object(driver.os, "openpty", side_effect=OSError(13, "denied")), \
             contextlib.redirect_stdout(output):
            status = driver.main(["--emacs", sys.executable])
        self.assertEqual(status, 0)
        self.assertIn("INFO case skipped (no pty:", output.getvalue())

    def test_command_returns_failure_when_child_cannot_start(self):
        try:
            master, slave = os.openpty()
        except OSError as err:
            self.skipTest("no PTY: %s" % err)
        os.close(master)
        os.close(slave)
        result = subprocess.run(
            [sys.executable, str(Path(driver.__file__)), "--emacs", sys.executable,
             "--case", "m42-imp3/case-1-no-input", "--timeout", "5"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=10)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("FAIL m42-imp3/case-1-no-input", result.stdout)

    def test_command_returns_success_for_missing_emacs_skip(self):
        result = subprocess.run(
            [sys.executable, str(Path(driver.__file__)), "--emacs", "/no-such-emacs",
             "--case", "m42-imp3/case-1-no-input"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("INFO m42-imp3/case-1-no-input skipped", result.stdout)


if __name__ == "__main__":
    unittest.main()
