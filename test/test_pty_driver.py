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

import pty_cases
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


    def test_newline_count_check_refuses_a_run_that_did_not_happen(self):
        # The m61-imp3 newline cases send the frame line count as a marker
        # and the span must then hold that many newline bytes, so a run
        # that never happened can not pass on the crossing count alone.
        case = {"name": "newline", "probe": "", "expect": "ok",
                "span_requires": {"span": (b"BEGIN", b"END"),
                                  "newline_count_re": r"M61-IMP3-N=(\d+)\|"}}
        result = SessionResult(report=b'"ok"\n',
                               output=b"M61-IMP3-N=4|BEGIN\n\n\n\nEND",
                               ready_seen=True, input_sent=True)
        with mock.patch.object(driver, "run_session", return_value=result):
            self.assertEqual(driver.run_case(case, "emacs", 1)[:2],
                             (case["name"], "PASS"))
            # Fewer newlines than the marker names: the branch did not run.
            result.output = b"M61-IMP3-N=4|BEGIN\nEND"
            self.assertEqual(driver.run_case(case, "emacs", 1)[1], "FAIL")
            # No line-count marker at all: the count can not be checked.
            result.output = b"BEGIN\nEND"
            self.assertEqual(driver.run_case(case, "emacs", 1)[1], "FAIL")


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


class TerminfoFixtureTests(unittest.TestCase):
    def test_fixture_queries_use_each_private_entry(self):
        xterm = pty_cases.terminfo_fixture("xterm")
        ansi = pty_cases.terminfo_fixture("ansi")
        delete = pty_cases.terminfo_fixture("m52-imp8")
        if xterm is None or ansi is None or delete is None:
            self.skipTest("tic unavailable or fixture compilation failed")
        self.assertEqual(driver.terminfo_capability("xterm", "sitm", xterm), b"\x1b[3m")
        self.assertIsNone(driver.terminfo_capability("ansi", "sitm", ansi))
        self.assertIsNone(driver.terminfo_capability("ansi", "smcup", ansi))
        self.assertEqual(driver.terminfo_capability("m52-imp8", "smdc", delete),
                         b"\x1b[4h")
        self.assertEqual(driver.terminfo_capability("m52-imp8", "rmdc", delete),
                         b"\x1b[4l")
        self.assertEqual(driver.terminfo_capability("xterm", "ht", xterm), b"\t")

    def test_missing_tic_skips_only_fixture_case(self):
        case = next(c for c in pty_cases.CASES if c["name"] == "m52-imp8/policy-key-e2e")
        with mock.patch.object(pty_cases, "_fixture_tried", False), \
             mock.patch.object(pty_cases, "_fixture_dir", None), \
             mock.patch.object(pty_cases.shutil, "which", return_value=None), \
             mock.patch.object(driver, "run_session") as session:
            name, kind, detail = driver.run_case(case, "emacs", 1)
        self.assertEqual((name, kind), (case["name"], "INFO"))
        self.assertIn("no terminfo fixture", detail)
        session.assert_not_called()

    def test_fixture_compile_failure_is_a_skip(self):
        case = next(c for c in pty_cases.CASES if c["name"] == "m52-imp8/policy-key-e2e")
        with mock.patch.object(pty_cases, "_fixture_tried", False), \
             mock.patch.object(pty_cases, "_fixture_dir", None), \
             mock.patch.object(pty_cases.shutil, "which", return_value="tic"), \
             mock.patch.object(pty_cases.subprocess, "run",
                               return_value=subprocess.CompletedProcess([], 1)), \
             mock.patch.object(driver, "run_session") as session:
            _, kind, detail = driver.run_case(case, "emacs", 1)
        self.assertEqual(kind, "INFO")
        self.assertIn("compilation failed", detail)
        session.assert_not_called()


if __name__ == "__main__":
    unittest.main()
