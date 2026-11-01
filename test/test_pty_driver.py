"""Behavior tests for PTY case verdicts."""

import importlib.util
from pathlib import Path
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


if __name__ == "__main__":
    unittest.main()
