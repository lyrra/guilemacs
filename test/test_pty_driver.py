"""Behavior tests for PTY case verdicts."""

import importlib.util
import contextlib
import io
import os
import re
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


class M62Imp1bTimeGapTests(unittest.TestCase):
    """The pure helpers of the padded-order case (M62 imp-1b)."""

    def test_largest_gap_counts_the_chunk_that_covers_the_span_start(self):
        # The mark of the case and the bytes of the run can arrive in ONE
        # chunk, so the chunk that starts before the span still counts.
        marks = [(0, 10.0), (6, 10.05), (20, 10.10), (40, 10.101)]
        self.assertAlmostEqual(driver.largest_gap(marks, 8, 39), 0.05)
        # A span that arrived as ONE chunk has no gap at all.  None is not
        # a gap of 0 seconds: the caller must not read it as a pass.
        self.assertIsNone(driver.largest_gap([(0, 10.0), (40, 10.06)], 8, 39))
        self.assertIsNone(driver.largest_gap([], 8, 39))
        self.assertIsNone(driver.largest_gap(None, 8, 39))

    def test_pad_marker_reads_every_marker_form(self):
        self.assertEqual(driver.pad_marker_seconds(b"\x1b[K$<50/>"), 0.05)
        self.assertEqual(driver.pad_marker_seconds(b"\x1b[K$<50>"), 0.05)
        self.assertEqual(driver.pad_marker_seconds(b"$<2.5*>"), 0.0025)
        self.assertIsNone(driver.pad_marker_seconds(b"\x1b[K"))
        self.assertIsNone(driver.pad_marker_seconds(b""))

    def test_the_case_takes_its_padding_from_the_fixture_entry(self):
        # The case holds no 50 ms of its own: the value must come from the
        # entry, so a host with another declared padding is measured on its
        # own value.
        case = next(c for c in pty_cases.CASES
                    if c["name"] == "m62-imp1b/padded-order-e2e")
        spec = case["time_gap"]
        self.assertEqual(spec["capability"], "el")
        self.assertNotIn("padding", spec)
        self.assertTrue(case["time_marks"])

    def test_the_order_holds_when_the_run_bytes_precede_the_sleep(self):
        # The fixed shape: BEGIN and the run bytes ESC [ K reach the pty at
        # ~t0, then the 50 ms sleep of the marker runs, then END arrives.
        case = {"name": "gap", "env": {"TERM": "xterm"},
                "time_gap": {"span": (b"B", b"E"), "capability": "el"}}
        marks = [(0, 10.0), (4, 10.050)]
        gap_before, gap_after = driver.order_gaps(marks, 1, 7, 1, 4)
        self.assertAlmostEqual(gap_before, 0.0)
        self.assertAlmostEqual(gap_after, 0.050)
        with mock.patch.object(driver, "terminfo_capability",
                               return_value=b"\x1b[K$<50/>"):
            self.assertIsNone(driver.time_gap_problem(
                case, b"B\x1b[KxyzE", marks))
        # A burst inside 1 chunk can not prove an order, so it is a FAIL
        # and never a pass.
        with mock.patch.object(driver, "terminfo_capability",
                               return_value=b"\x1b[K$<50/>"):
            problem = driver.time_gap_problem(
                case, b"B\x1b[KxyzE", [(0, 10.0), (1, 10.050)])
        self.assertEqual(problem[0], "FAIL")
        self.assertIn("fewer than 2 chunks", problem[1])

    def test_the_order_fails_when_the_run_bytes_follow_the_sleep(self):
        # The collecting shape: the whole burst leaves at the flush point,
        # so the run bytes and END arrive together and no sleep follows
        # them.  The largest gap of the span proves nothing here; only
        # gap_after names the defect.
        case = {"name": "gap", "env": {"TERM": "xterm"},
                "time_gap": {"span": (b"B", b"E"), "capability": "el"}}
        with mock.patch.object(driver, "terminfo_capability",
                               return_value=b"\x1b[K$<50/>"):
            problem = driver.time_gap_problem(
                case, b"B\x1b[KxyzE", [(0, 10.0), (4, 10.0001)])
        self.assertEqual(problem[0], "FAIL")
        self.assertIn("gap_after", problem[1])
        # The false pass that the LARGEST gap gives: the 60 ms sleep sits
        # BETWEEN the span start and the run bytes, so the span holds a gap
        # of 60 ms and the old form passed.  The sub-gap form names
        # gap_before, because the run bytes did not arrive before it.
        marks = [(0, 10.0), (3, 10.06), (6, 10.16)]
        self.assertAlmostEqual(driver.largest_gap(marks, 1, 7), 0.10)
        with mock.patch.object(driver, "terminfo_capability",
                               return_value=b"\x1b[K$<50/>"):
            problem = driver.time_gap_problem(case, b"Bxy\x1b[KzE", marks)
        self.assertEqual(problem[0], "FAIL")
        self.assertIn("gap_before", problem[1])

    def test_time_gap_refuses_a_span_that_holds_no_run(self):
        case = {"name": "gap", "env": {"TERM": "xterm"},
                "time_gap": {"span": (b"B", b"E"), "capability": "el"}}
        with mock.patch.object(driver, "terminfo_capability",
                               return_value=b"\x1b[K$<50/>"):
            # The run is absent: a gap would prove nothing.
            problem = driver.time_gap_problem(
                case, b"BxxE", [(0, 1.0), (3, 1.05)])
            self.assertEqual(problem[0], "FAIL")
            # The run is there and one chunk holds its start: the gap is
            # below the declared padding, so the order is wrong.
            problem = driver.time_gap_problem(
                case, b"B\x1b[KxE", [(0, 1.0), (4, 1.001)])
            self.assertEqual(problem[0], "FAIL")
            self.assertIn("0.0010", problem[1])
            # The order holds.
            self.assertIsNone(driver.time_gap_problem(
                case, b"B\x1b[KxE", [(0, 1.0), (4, 1.051)]))
            # A span that arrived as ONE chunk holds no gap, so the case
            # can not pass.
            problem = driver.time_gap_problem(
                case, b"B\x1b[KxE", [(0, 1.0)])
            self.assertEqual(problem[0], "FAIL")
            # No time marks at all: the case asked for a gap it can not
            # measure.
            problem = driver.time_gap_problem(case, b"B\x1b[KxE", None)
            self.assertEqual(problem[0], "FAIL")

    def test_time_gap_without_the_capability_is_an_info_skip(self):
        # A host whose entry holds no el can not pad, so the case reports
        # its own skip and never a pass.  The detail carries the group's
        # prefix, so the line is readable next to a probe skip.
        case = next(c for c in pty_cases.CASES
                    if c["name"] == "m62-imp1b/padded-order-e2e")
        with mock.patch.object(driver, "terminfo_capability", return_value=None):
            problem = driver.time_gap_problem(case, b"", None)
        self.assertEqual(problem[0], "INFO")
        self.assertTrue(problem[1].startswith(pty_cases.M62_IMP1B_SKIP),
                        problem[1])

    def test_an_info_time_gap_is_a_skip_that_exits_zero(self):
        # The driver path of that answer: an INFO line, its own prefix, and
        # exit status 0.  A FAIL is the only status that exits 1.
        case = next(c for c in pty_cases.CASES
                    if c["name"] == "m62-imp1b/padded-order-e2e")
        with mock.patch.object(driver, "terminfo_capability", return_value=None):
            result = (case["name"],) + driver.time_gap_problem(case, b"", None)
        output = io.StringIO()
        with mock.patch.object(driver, "group_cases", return_value=[case]), \
             mock.patch.object(driver.os, "openpty", side_effect=os.pipe), \
             mock.patch.object(driver, "run_case", return_value=result), \
             contextlib.redirect_stdout(output):
            status = driver.main(["--emacs", sys.executable])
        self.assertEqual(status, 0)
        self.assertIn("INFO %s skipped (%s" % (case["name"], pty_cases.M62_IMP1B_SKIP),
                      output.getvalue())


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


class M62Imp2ContractTests(unittest.TestCase):
    """The pty-free contracts of the M62 imp-2 group (the space run)."""

    def _case(self, name):
        return next(c for c in pty_cases.CASES if c["name"] == name)

    def test_space_run_width_follows_the_pinned_frame(self):
        # The run is FrameCols - 1 - cursorX bytes, and cursorX is 0 after
        # cmgoto (row, 0).  The case pins FrameCols through COLUMNS, so the
        # needle length MUST equal COLUMNS - 1 and not a magic 79.
        case = self._case("m62-imp2/space-run-bytes-e2e")
        cols = int(case["env"]["COLUMNS"])
        self.assertEqual(len(pty_cases.M62_IMP2_SPACES), cols - 1)

    def test_count_window_holds_the_act_and_refuses_the_control(self):
        case = self._case("m62-imp2/space-run-count-e2e")
        subst = case["subst"]
        lo, hi = int(subst["MIN_S2C"]), int(subst["MAX_S2C"])
        clo, chi = int(subst["MIN_C2S"]), int(subst["MAX_C2S"])
        act = pty_cases.M62_IMP2_ACT_PAIR
        control = pty_cases.M62_IMP2_CONTROL_PAIR
        self.assertLessEqual(lo, act[0])
        self.assertLessEqual(act[0], hi)
        self.assertLessEqual(clo, act[1])
        self.assertLessEqual(act[1], chi)
        self.assertLess(control[0], lo)
        self.assertLess(control[1], clo)

    def test_every_case_pins_the_fixture_and_the_size(self):
        for case in pty_cases.CASES:
            if case["group"] != "m62-imp2":
                continue
            self.assertEqual(case["terminfo_fixture"], pty_cases.M62_IMP2_TERM)
            self.assertEqual(case["env"]["TERM"], pty_cases.M62_IMP2_TERM)
            # An inherited COLUMNS/LINES of the host would override the
            # entry through ncurses setupterm, so each case pins both.
            self.assertEqual(case["env"]["COLUMNS"], "80")
            self.assertEqual(case["env"]["LINES"], "24")


class M62Imp4ContractTests(unittest.TestCase):
    """The pty-free contracts of the M62 imp-4 group (the 2nd writer)."""

    def _case(self, name):
        return next(c for c in pty_cases.CASES if c["name"] == name)

    def test_the_group_holds_the_3_declared_cases(self):
        names = [c["name"] for c in pty_cases.CASES
                 if c["group"] == "m62-imp4"]
        self.assertEqual(names,
                         ["m62-imp4/m52-leaf-route-e2e",
                          "m62-imp4/termscript-copy-e2e",
                          "m62-imp4/clean-exit-e2e"])

    def test_a_skip_can_not_read_as_a_pass(self):
        # Each case of the group carries the group's OWN skip prefix, so a
        # skip of this group is never read as the skip of another group.
        for case in pty_cases.CASES:
            if case["group"] != "m62-imp4":
                continue
            self.assertEqual(case["info_report_prefix"],
                             pty_cases.M62_IMP4_SKIP)
        prefixes = [c.get("info_report_prefix") for c in pty_cases.CASES
                    if c["group"] != "m62-imp4"]
        self.assertNotIn(pty_cases.M62_IMP4_SKIP, prefixes)

    def test_the_order_case_pins_the_capability_before_the_bytevector(self):
        # A count-only case would pass on either shape, so the order case
        # MUST pin the sequence: the capability bytes first.
        spec = self._case("m62-imp4/m52-leaf-route-e2e")["span_requires"]
        self.assertEqual(spec["needles_in_order"],
                         (pty_cases.M62_IMP4_CAP_BYTES,
                          pty_cases.M62_IMP4_BYTES))

    def test_a_reversed_run_fails_the_order_case(self):
        # The driver must REJECT the reversed order, not accept a mere
        # presence: this is the property the negative control relies on.
        case = dict(self._case("m62-imp4/m52-leaf-route-e2e"))
        cap, vec = (pty_cases.M62_IMP4_CAP_BYTES,
                    pty_cases.M62_IMP4_BYTES)
        begin, end = pty_cases.M62_IMP4_BEGIN, pty_cases.M62_IMP4_END
        result = SessionResult(report=b'"ok"\n',
                               output=begin + cap + vec + end,
                               ready_seen=True, input_sent=True)
        with mock.patch.object(driver, "run_session", return_value=result):
            self.assertEqual(driver.run_case(case, "emacs", 1)[1], "PASS")
            result.output = begin + vec + cap + end
            self.assertEqual(driver.run_case(case, "emacs", 1)[1], "FAIL")

    def test_the_termscript_case_compares_the_file_with_the_span(self):
        # A dropped or shortened copy must FAIL: the case pins the span
        # bytes and asks the driver to read a real termscript file.
        case = self._case("m62-imp4/termscript-copy-e2e")
        self.assertTrue(case["termscript"])
        self.assertEqual(case["output_span_bytes"],
                         pty_cases.M62_IMP4_CAP_BYTES
                         + pty_cases.M62_IMP4_BYTES)
        begin, end = case["output_span"]
        span_bytes = case["output_span_bytes"]
        result = SessionResult(report=b'"%d"\n' % len(span_bytes),
                               output=begin + case["output_span_bytes"] + end,
                               ready_seen=True, input_sent=True,
                               termscript=case["output_span_bytes"])
        with mock.patch.object(driver, "run_session", return_value=result):
            self.assertEqual(driver.run_case(case, "emacs", 1)[1], "PASS")
            result.termscript = span_bytes[:-1]
            self.assertEqual(driver.run_case(case, "emacs", 1)[1], "FAIL")

    def test_count_window_holds_the_act_and_refuses_the_control(self):
        subst = self._case("m62-imp4/m52-leaf-route-e2e")["subst"]
        lo, hi = int(subst["MIN_S2C"]), int(subst["MAX_S2C"])
        clo, chi = int(subst["MIN_C2S"]), int(subst["MAX_C2S"])
        act = pty_cases.M62_IMP4_ACT_PAIR
        control = pty_cases.M62_IMP4_CONTROL_PAIR
        self.assertLessEqual(lo, act[0])
        self.assertLessEqual(act[0], hi)
        self.assertLessEqual(clo, act[1])
        self.assertLessEqual(act[1], chi)
        # The negative control is the raw writer, so it MUST sit outside
        # the window: a window that admits it proves nothing.
        self.assertLess(control[0], lo)
        self.assertLess(control[1], clo)

    def test_every_case_pins_the_fixture_and_the_size(self):
        for case in pty_cases.CASES:
            if case["group"] != "m62-imp4":
                continue
            self.assertEqual(case["env"]["TERM"], pty_cases.M62_IMP4_TERM)
            self.assertEqual(case["env"]["COLUMNS"], "80")
            self.assertEqual(case["env"]["LINES"], "24")

    def test_the_clean_exit_case_waits_for_the_status_and_the_mode(self):
        case = self._case("m62-imp4/clean-exit-e2e")
        self.assertTrue(case["wait_exit"])
        self.assertTrue(case["capture_mode"])

    def test_the_probe_subst_holds_no_unreplaced_field(self):
        # A probe whose @@FIELD@@ stays unreplaced sends a broken form, and
        # the run answers a Scheme error instead of a verdict.
        for case in pty_cases.CASES:
            if case["group"] != "m62-imp4":
                continue
            # TSPATH is supplied by the driver at run time (the temp path
            # of the termscript file), so it is not a case field.
            for field in re.findall(r"@@([A-Z_]+)@@", case["probe"]):
                if field == "TSPATH":
                    continue
                self.assertIn(field, case["subst"], (case["name"], field))


if __name__ == "__main__":
    unittest.main()
