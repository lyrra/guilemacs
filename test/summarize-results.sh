#!/bin/bash
# Summarize test results

echo "=========================================="
echo "RUN AND SUMMARIZE ALL TEST SUITES"
echo "=========================================="
echo ""

# Run tests and capture output
(./src/emacs -Q --batch -l test/run-all-tests.el 2>&1) | tee _testlog
OUTPUT=$(cat _testlog | grep "TEST")

# Count results (exclude suite summaries)
TOTAL_PASS=$(echo "$OUTPUT" | grep " PASS$" | grep -v "TEST-SUITE-END" | wc -l)
TOTAL_FAIL=$(echo "$OUTPUT" | grep " FAIL" | grep -v "TEST-SUITE-END" | wc -l)
TOTAL_XFAIL=$(echo "$OUTPUT" | grep " XFAIL" | grep -v "TEST-SUITE-END" | wc -l)
TOTAL_XPASS=$(echo "$OUTPUT" | grep " XPASS" | grep -v "TEST-SUITE-END" | wc -l)
SUITE_COUNT=$(echo "$OUTPUT" | grep -c "TEST-SUITE-END")

echo "Test Suites: $SUITE_COUNT"
echo "Total Tests: $((TOTAL_PASS + TOTAL_FAIL + TOTAL_XFAIL + TOTAL_XPASS))"
echo "Passed: $TOTAL_PASS"
echo "Failed: $TOTAL_FAIL"
echo "Expected Failures (XFAIL): $TOTAL_XFAIL"
echo "Unexpected Passes (XPASS): $TOTAL_XPASS"
echo ""

# Show suite summaries
echo "Suite Breakdown:"
echo "$OUTPUT" | grep "TEST-SUITE-END" | sed 's/TEST-SUITE-END /  /'
echo ""

# Show any failures
FAILURES=$(echo "$OUTPUT" | grep " FAIL" | grep -v "TEST-SUITE-END")
if [ -n "$FAILURES" ]; then
    echo "FAILURES:"
    echo "$FAILURES"
    echo ""
fi

# Show any expected failures (informational)
XFAILS=$(echo "$OUTPUT" | grep " XFAIL" | grep -v "TEST-SUITE-END")
if [ -n "$XFAILS" ]; then
    echo "EXPECTED FAILURES (known bugs):"
    echo "$XFAILS"
    echo ""
fi

# Show any unexpected passes
XPASSES=$(echo "$OUTPUT" | grep " XPASS" | grep -v "TEST-SUITE-END")
if [ -n "$XPASSES" ]; then
    echo "UNEXPECTED PASSES (bugs may be fixed!):"
    echo "$XPASSES"
    echo ""
fi

# Final status
if [ -n "$FAILURES" ]; then
    echo "❌ SOME TESTS FAILED"
elif [ -n "$XPASSES" ]; then
    echo "⚠️  ALL TESTS PASSED (but some known bugs may be fixed - review XPASS)"
else
    echo "✅ ALL TESTS PASSED!"
fi

echo ""
echo "=========================================="
