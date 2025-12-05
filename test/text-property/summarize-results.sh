#!/bin/bash
# Summarize test results

echo "=========================================="
echo "TEXT PROPERTIES TEST SUMMARY"
echo "=========================================="
echo ""

# Run tests and capture output
OUTPUT=$(./src/emacs -Q --batch -l test/text-property/run-all-tests.el 2>&1 | grep "TEST")

# Count results (exclude suite summaries)
TOTAL_PASS=$(echo "$OUTPUT" | grep " PASS$" | grep -v "TEST-SUITE-END" | wc -l)
TOTAL_FAIL=$(echo "$OUTPUT" | grep " FAIL" | grep -v "TEST-SUITE-END" | wc -l)
SUITE_COUNT=$(echo "$OUTPUT" | grep -c "TEST-SUITE-END")

echo "Test Suites: $SUITE_COUNT"
echo "Total Tests: $((TOTAL_PASS + TOTAL_FAIL))"
echo "Passed: $TOTAL_PASS"
echo "Failed: $TOTAL_FAIL"
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
else
    echo "✅ ALL TESTS PASSED!"
fi

echo ""
echo "=========================================="
