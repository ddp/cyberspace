#!/bin/sh
# Run all Chez Scheme tests
# Usage: cd spki/scheme/chez && tests/run-all.sh

CHEZ="${CHEZ:-/opt/homebrew/bin/chez}"
LIBDIRS="."
PASS=0
FAIL=0
TESTS=""

cd "$(dirname "$0")/.."

for test in tests/test-*.sps; do
    name=$(basename "$test" .sps)
    echo "━━━ $name ━━━"
    if $CHEZ --libdirs "$LIBDIRS" --script "$test" 2>&1; then
        PASS=$((PASS + 1))
    else
        FAIL=$((FAIL + 1))
        TESTS="$TESTS $name"
    fi
    echo ""
done

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Test suites passed: $PASS"
echo "Test suites failed: $FAIL"
if [ $FAIL -gt 0 ]; then
    echo "Failed:$TESTS"
    exit 1
fi
