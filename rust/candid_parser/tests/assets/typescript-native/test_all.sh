#! /bin/bash

# Define the list of files to skip
SKIP_FILES=("bad_comment" "bad_import" "bad_import2" "bad_import3" "collision_fields" "collision_fields2" "comment" "invalid_cyclic" "not_func" "not_serv" "oneway" "surrogate" "underline")
# Function to check if a file should be skipped
should_skip() {
    local filename="$1"
    for skip_file in "${SKIP_FILES[@]}"; do
        if [[ "$filename" == "$skip_file" ]]; then
            return 0  # True, should skip
        fi
    done
    return 1  # False, should not skip
}

# If a specific test case is provided, run just that test

echo "Running all valid tests from assets directory"

# Get the path to the assets directory
ASSETS_DIR="../"
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Track test results
PASSED=0
FAILED=0
SKIPPED=0

# Iterate over all .did files in the assets directory
FAILED_TESTS=()

for did_file in "$ASSETS_DIR"/*.did; do
    # Extract the base filename without extension
    filename=$(basename "$did_file" .did)
    
    # Check if this file should be skipped
    if should_skip "$filename"; then
        echo "Skipping test for $filename (known invalid file)"
        SKIPPED=$((SKIPPED + 1))
        continue
    fi
    
    echo "Running test for $filename"
    
    # Run the test for this file
    "$SCRIPT_DIR/test.sh" "$ASSETS_DIR/$filename.did"
    
    if [ $? -eq 0 ]; then
        echo "✅ Test passed: $filename"
        PASSED=$((PASSED + 1))
    else
        echo "❌ Test failed: $filename"
        FAILED=$((FAILED + 1))
        FAILED_TESTS+=("$filename")
    fi
done

echo "Test summary: $PASSED passed, $FAILED failed, $SKIPPED skipped"

# List the tests that didn't pass
if [ ${#FAILED_TESTS[@]} -gt 0 ]; then
    echo "Failed tests:"
    for test in "${FAILED_TESTS[@]}"; do
        echo "  - $test"
    done
fi