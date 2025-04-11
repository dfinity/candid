# Define the list of files to skip
SKIP_FILES=("bad_comment" "bad_import" "bad_import2" "bad_import3" "collision_fields" "collisions_fields2" "invalid_cyclic" "not_func" "not_serv" "oneway" "surrogate" "underline")
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

# Check if the assets directory exists
if [ ! -d "$ASSETS_DIR" ]; then
    echo "Error: Assets directory not found at $ASSETS_DIR"
    cleanup 1
fi

# Track test results
PASSED=0
FAILED=0
SKIPPED=0

# Iterate over all .did files in the assets directory
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
    
    # Copy the .did file to the current directory for testing
    cp "$did_file" "$ORIGINAL_DIR/$filename.did"
    
    # Run the test for this file
    "$ORIGINAL_DIR/test.sh" "$filename"
    
    if [ $? -eq 0 ]; then
        echo "✅ Test passed: $filename"
        PASSED=$((PASSED + 1))
    else
        echo "❌ Test failed: $filename"
        FAILED=$((FAILED + 1))
    fi
    
    # Clean up the copied .did file
    rm -f "$ORIGINAL_DIR/$filename.did"
done

echo "Test summary: $PASSED passed, $FAILED failed, $SKIPPED skipped"

if [ $FAILED -gt 0 ]; then
    cleanup 1
else
    cleanup 0
fi