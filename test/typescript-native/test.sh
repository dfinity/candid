#!/usr/bin/env bash

# Usage: test.sh <test_case>

# Define cleanup function for exit
cleanup() {
    
    # Return to original directory if we changed
    if [ -n "$ORIGINAL_DIR" ]; then
        cd "$ORIGINAL_DIR" || true
    fi
    
    # # Remove temporary directory
    # if [ -n "$TEMP_DIR" ] && [ -d "$TEMP_DIR" ]; then
    #     rm -rf "$TEMP_DIR"
    # fi
    
    exit $1
}

# Handle script interruption
trap 'cleanup 1' INT TERM

# Check arguments
if [ -z "$1" ]; then
    echo "Usage: test.sh <test_case>"
    cleanup 1
fi

# Store original directory
ORIGINAL_DIR=$(pwd)


# Create a temporary directory
TEMP_DIR="./tmp/$1"
if [ -d "$TEMP_DIR" ]; then
    rm -rf $TEMP_DIR
fi
mkdir -p $TEMP_DIR
echo "Created temporary directory: $TEMP_DIR"
cp $1.did $TEMP_DIR/$1.did

if [ ! -f "$1.did" ]; then
    echo "Candid file `<test_case>/$1.did` does not exist"
fi


cargo run --package didc -- bind --target ts-native-interface $1.did > ${TEMP_DIR}/$1.d.ts
cargo run --package didc -- bind --target ts-native-wrapper $1.did > ${TEMP_DIR}/$1.ts

mkdir -p ${TEMP_DIR}/declarations/$1
cargo run --package didc -- bind --target ts $1.did > ${TEMP_DIR}/declarations/$1/$1.did.d.ts
cargo run --package didc -- bind --target js $1.did > ${TEMP_DIR}/declarations/$1/$1.did.js


export_code="export const $1 = canisterId ? createActor(canisterId) : undefined;"
awk '// {gsub("{{canister_name}}", "'$1'"); gsub("{{canister_name_ident}}", "'$1'"); print }' "./templates/index.d.ts.hbs" > ${TEMP_DIR}/declarations/$1/index.d.ts
awk -v export_str="$export_code" '// {gsub("{{canister_name}}", "'$1'"); gsub("{{{canister_name_process_env}}}", "process.env.'$1'"); gsub("{{{actor_export}}}", export_str);  print }' "./templates/index.js.hbs" > ${TEMP_DIR}/declarations/$1/index.js

cp ./templates/package.json ${TEMP_DIR}/package.json
cp ./templates/tsconfig.json ${TEMP_DIR}/tsconfig.json
cd ${TEMP_DIR}
npm install
npm run build

if [ $? != 0 ]; then
    echo "Test failed: $1"
    cleanup 1
fi

echo "Test passed: $1"
cleanup 0