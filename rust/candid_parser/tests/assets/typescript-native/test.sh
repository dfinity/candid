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

CANDID_NAME=$(basename $1 .did)
# Create a temporary directory
TEMP_DIR="./tmp/$CANDID_NAME"
if [ -d "$TEMP_DIR" ]; then
    rm -rf $TEMP_DIR
fi
mkdir -p $TEMP_DIR
echo "Created temporary directory: $TEMP_DIR"

# extract the file name from the path

cp $1 $TEMP_DIR/$CANDID_NAME.did

if [ ! -f "$1.did" ]; then
    echo "Candid file `<test_case>/$1.did` does not exist"
fi


cargo run --package caffeine-stub -- bind --target ts-native-interface $TEMP_DIR/$CANDID_NAME.did > ${TEMP_DIR}/$CANDID_NAME.d.ts
cargo run --package caffeine-stub -- bind --target ts-native-wrapper $TEMP_DIR/$CANDID_NAME.did > ${TEMP_DIR}/$CANDID_NAME.ts

mkdir -p ${TEMP_DIR}/declarations/$CANDID_NAME
cargo run --package caffeine-stub -- bind --target ts $TEMP_DIR/$CANDID_NAME.did > ${TEMP_DIR}/declarations/$CANDID_NAME/$CANDID_NAME.did.d.ts
cargo run --package caffeine-stub -- bind --target js $TEMP_DIR/$CANDID_NAME.did > ${TEMP_DIR}/declarations/$CANDID_NAME/$CANDID_NAME.did.js


export_code="export const $CANDID_NAME = canisterId ? createActor(canisterId) : undefined;"
awk '// {gsub("{{canister_name}}", "'$CANDID_NAME'"); gsub("{{canister_name_ident}}", "'$CANDID_NAME'"); print }' "./templates/index.d.ts.hbs" > ${TEMP_DIR}/declarations/$CANDID_NAME/index.d.ts
awk -v export_str="$export_code" '// {gsub("{{canister_name}}", "'$CANDID_NAME'"); gsub("{{{canister_name_process_env}}}", "process.env.'$CANDID_NAME'"); gsub("{{{actor_export}}}", export_str);  print }' "./templates/index.js.hbs" > ${TEMP_DIR}/declarations/$CANDID_NAME/index.js

cp ./templates/package.json ${TEMP_DIR}/package.json
cp ./templates/tsconfig.json ${TEMP_DIR}/tsconfig.json
cp ./templates/env.json ${TEMP_DIR}/env.json
cd ${TEMP_DIR}
npm install
npm run build

if [ $? != 0 ]; then
    echo "Test failed: $CANDID_NAME"
    cleanup 1
fi

echo "Test passed: $CANDID_NAME"
cleanup 0