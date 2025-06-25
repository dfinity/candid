#!/bin/bash

#############################################
# USAGE                                     #
#############################################

function title() {
  echo "Build script for the rust and js code"
}

function usage() {
  cat <<EOF

Usage:
  $0

Options:
  --target <target>  The target to build for, default is "web"
  --mode <mode>      The build mode, default is "production"
  --dir <dir>        The build directory, default is "./dist"
EOF
}

function help() {
  cat <<EOF

Helper script to build the library for the specified target.

NOTE: This requires a working rust toolchain and nodejs to operate correctly.
EOF
}

#############################################
# VARS                                      #
#############################################

PACKAGE_ROOT=$(pwd)
LIBRARY_NAME="didc"
BUILD_DIR=${BUILD_DIR:-./dist}
BUILD_TARGET=${BUILD_TARGET:-web}
BUILD_MODE=${NODE_ENV:-production}

#############################################
# SCRIPT OPTIONS                            #
#############################################

while [[ $# -gt 0 ]]; do
  case "$1" in
  -h | --help)
    title
    usage
    help
    exit 0
    ;;
  --target)
    shift
    if [[ $# -eq 0 ]]; then
      echo "ERROR: No target provided"
      exit 1
    fi
    BUILD_TARGET=$1
    shift # removes the argument
    echo
    ;;
  --mode)
    shift
    if [[ $# -eq 0 ]]; then
      echo "ERROR: No build mode provided"
      exit 1
    fi
    BUILD_MODE=$1
    shift # removes the argument
    echo
    ;;
  --dir)
    shift
    if [[ $# -eq 0 ]]; then
      echo "ERROR: No build directory provided"
      exit 1
    fi
    BUILD_DIR=$1
    shift # removes the argument
    echo
    ;;
  *)
    echo "ERROR: unknown argument $1"
    usage
    echo
    echo "Use '$0 --help' for more information"
    exit 1
    ;;
  esac
done

#############################################
# UTILS                                     #
#############################################

early_exit() {
  echo "Performing early exit..."

  exit 1
}

#############################################
# BUILDING                                  #
#############################################

RUST_BUILD_MODE="--dev"
if [[ "$BUILD_MODE" == "production" ]]; then
  RUST_BUILD_MODE="--release"
fi

OUT_DIR="$BUILD_DIR/$BUILD_TARGET"

rm -rf $OUT_DIR

if [[ "$BUILD_TARGET" == "nodejs" ]]; then
  echo "Building the library for node..."

  ./node_modules/wasm-pack/run.js build --target $BUILD_TARGET --out-name $LIBRARY_NAME --out-dir $OUT_DIR $RUST_BUILD_MODE --no-pack
else
  echo "Building the library for the web..."

  ./node_modules/wasm-pack/run.js build --target bundler --out-name $LIBRARY_NAME --out-dir $OUT_DIR $RUST_BUILD_MODE --no-pack
fi
