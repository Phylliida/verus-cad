#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "Usage: $0 <crate> [--features <f>] [--release] [--bin <name>] [-- <binary args>]"
  echo ""
  echo "Build and run a Verus crate. Builds with cargo-verus, then execs the binary."
  echo "(cargo-verus does not have a 'run' subcommand.)"
  echo ""
  echo "  <crate>              Crate directory name (e.g. verus-gui)"
  echo "  --features, -f <f>   Cargo features to enable"
  echo "  --release, -r        Build and run in release mode"
  echo "  --bin <name>         Run a specific binary target"
  echo "  -- <args>            Arguments passed to the binary"
  echo ""
  echo "If --bin is not specified and src/bin/ exists, the first binary is auto-discovered."
  echo "On macOS with Nix, Vulkan/MoltenVK paths are set up automatically."
  echo ""
  echo "Examples:"
  echo "  $0 verus-gui"
  echo "  $0 verus-gui --release"
  echo "  $0 verus-mandelbrot --features viewer"
  echo "  $0 verus-gui -- --width 800 --height 600"
  exit 1
}

[[ $# -lt 1 ]] && usage

CRATE="$1"; shift
FEATURES=""
RELEASE=false
BIN_NAME=""
BIN_ARGS=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --features|-f) FEATURES="$2"; shift 2 ;;
    --release|-r)  RELEASE=true; shift ;;
    --bin)         BIN_NAME="$2"; shift 2 ;;
    -h|--help)     usage ;;
    --)            shift; BIN_ARGS=("$@"); break ;;
    *)             echo "Unknown arg: $1"; usage ;;
  esac
done

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CRATE_DIR="$SCRIPT_DIR/$CRATE"

if [[ ! -d "$CRATE_DIR/src" ]]; then
  echo "Error: crate '$CRATE' not found (no $CRATE_DIR/src/)"
  echo ""
  echo "Available crates:"
  for d in "$SCRIPT_DIR"/verus-*/; do
    [[ -d "$d/src" ]] && echo "  $(basename "$d")"
  done
  exit 1
fi

VERUS_ROOT="${VERUS_ROOT:-$SCRIPT_DIR/verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
CARGO_VERUS="$VERUS_SOURCE/target-verus/release/cargo-verus"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)  TOOLCHAIN="1.93.0-aarch64-apple-darwin" ;;
  Darwin-x86_64) TOOLCHAIN="1.93.0-x86_64-apple-darwin" ;;
  *)             TOOLCHAIN="1.93.0-x86_64-unknown-linux-gnu" ;;
esac

export PATH="$VERUS_SOURCE/target-verus/release:$PATH"
export VERUS_Z3_PATH="$VERUS_SOURCE/z3"
export RUSTUP_TOOLCHAIN="$TOOLCHAIN"

cd "$CRATE_DIR"

# Auto-discover binary target from src/bin/ if --bin not specified
if [[ -z "$BIN_NAME" && -d src/bin ]]; then
  for f in src/bin/*.rs; do
    BIN_NAME="$(basename "$f" .rs)"
    break
  done
fi

# Fall back to crate name if no bin discovered
if [[ -z "$BIN_NAME" ]]; then
  BIN_NAME="$CRATE"
fi

# Determine profile directory
if $RELEASE; then
  PROFILE_DIR="release"
else
  PROFILE_DIR="debug"
fi

# Build: Verus-relevant args (--features, --release) MUST come before
# Verus-irrelevant args (--bin) for cargo-verus.
BUILD_CMD=("$CARGO_VERUS" build --manifest-path Cargo.toml -p "$CRATE")
[[ -n "$FEATURES" ]] && BUILD_CMD+=(--features "$FEATURES")
$RELEASE && BUILD_CMD+=(--release)
BUILD_CMD+=(--bin "$BIN_NAME")

echo "Building $CRATE (bin: $BIN_NAME)..."
"${BUILD_CMD[@]}"

# Find the binary (try underscore-munged name first, then original)
BIN_NAME_US="${BIN_NAME//-/_}"
BIN_PATH="target/$PROFILE_DIR/$BIN_NAME_US"
if [[ ! -f "$BIN_PATH" ]]; then
  BIN_PATH="target/$PROFILE_DIR/$BIN_NAME"
fi
if [[ ! -f "$BIN_PATH" ]]; then
  echo "Binary not found. Available in target/$PROFILE_DIR/:"
  ls "target/$PROFILE_DIR/" | head -20
  exit 1
fi

# On macOS with Nix, set up Vulkan/MoltenVK paths
if [[ "$(uname -s)" == "Darwin" ]]; then
  VK_LIB=$(find /nix/store -name "libvulkan.dylib" 2>/dev/null | head -1)
  if [[ -n "$VK_LIB" ]]; then
    export DYLD_LIBRARY_PATH="$(dirname "$VK_LIB")${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"
  fi
  VK_ICD=$(find /nix/store -name "MoltenVK_icd.json" 2>/dev/null | head -1)
  if [[ -n "$VK_ICD" ]]; then
    export VK_DRIVER_FILES="$VK_ICD"
  fi
fi

exec "$BIN_PATH" "${BIN_ARGS[@]}"
