#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "Usage: $0 <crate> [--features <f>] [--release] [--bin <name>] [-- <extra cargo args>]"
  echo ""
  echo "Build a Verus crate using cargo-verus build."
  echo ""
  echo "  <crate>              Crate directory name (e.g. verus-gui)"
  echo "  --features, -f <f>   Cargo features to enable"
  echo "  --release, -r        Build in release mode"
  echo "  --bin <name>         Build a specific binary target"
  echo "  -- <args>            Extra args passed to cargo build"
  echo ""
  echo "If --bin is not specified and src/bin/ exists, the first binary is auto-discovered."
  echo ""
  echo "Examples:"
  echo "  $0 verus-gui"
  echo "  $0 verus-gui --release"
  echo "  $0 verus-gui --features vulkan"
  echo "  $0 verus-mandelbrot --features viewer"
  echo "  $0 verus-gui -- --target x86_64-unknown-linux-gnu"
  exit 1
}

[[ $# -lt 1 ]] && usage

CRATE="$1"; shift
FEATURES=""
RELEASE=false
BIN_NAME=""
EXTRA_ARGS=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --features|-f) FEATURES="$2"; shift 2 ;;
    --release|-r)  RELEASE=true; shift ;;
    --bin)         BIN_NAME="$2"; shift 2 ;;
    -h|--help)     usage ;;
    --)            shift; EXTRA_ARGS=("$@"); break ;;
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

# Build command: Verus-relevant args (--features, --release) MUST come before
# Verus-irrelevant args (--bin) for cargo-verus to handle them correctly.
CMD=("$CARGO_VERUS" build --manifest-path Cargo.toml -p "$CRATE")
[[ -n "$FEATURES" ]] && CMD+=(--features "$FEATURES")
$RELEASE && CMD+=(--release)
[[ -n "$BIN_NAME" ]] && CMD+=(--bin "$BIN_NAME")
[[ ${#EXTRA_ARGS[@]} -gt 0 ]] && CMD+=("${EXTRA_ARGS[@]}")

exec "${CMD[@]}"
