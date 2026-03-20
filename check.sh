#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "Usage: $0 <crate> [--module <module>] [--raw]"
  echo ""
  echo "Run Verus verification on a crate."
  echo ""
  echo "  <crate>              Crate directory name (e.g. verus-geometry)"
  echo "  --module, -m <mod>   Verify only this module (file path or module path)"
  echo "  --raw, -r            Show raw compiler output"
  echo ""
  echo "Examples:"
  echo "  $0 verus-geometry"
  echo "  $0 verus-geometry -m runtime::polygon"
  echo "  $0 verus-topology -m src/queries.rs"
  exit 1
}

[[ $# -lt 1 ]] && usage

CRATE="$1"; shift
MODULE=""
RAW=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --module|-m) MODULE="$2"; shift 2 ;;
    --raw|-r)    RAW=true; shift ;;
    -h|--help)   usage ;;
    *)           echo "Unknown arg: $1"; usage ;;
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

# Build --verify-module flag
MODULE_FLAG=""
if [[ -n "$MODULE" ]]; then
  # Convert crate name to underscore form
  CRATE_MOD="${CRATE//-/_}"

  if [[ "$MODULE" == *"::"* && "$MODULE" != *"/"* ]]; then
    # Module path — strip crate:: or crate_mod:: prefix if present
    MOD="$MODULE"
    MOD="${MOD#crate::}"
    MOD="${MOD#${CRATE_MOD}::}"
  else
    # File path — strip src/ prefix and .rs suffix, convert / to ::
    MOD="$MODULE"
    MOD="${MOD#src/}"
    MOD="${MOD%.rs}"
    MOD="${MOD//\//::}"
    MOD="${MOD/::mod/}"
  fi
  MODULE_FLAG="--verify-module $MOD "
fi

cd "$CRATE_DIR"

if $RAW; then
  "$CARGO_VERUS" verify --manifest-path Cargo.toml -p "$CRATE" -- ${MODULE_FLAG}--triggers-mode silent
else
  "$CARGO_VERUS" verify --manifest-path Cargo.toml -p "$CRATE" --message-format=json -- ${MODULE_FLAG}--triggers-mode silent
fi
