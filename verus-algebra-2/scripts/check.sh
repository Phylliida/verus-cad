#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
if [[ -z "${VERUS_TOOLCHAIN:-}" ]]; then
  case "$(uname -s)-$(uname -m)" in
    Darwin-arm64)  TOOLCHAIN="1.93.0-aarch64-apple-darwin" ;;
    Darwin-x86_64) TOOLCHAIN="1.93.0-x86_64-apple-darwin" ;;
    *)             TOOLCHAIN="1.93.0-x86_64-unknown-linux-gnu" ;;
  esac
else
  TOOLCHAIN="$VERUS_TOOLCHAIN"
fi

OFFLINE=0
while [[ "$#" -gt 0 ]]; do
  case "${1:-}" in
    --offline) OFFLINE=1 ;;
    -h|--help) echo "usage: ./scripts/check.sh [--offline]"; exit 0 ;;
    *) echo "error: unknown argument '$1'"; exit 1 ;;
  esac
  shift
done

CARGO_CMD=(cargo)
if [[ "$OFFLINE" == "1" ]]; then
  CARGO_CMD=(cargo --offline)
fi

if [[ ! -x "$VERUS_SOURCE/target-verus/release/cargo-verus" ]]; then
  echo "error: cargo-verus not found at $VERUS_SOURCE/target-verus/release/cargo-verus"
  exit 1
fi

if [[ ! -x "$VERUS_SOURCE/z3" ]]; then
  echo "error: z3 not found at $VERUS_SOURCE/z3"
  exit 1
fi

export PATH="$VERUS_SOURCE/target-verus/release:$PATH"
export VERUS_Z3_PATH="$VERUS_SOURCE/z3"
export RUSTUP_TOOLCHAIN="$TOOLCHAIN"

echo "[check] Running cargo verus verify for verus-algebra-2"

verus_log="$(mktemp)"
set +e
cd "$ROOT_DIR"
"${CARGO_CMD[@]}" verus verify --manifest-path Cargo.toml -p verus-algebra-2 -- --triggers-mode silent 2>&1 | tee "$verus_log"
verus_status="${PIPESTATUS[0]}"
set -e

if (( verus_status != 0 )); then
  rm -f "$verus_log"
  exit "$verus_status"
fi

summary="$(sed -nE 's/.*verification results::[[:space:]]*([0-9]+) verified,[[:space:]]*([0-9]+) errors.*/\1|\2/p' "$verus_log" | tail -n 1 || true)"
if [[ -z "$summary" ]]; then
  echo "error: could not parse Verus verification summary"
  cat "$verus_log"
  rm -f "$verus_log"
  exit 1
fi

verified_count="${summary%%|*}"
error_count="${summary##*|}"

if (( error_count != 0 )); then
  echo "error: Verus verification reported $error_count errors"
  rm -f "$verus_log"
  exit 1
fi

echo "[check] Verus verification passed: $verified_count verified, 0 errors"
rm -f "$verus_log"
