#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "Usage: $0 <crate> [--module <module>] [--top N] [--raw]"
  echo ""
  echo "Run Verus verification with per-function profiling on a crate."
  echo ""
  echo "  <crate>              Crate directory name (e.g. verus-geometry)"
  echo "  --module, -m <mod>   Profile only this module (file path or module path)"
  echo "  --top, -n <N>        Show top N functions (default: 25)"
  echo "  --raw, -r            Print raw compiler output"
  echo ""
  echo "Examples:"
  echo "  $0 verus-geometry"
  echo "  $0 verus-geometry -m runtime::polygon"
  echo "  $0 verus-topology -m src/queries.rs --top 50"
  exit 1
}

[[ $# -lt 1 ]] && usage

CRATE="$1"; shift
MODULE=""
RAW=false
TOP_N=25

while [[ $# -gt 0 ]]; do
  case "$1" in
    --module|-m) MODULE="$2"; shift 2 ;;
    --top|-n)    TOP_N="$2"; shift 2 ;;
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

if [[ ! -x "$CARGO_VERUS" ]]; then
  echo "error: cargo-verus not found at $CARGO_VERUS"
  exit 1
fi

if [[ ! -x "$VERUS_SOURCE/z3" ]]; then
  echo "error: expected z3 at $VERUS_SOURCE/z3"
  exit 1
fi

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
  CRATE_MOD="${CRATE//-/_}"

  if [[ "$MODULE" == *"::"* && "$MODULE" != *"/"* ]]; then
    MOD="$MODULE"
    MOD="${MOD#crate::}"
    MOD="${MOD#${CRATE_MOD}::}"
  else
    MOD="$MODULE"
    MOD="${MOD#src/}"
    MOD="${MOD%.rs}"
    MOD="${MOD//\//::}"
    MOD="${MOD/::mod/}"
  fi
  MODULE_FLAG="--verify-module $MOD "
fi

JSON_FILE="$(mktemp)"
trap 'rm -f "$JSON_FILE"' EXIT

cd "$CRATE_DIR"

echo "=== $CRATE function profile ===" >&2
echo "" >&2

WALL_START="$(date +%s)"
set +e
"$CARGO_VERUS" verify --manifest-path Cargo.toml -p "$CRATE" \
  -- ${MODULE_FLAG}--output-json --time-expanded --triggers-mode silent \
  > "$JSON_FILE" 2>/dev/null
VERUS_STATUS=$?
set -e
WALL_END="$(date +%s)"
WALL_ELAPSED=$((WALL_END - WALL_START))

if $RAW; then
  cat "$JSON_FILE"
  exit $VERUS_STATUS
fi

python3 - "$JSON_FILE" "$TOP_N" "$WALL_ELAPSED" <<'PYEOF'
import json, sys, re

json_path = sys.argv[1]
top_n = int(sys.argv[2])
wall = int(sys.argv[3])

with open(json_path) as f:
    raw = f.read().strip()

# Strip non-JSON lines (e.g. "Compiling ...", "Finished ...")
# by finding the outermost { ... } JSON object
brace_depth = 0
json_start = None
json_end = None
for i, ch in enumerate(raw):
    if ch == '{':
        if brace_depth == 0:
            json_start = i
        brace_depth += 1
    elif ch == '}':
        brace_depth -= 1
        if brace_depth == 0:
            json_end = i + 1
            # take the last complete top-level object
            # (the first might be a small cargo metadata blob)

if json_start is None or json_end is None:
    print(f"error: no JSON object found in output. Raw output:\n{raw[:500]}", file=sys.stderr)
    sys.exit(1)

data = json.loads(raw[json_start:json_end])

# If this object doesn't have times-ms, scan for the next one
if "times-ms" not in data:
    rest = raw[json_end:]
    m = re.search(r'\{', rest)
    if m:
        second_start = json_end + m.start()
        brace_depth = 0
        for i, ch in enumerate(raw[second_start:], second_start):
            if ch == '{':
                brace_depth += 1
            elif ch == '}':
                brace_depth -= 1
                if brace_depth == 0:
                    data = json.loads(raw[second_start:i+1])
                    break

times = data.get("times-ms", {})
smt = times.get("smt", {})
verified = data.get("verification-results", {}).get("verified", "?")
errors = data.get("verification-results", {}).get("errors", "?")

# Collect per-function data from smt-run-module-times
funcs = []
for mod in smt.get("smt-run-module-times", []):
    for fn in mod.get("function-breakdown", []):
        name = fn["function"].split("::")[-1]
        module = mod["module"]
        funcs.append({
            "name": name,
            "module": module,
            "time_us": fn["time-micros"],
            "rlimit": fn["rlimit"],
            "ok": fn.get("success", True),
        })

funcs.sort(key=lambda x: x["rlimit"], reverse=True)
total_us = sum(f["time_us"] for f in funcs)
total_rlimit = sum(f["rlimit"] for f in funcs)

print(f"{'#':>3}  {'Function':<48} {'Time':>10} {'Rlimit':>12}  {'Module'}")
print("-" * 100)

for i, fn in enumerate(funcs[:top_n]):
    ms = fn["time_us"] / 1000
    rlimit_s = f"{fn['rlimit']:,}"
    fail = " FAIL" if not fn["ok"] else ""
    print(f"{i+1:>3}  {fn['name']:<48} {ms:>8.1f}ms {rlimit_s:>12}  {fn['module']}{fail}")

print()

# Module summary
mods = {}
for fn in funcs:
    m = fn["module"]
    if m not in mods:
        mods[m] = {"time_us": 0, "rlimit": 0, "count": 0}
    mods[m]["time_us"] += fn["time_us"]
    mods[m]["rlimit"] += fn["rlimit"]
    mods[m]["count"] += 1

print(f"{'Module':<35} {'Time':>10} {'Rlimit':>14}  {'Fns':>4}")
print("-" * 72)
for m, v in sorted(mods.items(), key=lambda x: x[1]["rlimit"], reverse=True):
    ms = v["time_us"] / 1000
    print(f"{m:<35} {ms:>8.1f}ms {v['rlimit']:>14,}  {v['count']:>4}")

print()
print(f"Total: {len(funcs)} functions, {total_us/1000:.0f}ms SMT, {total_rlimit:,} rlimit, wall {wall}s")
print(f"Verification: {verified} verified, {errors} errors")
PYEOF

exit $VERUS_STATUS
