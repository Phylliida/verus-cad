#!/usr/bin/env bash
# Streaming cube-and-conquer verification of genArena.cnf with cake_lpr.
# Resumable (verified.txt): re-run any time. Verifies each leaf's binary LRAT
# cert with cake_lpr, deletes it (bounds disk), solves the unsolved frontier,
# and writes manifest.json + a cover (trie-completeness) check when the tree
# is complete. Trust: cake_lpr (CakeML/HOL4-verified LRAT checker).
cd "$(dirname "$0")" || exit 1
export LD_LIBRARY_PATH=/run/current-system/sw/lib:/nix/store/j2kgllgds4w7na8zqv1msi0mpvpjxda8-gcc-15.2.0-lib/lib
PY=/home/bepis/.venv/bin/python3
[ -x tools/cake_lpr/cake_lpr ] || { echo "ERROR: build cake_lpr first (cd tools/cake_lpr && make)"; exit 1; }
if pgrep -f "[s]tream_verify.py" >/dev/null; then
  echo "already running (PID $(pgrep -f '[s]tream_verify.py' | tr '\n' ' '))"
else
  setsid "$PY" stream_verify.py >> stream_verify.log 2>&1 < /dev/null &
  echo "started streaming verification (PID $!)"
fi
echo "verified: $(wc -l < cube_certs/verified.txt 2>/dev/null || echo 0) | remaining certs: $(ls cube_certs/*.lrat 2>/dev/null | wc -l) | df: $(df -h . | tail -1 | awk '{print $4}') free"
[ -f cube_certs/manifest.json ] && echo "manifest.json EXISTS -> tree complete + verified"
echo "watch: tail -f $(pwd)/stream_verify.log"
