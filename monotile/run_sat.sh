#!/usr/bin/env bash
# Resume the cube-and-conquer LRAT cert generation for genArena.cnf.
#
# Safe to re-run any time (e.g. after a machine restart): gen_cube_certs.py is
# resumable -- it skips every cube already solved (cert on disk) or known-split
# (split_cache.txt) WITHOUT re-running cadical, and continues from the unsolved
# frontier. Writes cube_certs/manifest.json once the whole tree is UNSAT.

cd "$(dirname "$0")" || exit 1
export LD_LIBRARY_PATH=/run/current-system/sw/lib:/nix/store/j2kgllgds4w7na8zqv1msi0mpvpjxda8-gcc-15.2.0-lib/lib
PY=/home/bepis/.venv/bin/python3

[ -f genArena.cnf ] || { echo "ERROR: genArena.cnf missing (export it from Lean first)."; exit 1; }

if pgrep -f "[g]en_cube_certs.py" >/dev/null; then
  echo "already running (PID $(pgrep -f '[g]en_cube_certs.py' | tr '\n' ' '))"
else
  setsid "$PY" gen_cube_certs.py >> cube_certs.log 2>&1 < /dev/null &
  echo "resumed cube cert generation (PID $!)"
fi

leaves=$(ls cube_certs/*.lrat 2>/dev/null | wc -l)
splits=$(wc -l < cube_certs/split_cache.txt 2>/dev/null || echo 0)
echo "leaves solved: $leaves  |  split-nodes cached: $splits"
[ -f cube_certs/manifest.json ] && echo "manifest.json EXISTS -> tree complete"
echo "watch:  tail -f $(pwd)/cube_certs.log"
