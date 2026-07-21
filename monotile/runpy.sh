#!/usr/bin/env bash
# Generic runner: like run.sh (NixOS LD_LIBRARY_PATH dance for the uv venv's
# numpy + python-sat wheels) but runs an arbitrary script:
#     ./runpy.sh <script.py> [args...]
set -euo pipefail

cd "$(dirname "$0")"

PY=/home/bepis/.venv/bin/python3

ZLIB_DIR=/run/current-system/sw/lib

STDCPP_DIR=""
best_ver=""
while IFS= read -r so; do
  [ "$(od -An -tu1 -j4 -N1 "$so" 2>/dev/null | tr -d ' ')" = "2" ] || continue
  ver=$(printf '%s' "$so" | sed -n 's#.*gcc-\([0-9][0-9.]*\)-lib/.*#\1#p')
  [ -n "$ver" ] || continue
  if [ -z "$best_ver" ] || [ "$(printf '%s\n%s\n' "$ver" "$best_ver" | sort -V | tail -1)" = "$ver" ]; then
    best_ver="$ver"
    STDCPP_DIR=$(dirname "$so")
  fi
done < <(find /nix/store -maxdepth 3 -name 'libstdc++.so.6' -path '*gcc-*-lib/*' 2>/dev/null)
if [ -z "$STDCPP_DIR" ]; then
  STDCPP_DIR=/nix/store/j2kgllgds4w7na8zqv1msi0mpvpjxda8-gcc-15.2.0-lib/lib
fi

export LD_LIBRARY_PATH="${ZLIB_DIR}:${STDCPP_DIR}${LD_LIBRARY_PATH:+:${LD_LIBRARY_PATH}}"
export PYTHONUNBUFFERED=1

exec "$PY" "$@"
