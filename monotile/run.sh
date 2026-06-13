#!/usr/bin/env bash
# Run the CEGIS search (cegis.py) under the project's uv venv.
#
# This box is NixOS: the pip/uv-installed numpy + python-sat wheels expect
# libz.so.1 and libstdc++.so.6 on the loader path, which NixOS does not put in
# the usual places. We point LD_LIBRARY_PATH at the nix-store copies. The paths
# are discovered dynamically (so a system update doesn't break this), with the
# currently-known-good store paths as a fallback.
set -euo pipefail

cd "$(dirname "$0")"

PY=/home/bepis/.venv/bin/python3

# libz: the NixOS system profile exposes a stable symlink here.
ZLIB_DIR=/run/current-system/sw/lib

# libstdc++: scan the store for a 64-bit gcc libstdc++.so.6 and prefer the
# highest gcc version. (The store holds 32-bit multilib copies too, so we must
# check the ELF class — byte 4 == 2 means ELFCLASS64 — not just the filename.)
# Falls back to a currently-known-good path if the scan finds nothing.
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

exec "$PY" arena2.py "$@"
