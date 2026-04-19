#!/bin/sh

git config -f .gitmodules --get-regexp '^submodule\..*\.path$' | while read -r key path; do
    [ -e "$path/.git" ] || continue
    echo "=== $path ==="
    (cd "$path" && git add . && git commit -m "h") || echo "(nothing to commit)"
done
