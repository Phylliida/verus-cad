#!/bin/sh
set -e

for dir in verus-*/; do
    if [ -e "$dir/.git" ]; then
        echo "=== $dir ==="
        cd "$dir"
        git push
        cd ..
    fi
done
