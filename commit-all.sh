#!/bin/sh
set -e

for dir in verus-*/; do
    if [ -e "$dir/.git" ]; then
        echo "=== $dir ==="
        cd "$dir"
        git add . && git commit -m "h"
        cd ..
    fi
done
