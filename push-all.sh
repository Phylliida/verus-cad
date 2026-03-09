#!/bin/bash
set -e

for dir in verus-*/; do
    if [ -e "$dir/.git" ]; then
        echo "=== $dir ==="
        cd "$dir"
        git add .
        git diff --cached --quiet && echo "  nothing to commit" || (git commit -m "h" && git push)
        cd ..
    fi
done
