#!/bin/sh

git config -f .gitmodules --get-regexp '^submodule\..*\.path$' | while read -r key path; do
    [ -e "$path/.git" ] || continue
    url=$(git -C "$path" remote get-url origin 2>/dev/null || echo "")
    case "$url" in
        "")
            echo "--- skip $path (no origin remote) ---"
            ;;
        *github.com[:/]Phylliida/*)
            ahead=$(git -C "$path" rev-list '@{u}..HEAD' --count 2>/dev/null || echo unknown)
            if [ "$ahead" = "0" ]; then
                echo "--- skip $path (already up to date) ---"
            else
                echo "=== $path ==="
                (cd "$path" && git push) || echo "(push failed)"
            fi
            ;;
        *)
            echo "--- skip $path ($url) ---"
            ;;
    esac
done
