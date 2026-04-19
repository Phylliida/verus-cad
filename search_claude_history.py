#!/usr/bin/env python3
"""Search Claude Code session history for keyword mentions.

Usage:
    python search_claude_history.py <pattern> [options]

Examples:
    # Search current project (auto-detects from cwd)
    python search_claude_history.py "conjecture|hypothesis"

    # Search a specific project
    python search_claude_history.py "TODO|FIXME" --project /home/user/myproject

    # Search all projects in ~/.claude
    python search_claude_history.py "bug" --all-projects

    # Search arbitrary directories containing .jsonl files (backups, etc.)
    python search_claude_history.py "refactor" --dir ~/backups/claude-sessions
    python search_claude_history.py "bug" --dir ~/old-claude --dir ~/another-backup

    # Write to file, with more context
    python search_claude_history.py "conjecture" -o results.txt -c 200
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path


def get_claude_dir():
    return Path.home() / ".claude"


def get_project_dirs(claude_dir, project_path=None, all_projects=False):
    projects_dir = claude_dir / "projects"
    if not projects_dir.exists():
        return []

    if all_projects:
        return [d for d in projects_dir.iterdir() if d.is_dir()]

    if project_path:
        mangled = str(Path(project_path).resolve()).replace("/", "-")
    else:
        mangled = str(Path.cwd().resolve()).replace("/", "-")

    target = projects_dir / mangled
    if target.exists():
        return [target]

    # fuzzy match
    matches = [d for d in projects_dir.iterdir() if d.is_dir() and mangled in d.name]
    return matches


def find_jsonl_files(dirs):
    files = []
    for d in dirs:
        d = Path(d)
        if d.is_file() and d.suffix == ".jsonl":
            files.append(d)
        elif d.is_dir():
            for f in d.rglob("*.jsonl"):
                files.append(f)
    return sorted(files, key=lambda f: f.stat().st_mtime)


def extract_text(obj):
    msg = obj.get("message", obj)
    if not isinstance(msg, dict):
        return None, None
    role = msg.get("role", "?")
    content = msg.get("content", "")
    text = ""
    if isinstance(content, str):
        text = content
    elif isinstance(content, list):
        for part in content:
            if isinstance(part, dict) and part.get("type") == "text":
                text += part.get("text", "") + " "
    return role, text


def search_file(filepath, pattern, context_chars, skip_patterns):
    results = []
    try:
        with open(filepath, "r", errors="replace") as f:
            for line in f:
                try:
                    obj = json.loads(line.strip())
                except (json.JSONDecodeError, ValueError):
                    continue
                role, text = extract_text(obj)
                if not text:
                    continue
                for m in re.finditer(
                    rf".{{0,{context_chars}}}({pattern}).{{0,{context_chars}}}",
                    text,
                    re.IGNORECASE,
                ):
                    snippet = m.group().strip()
                    if any(sp in snippet for sp in skip_patterns):
                        continue
                    results.append((role, snippet))
    except Exception as e:
        print(f"  [error reading {filepath}: {e}]", file=sys.stderr)
    return results


def main():
    parser = argparse.ArgumentParser(description="Search Claude Code session history")
    parser.add_argument("pattern", help="Regex pattern to search for")
    parser.add_argument("--project", "-p", help="Project path to search in ~/.claude (default: cwd)")
    parser.add_argument("--all-projects", action="store_true", help="Search all projects in ~/.claude")
    parser.add_argument("--dir", "-d", action="append", metavar="PATH",
                        help="Search .jsonl files in this directory (can be repeated). "
                             "Skips ~/.claude entirely — use for backups, exports, etc.")
    parser.add_argument("-o", "--output", help="Output file (default: stdout)")
    parser.add_argument("-c", "--context", type=int, default=150, help="Context chars around match (default: 150)")
    parser.add_argument(
        "--no-skip", action="store_true",
        help="Don't skip system reminder / CLAUDE.md echoes",
    )
    args = parser.parse_args()

    if args.dir:
        # Direct directory mode — no ~/.claude needed
        raw_dirs = []
        for d in args.dir:
            p = Path(d).expanduser().resolve()
            if not p.exists():
                print(f"Warning: {d} does not exist, skipping", file=sys.stderr)
            else:
                raw_dirs.append(p)
        if not raw_dirs:
            print("No valid directories provided.", file=sys.stderr)
            sys.exit(1)
        files = find_jsonl_files(raw_dirs)
    else:
        claude_dir = get_claude_dir()
        if not claude_dir.exists():
            print(f"No Claude directory found at {claude_dir}", file=sys.stderr)
            sys.exit(1)
        dirs = get_project_dirs(claude_dir, args.project, args.all_projects)
        if not dirs:
            print("No matching project directories found.", file=sys.stderr)
            sys.exit(1)
        files = find_jsonl_files(dirs)
    if not files:
        print("No session files found.", file=sys.stderr)
        sys.exit(1)

    skip_patterns = []
    if not args.no_skip:
        skip_patterns = ["CLAUDE.md", "system-reminder", "claudeMd", "instructions OVERRIDE"]

    out = open(args.output, "w") if args.output else sys.stdout

    # For display: find common ancestor of all files
    if len(files) > 1:
        common = Path(os.path.commonpath([str(f) for f in files]))
    else:
        common = files[0].parent

    total_matches = 0
    for filepath in files:
        results = search_file(filepath, args.pattern, args.context, skip_patterns)
        if results:
            try:
                rel = filepath.relative_to(common)
            except ValueError:
                rel = filepath
            print(f"=== {rel} ===", file=out)
            for role, snippet in results:
                print(f"  [{role}] ...{snippet}...", file=out)
                print(file=out)
                total_matches += 1

    print(f"\n--- {total_matches} matches across {len(files)} session files ---", file=out)

    if args.output:
        out.close()
        print(f"Wrote {total_matches} matches to {args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()
