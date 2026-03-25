#!/usr/bin/env bash
input=$(cat)

# Context usage
ctx_pct=$(echo "$input" | grep -o '"used_percentage":[0-9.]*' | head -1 | grep -o '[0-9.]*')

# Rate limits
five_pct=$(echo "$input" | grep -o '"five_hour":{[^}]*' | grep -o '"used_percentage":[0-9.]*' | grep -o '[0-9.]*')
five_reset=$(echo "$input" | grep -o '"five_hour":{[^}]*' | grep -o '"resets_at":[0-9]*' | grep -o '[0-9]*')
week_pct=$(echo "$input" | grep -o '"seven_day":{[^}]*' | grep -o '"used_percentage":[0-9.]*' | grep -o '[0-9.]*')
week_reset=$(echo "$input" | grep -o '"seven_day":{[^}]*' | grep -o '"resets_at":[0-9]*' | grep -o '[0-9]*')

now=$(date +%s)

fmt_remaining() {
    local reset=$1
    [ -z "$reset" ] && return
    local diff=$(( reset - now ))
    [ "$diff" -le 0 ] && echo "now" && return
    local d=$(( diff / 86400 ))
    local h=$(( (diff % 86400) / 3600 ))
    local m=$(( (diff % 3600) / 60 ))
    local out=""
    [ "$d" -gt 0 ] && out="${d}d"
    [ "$h" -gt 0 ] && out="${out}${h}h"
    [ "$m" -gt 0 ] && out="${out}${m}m"
    [ -z "$out" ] && out="<1m"
    echo "$out"
}

# Build context bar: filled/total out of 95%
bar_width=10
if [ -n "$ctx_pct" ]; then
    filled=$(echo "$ctx_pct 95 $bar_width" | awk '{printf "%d", ($1/$2)*$3}')
    [ "$filled" -gt "$bar_width" ] && filled=$bar_width
    bar=""
    for ((i=0; i<filled; i++)); do bar="${bar}█"; done
    for ((i=filled; i<bar_width; i++)); do bar="${bar}░"; done
    ctx_part="${bar} $(printf '%.0f' "$ctx_pct")/95%"
else
    ctx_part=""
fi

# Rate limit parts
five_remaining=$(fmt_remaining "$five_reset")
week_remaining=$(fmt_remaining "$week_reset")

rl_part=""
[ -n "$five_pct" ] && rl_part="5h: $(printf '%.0f' "$five_pct")%"
[ -n "$five_remaining" ] && rl_part="${rl_part} (${five_remaining})"
if [ -n "$week_pct" ]; then
    [ -n "$rl_part" ] && rl_part="${rl_part}  "
    rl_part="${rl_part}7d: $(printf '%.0f' "$week_pct")%"
    [ -n "$week_remaining" ] && rl_part="${rl_part} (${week_remaining})"
fi

# Combine
out=""
[ -n "$ctx_part" ] && out="$ctx_part"
[ -n "$rl_part" ] && { [ -n "$out" ] && out="$out  │  "; out="${out}${rl_part}"; }
echo "$out"
