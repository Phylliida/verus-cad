"""Unsupervised word segmentation for scripts without word boundaries.

Method: branching entropy (Harris 1955; Jin & Tanaka-Ishii 2006).
At a word boundary, the identity of the next character becomes hard to
predict — the entropy of the successor distribution spikes. We score
every inter-character position with forward + backward branching
entropy, then choose the boundary threshold by minimum description
length: the segmentation that best compresses the corpus (lexicon cost
+ corpus cost) wins.
"""

import math
from collections import Counter, defaultdict

MAX_CTX = 3  # longest character context used for branching entropy


def _build_models(lines, max_ctx=MAX_CTX):
    fwd = [defaultdict(Counter) for _ in range(max_ctx + 1)]
    bwd = [defaultdict(Counter) for _ in range(max_ctx + 1)]
    for line in lines:
        n = len(line)
        for i in range(n):
            for k in range(1, max_ctx + 1):
                if i - k >= 0:
                    fwd[k][line[i - k:i]][line[i]] += 1
                if i + k < n:
                    bwd[k][line[i + 1:i + 1 + k]][line[i]] += 1
    return fwd, bwd


def _entropy(counter):
    total = sum(counter.values())
    if total == 0:
        return 0.0
    h = 0.0
    for c in counter.values():
        p = c / total
        h -= p * math.log2(p)
    return h


def _boundary_scores(line, fwd, bwd, max_ctx=MAX_CTX, min_count=3):
    """Score for a boundary after position i (between line[i] and line[i+1]).

    Uses the longest context with enough evidence, backing off to
    shorter ones. Forward and backward views are averaged.
    """
    scores = []
    n = len(line)
    for i in range(n - 1):
        f = None
        for k in range(max_ctx, 0, -1):
            if i + 1 - k >= 0:
                ctx = line[i + 1 - k:i + 1]
                dist = fwd[k].get(ctx)
                if dist and sum(dist.values()) >= min_count:
                    f = _entropy(dist)
                    break
        b = None
        for k in range(max_ctx, 0, -1):
            if i + 1 + k <= n:
                ctx = line[i + 1:i + 1 + k]
                dist = bwd[k].get(ctx)
                if dist and sum(dist.values()) >= min_count:
                    b = _entropy(dist)
                    break
        parts = [x for x in (f, b) if x is not None]
        scores.append(sum(parts) / len(parts) if parts else 0.0)
    return scores


def _segment_with_threshold(lines, all_scores, threshold):
    segmented = []
    for line, scores in zip(lines, all_scores):
        toks = []
        start = 0
        for i, sc in enumerate(scores):
            if sc >= threshold:
                toks.append(line[start:i + 1])
                start = i + 1
        toks.append(line[start:])
        segmented.append(toks)
    return segmented


def _description_length(segmented):
    """Two-part MDL: cost of the lexicon + cost of the corpus under it."""
    lex = Counter()
    for toks in segmented:
        lex.update(toks)
    total_tokens = sum(lex.values())
    # Corpus cost: -log2 P(word) per token under the unigram lexicon model.
    corpus_bits = 0.0
    for w, c in lex.items():
        corpus_bits += -c * math.log2(c / total_tokens)
    # Lexicon cost: spell out each distinct word, char by char.
    chars = Counter()
    for w in lex:
        chars.update(w)
    char_total = sum(chars.values())
    char_h = 0.0
    for c in chars.values():
        p = c / char_total
        char_h -= p * math.log2(p)
    lexicon_bits = sum((len(w) + 1) * char_h for w in lex)
    return corpus_bits + lexicon_bits


def _xlx(c):
    return c * math.log2(c) if c > 0 else 0.0


def _char_entropy(lines):
    chars = Counter()
    for l in lines:
        chars.update(l)
    total = sum(chars.values())
    return -sum((c / total) * math.log2(c / total) for c in chars.values())


def _make_delta(lex, char_h):
    """DL change for a batch of count changes. `lex` and the token total
    are read at call time via closure over the mutable dict."""
    def delta(changes, n_tokens, dN):
        d = _xlx(n_tokens + dN) - _xlx(n_tokens)
        for w, dc in changes.items():
            c0 = lex.get(w, 0)
            c1 = c0 + dc
            d -= _xlx(c1) - _xlx(c0)
            if c0 == 0 and c1 > 0:
                d += (len(w) + 1) * char_h
            elif c0 > 0 and c1 == 0:
                d -= (len(w) + 1) * char_h
        return d
    return delta


def _mdl_type_moves(segmented, char_h, max_outer=6):
    """Type-level MDL moves: merge ALL adjacent occurrences of a token
    pair, or split ALL occurrences of a type, whenever that lowers total
    description length. Token-level flips get trapped — merging one
    occurrence of an over-cut word pays full lexicon cost for the new
    type — but batch moves amortize it (Morfessor-style).
    """
    lex = Counter()
    for toks in segmented:
        lex.update(toks)
    n_tokens = sum(lex.values())
    delta = _make_delta(lex, char_h)

    def apply_counts(changes, dN):
        nonlocal n_tokens
        n_tokens += dN
        for w, dc in changes.items():
            c = lex.get(w, 0) + dc
            if c > 0:
                lex[w] = c
            else:
                lex.pop(w, None)

    def merge_pass():
        moved = False
        while True:
            pairs = Counter()
            for toks in segmented:
                for a, b in zip(toks, toks[1:]):
                    pairs[(a, b)] += 1
            best = None
            for (a, b), c in pairs.items():
                if c < 2:
                    continue
                if a == b:
                    c = c - c // 2  # non-overlapping occurrences of (a, a)
                changes = Counter({a: -c, b: -c})
                changes[a + b] += c
                d = delta(changes, n_tokens, -c)
                if d < -1e-9 and (best is None or d < best[0]):
                    best = (d, a, b, changes, c)
            if best is None:
                return moved
            _, a, b, changes, c = best
            merged = 0  # actual non-overlapping merges may differ from the estimate
            for li, toks in enumerate(segmented):
                out = []
                i = 0
                while i < len(toks):
                    if i < len(toks) - 1 and toks[i] == a and toks[i + 1] == b:
                        out.append(a + b)
                        merged += 1
                        i += 2
                    else:
                        out.append(toks[i])
                        i += 1
                segmented[li] = out
            actual = Counter({a: -merged, b: -merged})
            actual[a + b] += merged
            apply_counts(actual, -merged)
            moved = True

    def split_pass():
        moved = False
        while True:
            best = None
            for t, c in lex.items():
                if len(t) < 2:
                    continue
                for i in range(1, len(t)):
                    changes = Counter({t: -c})
                    changes[t[:i]] += c
                    changes[t[i:]] += c
                    d = delta(changes, n_tokens, c)
                    if d < -1e-9 and (best is None or d < best[0]):
                        best = (d, t, i, changes, c)
            if best is None:
                return moved
            _, t, i, changes, c = best
            for li, toks in enumerate(segmented):
                out = []
                for tok in toks:
                    if tok == t:
                        out.append(t[:i])
                        out.append(t[i:])
                    else:
                        out.append(tok)
                segmented[li] = out
            apply_counts(changes, c)
            moved = True

    for _ in range(max_outer):
        any_move = merge_pass()
        any_move |= split_pass()
        if not any_move:
            break
    return segmented


def _mdl_local_search(lines, segmented, max_sweeps=8):
    """Greedily flip individual boundaries to reduce description length.

    The threshold segmentation tends to over-cut at morpheme boundaries;
    the two-part MDL objective prefers whole words, but a single global
    threshold can't express that. Flipping boundaries one at a time
    (merge or split, accept if DL drops) closes most of the gap.
    """
    lex = Counter()
    for toks in segmented:
        lex.update(toks)
    n_tokens = sum(lex.values())

    chars = Counter()
    for l in lines:
        chars.update(l)
    ctot = sum(chars.values())
    char_h = -sum((c / ctot) * math.log2(c / ctot) for c in chars.values())

    # boundary bitmap per line: bnd[i] == boundary between line[i] and line[i+1]
    bnds = []
    for line, toks in zip(lines, segmented):
        b = [False] * max(0, len(line) - 1)
        pos = 0
        for t in toks[:-1]:
            pos += len(t)
            b[pos - 1] = True
        bnds.append(b)

    def delta(changes, dN):
        nonlocal n_tokens
        N2 = n_tokens + dN
        d = _xlx(N2) - _xlx(n_tokens)  # N*log2(N) term of corpus cost
        for w, dc in changes.items():
            c0 = lex.get(w, 0)
            c1 = c0 + dc
            d -= _xlx(c1) - _xlx(c0)
            if c0 == 0 and c1 > 0:
                d += (len(w) + 1) * char_h
            elif c0 > 0 and c1 == 0:
                d -= (len(w) + 1) * char_h
        return d

    def apply(changes, dN):
        nonlocal n_tokens
        n_tokens += dN
        for w, dc in changes.items():
            c = lex.get(w, 0) + dc
            if c > 0:
                lex[w] = c
            else:
                lex.pop(w, None)

    for _ in range(max_sweeps):
        changed = 0
        for line, b in zip(lines, bnds):
            n = len(line)
            for i in range(n - 1):
                p = i - 1
                while p >= 0 and not b[p]:
                    p -= 1
                q = i + 1
                while q < n - 1 and not b[q]:
                    q += 1
                # right segment ends at char q if b[q] else at n-1
                end = q if q < n - 1 and b[q] else n - 1
                changes = Counter()
                if b[i]:  # try merge
                    left, right = line[p + 1:i + 1], line[i + 1:end + 1]
                    changes[left] -= 1
                    changes[right] -= 1
                    changes[left + right] += 1
                    dN = -1
                else:     # try split
                    whole = line[p + 1:end + 1]
                    changes[whole] -= 1
                    changes[line[p + 1:i + 1]] += 1
                    changes[line[i + 1:end + 1]] += 1
                    dN = +1
                if delta(changes, dN) < -1e-9:
                    apply(changes, dN)
                    b[i] = not b[i]
                    changed += 1
        if changed == 0:
            break

    out = []
    for line, b in zip(lines, bnds):
        toks = []
        start = 0
        for i, flag in enumerate(b):
            if flag:
                toks.append(line[start:i + 1])
                start = i + 1
        toks.append(line[start:])
        out.append(toks)
    return out


def run(lines, max_ctx=MAX_CTX, n_thresholds=12, refine=True):
    """Segment `lines` (strings without spaces). Returns dict with
    'segmented' (list of token lists) and diagnostics.
    """
    lines = [l for l in (l.strip() for l in lines) if l]
    fwd, bwd = _build_models(lines, max_ctx)
    all_scores = [_boundary_scores(l, fwd, bwd, max_ctx) for l in lines]

    flat = sorted(s for scores in all_scores for s in scores)
    if not flat:
        return {"segmented": [[l] for l in lines], "threshold": 0.0, "mdl_bits": 0.0}

    # Candidate thresholds at evenly spaced percentiles of the score
    # distribution; pick the one minimizing description length.
    candidates = []
    for q in range(1, n_thresholds + 1):
        idx = min(len(flat) - 1, int(len(flat) * q / (n_thresholds + 1)))
        candidates.append(flat[idx])
    candidates = sorted(set(candidates))

    best = None
    trials = []
    for th in candidates:
        seg = _segment_with_threshold(lines, all_scores, th)
        dl = _description_length(seg)
        mean_len = sum(len(w) for toks in seg for w in toks) / max(1, sum(len(t) for t in seg))
        trials.append({"threshold": th, "mdl_bits": dl, "mean_word_length": mean_len})
        if best is None or dl < best[1]:
            best = (th, dl, seg)

    th, dl, seg = best
    if refine:
        char_h = _char_entropy(lines)
        seg = _mdl_local_search(lines, seg)
        seg = _mdl_type_moves(seg, char_h)
        seg = _mdl_local_search(lines, seg)
        dl = _description_length(seg)
    lex = Counter()
    for toks in seg:
        lex.update(toks)
    return {
        "segmented": seg,
        "threshold": th,
        "mdl_bits": dl,
        "lexicon_size": len(lex),
        "mean_word_length": sum(len(w) * c for w, c in lex.items()) / sum(lex.values()),
        "trials": trials,
    }
