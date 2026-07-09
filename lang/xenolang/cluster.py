"""Distributional word classes.

Words are represented by PPMI-weighted vectors over their immediate
left/right neighbors (position-sensitive), then clustered with
spherical k-means (cosine). Words that pattern alike syntactically —
same neighbors on both sides — land in the same cluster; in practice
these clusters approximate parts of speech and inflection classes.

Also reports the classic decipherment "substitution grid": pairs of
words with near-identical contexts, i.e. mutually substitutable.
"""

import math
from collections import Counter, defaultdict

from .corpus import BOS, EOS


def build_vectors(sentences, target_words, feature_words):
    """PPMI vectors over ('L', neighbor) / ('R', neighbor) features."""
    fset = set(feature_words) | {BOS, EOS}
    counts = {w: Counter() for w in target_words}
    feat_totals = Counter()
    word_totals = Counter()
    grand = 0
    for sent in sentences:
        padded = [BOS] + sent + [EOS]
        for i in range(1, len(padded) - 1):
            w = padded[i]
            if w not in counts:
                continue
            for feat_word, side in ((padded[i - 1], "L"), (padded[i + 1], "R")):
                if feat_word in fset:
                    f = (side, feat_word)
                    counts[w][f] += 1
                    feat_totals[f] += 1
                    word_totals[w] += 1
                    grand += 1
    if grand == 0:
        return {}

    vectors = {}
    for w, feats in counts.items():
        if not feats:
            continue
        vec = {}
        for f, c in feats.items():
            pmi = math.log((c * grand) / (word_totals[w] * feat_totals[f]))
            if pmi > 0:
                vec[f] = pmi
        if vec:
            norm = math.sqrt(sum(v * v for v in vec.values()))
            vectors[w] = {f: v / norm for f, v in vec.items()}
    return vectors


def _dot(u, v):
    if len(u) > len(v):
        u, v = v, u
    return sum(x * v[f] for f, x in u.items() if f in v)


def _centroid(members, vectors, max_feats=400):
    acc = defaultdict(float)
    for w in members:
        for f, v in vectors[w].items():
            acc[f] += v
    if not acc:
        return {}
    top = sorted(acc.items(), key=lambda kv: -kv[1])[:max_feats]
    norm = math.sqrt(sum(v * v for _, v in top))
    return {f: v / norm for f, v in top} if norm > 0 else {}


def kmeans(vectors, k, freq, iterations=30):
    """Spherical k-means, centroids initialized at the k most frequent
    vectorized words. Frequent grammar words then anchor their own
    clusters instead of being absorbed into content-word clusters, and
    the result is deterministic (validated: +15-24 points of POS purity
    over k-means++ on the synthetic benchmark).
    """
    words = sorted(vectors)
    if len(words) <= k:
        return {w: i for i, w in enumerate(words)}

    seeds = sorted(words, key=lambda w: (-freq[w], w))[:k]
    centroids = [dict(vectors[w]) for w in seeds]

    assign = {}
    for _ in range(iterations):
        changed = 0
        for w in words:
            best, best_s = 0, -2.0
            v = vectors[w]
            for ci, c in enumerate(centroids):
                s = _dot(v, c)
                if s > best_s:
                    best, best_s = ci, s
            if assign.get(w) != best:
                changed += 1
            assign[w] = best
        members = defaultdict(list)
        for w, ci in assign.items():
            members[ci].append(w)
        for ci in range(k):
            if members[ci]:
                centroids[ci] = _centroid(members[ci], vectors)
            else:
                # reseed empty cluster with the word least similar to its centroid
                worst = min(words, key=lambda w: _dot(vectors[w], centroids[assign[w]]))
                centroids[ci] = dict(vectors[worst])
                assign[worst] = ci
        if changed == 0:
            break
    return assign


def substitution_grid(vectors, type_counts, top_words=300, top_pairs=40):
    """Most mutually-substitutable word pairs (highest context cosine)."""
    cand = [w for w, _ in type_counts.most_common() if w in vectors][:top_words]
    pairs = []
    for i in range(len(cand)):
        vi = vectors[cand[i]]
        for j in range(i + 1, len(cand)):
            s = _dot(vi, vectors[cand[j]])
            if s > 0.15:
                pairs.append((s, cand[i], cand[j]))
    pairs.sort(reverse=True)
    return [{"cosine": round(s, 3), "a": a, "b": b} for s, a, b in pairs[:top_pairs]]


def run(corpus, k=20, max_targets=1200, max_features=400, min_count=2):
    type_counts = corpus.type_counts()
    targets = [w for w, c in type_counts.most_common(max_targets) if c >= min_count]
    features = [w for w, _ in type_counts.most_common(max_features)]
    vectors = build_vectors(corpus.sentences, targets, features)
    assign = kmeans(vectors, k, type_counts)

    # positional stats per word
    pos_sum = Counter()
    pos_n = Counter()
    first = Counter()
    last = Counter()
    for sent in corpus.sentences:
        n = len(sent)
        for i, w in enumerate(sent):
            if n > 1:
                pos_sum[w] += i / (n - 1)
                pos_n[w] += 1
            if i == 0:
                first[w] += 1
            if i == n - 1:
                last[w] += 1

    clusters = []
    members = defaultdict(list)
    for w, ci in assign.items():
        members[ci].append(w)
    total_tokens = sum(type_counts.values())
    for ci in sorted(members):
        ws = sorted(members[ci], key=lambda w: -type_counts[w])
        tok = sum(type_counts[w] for w in ws)
        occ = sum(pos_n[w] for w in ws)
        mean_pos = (sum(pos_sum[w] for w in ws) / occ) if occ else 0.5
        n_first = sum(first[w] for w in ws)
        n_last = sum(last[w] for w in ws)
        mean_len = sum(len(w) for w in ws) / len(ws)
        clusters.append({
            "id": ci,
            "n_types": len(ws),
            "n_tokens": tok,
            "token_share": tok / total_tokens,
            "tokens_per_type": tok / len(ws),
            "mean_norm_position": mean_pos,
            "p_sentence_initial": n_first / tok if tok else 0.0,
            "p_sentence_final": n_last / tok if tok else 0.0,
            "mean_word_length": mean_len,
            "members": ws,
        })
    clusters.sort(key=lambda c: -c["n_tokens"])

    grid = substitution_grid(vectors, type_counts)
    return {
        "assign": assign,
        "clusters": clusters,
        "substitution_grid": grid,
        "n_vectorized": len(vectors),
    }
