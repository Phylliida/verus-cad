"""Syntax probes: word order, collocations, formulae, anchor candidates.

Everything here operates on cluster assignments from cluster.py plus
raw token sequences. Output is evidence for an analyst, not claims:
cluster transition preferences, sentence-edge affinities, high-PMI
bigrams, and repeated multiword formulae.
"""

import math
from collections import Counter, defaultdict

from .corpus import BOS, EOS


def cluster_transitions(sentences, assign, top=20):
    """P(next cluster | cluster), plus sentence-boundary affinities."""
    trans = Counter()
    totals = Counter()
    for sent in sentences:
        seq = [assign.get(w) for w in sent]
        seq = [BOS] + [c for c in seq] + [EOS]
        for a, b in zip(seq, seq[1:]):
            if a is None or b is None:
                continue
            trans[(a, b)] += 1
            totals[a] += 1
    rows = []
    for (a, b), c in trans.most_common():
        if totals[a] < 10:
            continue
        p = c / totals[a]
        if p >= 0.05 and c >= 5:
            rows.append({"from": a, "to": b, "count": c, "p": round(p, 3)})
    rows.sort(key=lambda r: -r["count"])
    return rows[:top * 2]


def pmi_bigrams(sentences, min_count=5, top=30):
    uni = Counter()
    bi = Counter()
    for s in sentences:
        uni.update(s)
        for a, b in zip(s, s[1:]):
            bi[(a, b)] += 1
    total_uni = sum(uni.values())
    total_bi = sum(bi.values())
    out = []
    for (a, b), c in bi.items():
        if c < min_count:
            continue
        pmi = math.log2((c / total_bi) / ((uni[a] / total_uni) * (uni[b] / total_uni)))
        out.append({"a": a, "b": b, "count": c, "pmi": round(pmi, 2)})
    out.sort(key=lambda r: -r["pmi"])
    return out[:top]


def formulae(sentences, min_n=3, max_n=5, min_count=4, top=20):
    """Repeated multiword sequences — greetings, headers, fixed phrases.

    Formulae are decipherment gold: they often mark text function.
    """
    grams = Counter()
    for s in sentences:
        for n in range(min_n, max_n + 1):
            for i in range(len(s) - n + 1):
                grams[tuple(s[i:i + n])] += 1
    # keep maximal ones: drop an n-gram if a longer one containing it is as frequent
    out = []
    items = [(g, c) for g, c in grams.items() if c >= min_count]
    items.sort(key=lambda gc: (-gc[1], -len(gc[0])))
    kept = []
    for g, c in items:
        sub = any(len(h) > len(g) and c == hc and " ".join(g) in " ".join(h)
                  for h, hc in kept)
        if not sub:
            kept.append((g, c))
    for g, c in kept[:top]:
        out.append({"phrase": " ".join(g), "count": c})
    return out


def edge_profile(clusters):
    """Summarize where each cluster likes to sit in the sentence."""
    rows = []
    for c in clusters:
        openness = "closed" if (c["n_types"] <= 12 and c["tokens_per_type"] >= 20) else \
                   "open" if c["n_types"] >= 25 else "small"
        pos = c["mean_norm_position"]
        if c["p_sentence_final"] > 0.5:
            habit = "strongly sentence-final"
        elif c["p_sentence_initial"] > 0.5:
            habit = "strongly sentence-initial"
        elif pos > 0.7:
            habit = "late in sentence"
        elif pos < 0.3:
            habit = "early in sentence"
        else:
            habit = "medial"
        rows.append({
            "id": c["id"],
            "n_types": c["n_types"],
            "token_share": round(c["token_share"], 3),
            "class_type": openness,
            "position_habit": habit,
            "examples": c["members"][:8],
        })
    return rows


def anchor_candidates(corpus, assign, clusters, top=15):
    """Heuristics for the words most likely to yield external anchors.

    - Numeral-like: members of a closed class that immediately precede or
      follow one open class, and rarely occur adjacent to each other.
    - Name-like: low-frequency words that slot into high-frequency frames
      (their contexts are shared with many other words).
    """
    type_counts = corpus.type_counts()
    by_id = {c["id"]: c for c in clusters}

    # adjacency of each closed cluster to open clusters vs itself
    adj_open = Counter()
    adj_self = Counter()
    adj_total = Counter()
    for sent in corpus.sentences:
        seq = [(w, assign.get(w)) for w in sent]
        for (wa, ca), (wb, cb) in zip(seq, seq[1:]):
            if ca is None or cb is None:
                continue
            for c_this, c_other in ((ca, cb), (cb, ca)):
                cl = by_id.get(c_this)
                if cl and cl["n_types"] <= 15:
                    adj_total[c_this] += 1
                    if c_this == c_other:
                        adj_self[c_this] += 1
                    other = by_id.get(c_other)
                    if other and other["n_types"] >= 25:
                        adj_open[c_this] += 1

    numeral_like = []
    for cid, tot in adj_total.items():
        if tot < 20:
            continue
        open_rate = adj_open[cid] / tot
        self_rate = adj_self[cid] / tot
        if open_rate > 0.6 and self_rate < 0.1:
            numeral_like.append({
                "cluster": cid,
                "members": by_id[cid]["members"][:12],
                "open_adjacency": round(open_rate, 2),
                "self_adjacency": round(self_rate, 2),
            })
    numeral_like.sort(key=lambda r: -r["open_adjacency"])

    return {"numeral_like_clusters": numeral_like[:5]}


def run(corpus, cluster_result):
    assign = cluster_result["assign"]
    clusters = cluster_result["clusters"]
    return {
        "edge_profile": edge_profile(clusters),
        "transitions": cluster_transitions(corpus.sentences, assign),
        "pmi_bigrams": pmi_bigrams(corpus.sentences),
        "formulae": formulae(corpus.sentences),
        "anchors": anchor_candidates(corpus, assign, clusters),
    }
