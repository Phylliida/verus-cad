"""Score the xenolang toolkit against the synthetic language's ground truth.

Metrics:
  - cluster purity: do distributional clusters match true parts of speech?
    (token-weighted majority-label purity, plus per-cluster breakdown)
  - suffix recovery: are the true suffixes among the top suffix candidates?
  - segmentation F1: boundary precision/recall on the no-space corpus
"""

import json
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from xenolang import corpus as corpus_mod
from xenolang import cluster as cluster_mod
from xenolang import morph as morph_mod
from xenolang import segment as segment_mod


def cluster_purity(corp, gold_lex, k=20):
    res = cluster_mod.run(corp, k=k)
    counts = corp.type_counts()
    total_w = 0
    correct_w = 0
    breakdown = []
    for c in res["clusters"]:
        lab = Counter()
        for w in c["members"]:
            g = gold_lex.get(w)
            if g:
                lab[g["pos"]] += counts[w]
        if not lab:
            continue
        maj, majc = lab.most_common(1)[0]
        tot = sum(lab.values())
        total_w += tot
        correct_w += majc
        breakdown.append((c["id"], maj, majc / tot, tot, dict(lab.most_common(3))))
    return correct_w / total_w if total_w else 0.0, breakdown, res


def suffix_recovery(corp, true_suffixes, top_n=20):
    mo = morph_mod.run(corp.type_counts())
    found = [a for a, _ in mo["suffix"]["affixes"][:top_n]]
    hits = [s for s in true_suffixes if s in found]
    # composite chains like 'neka' (plural+case) also count as structure found
    composites = [f for f in found
                  if f not in true_suffixes
                  and any(f.endswith(s) and f[:-len(s)] in true_suffixes
                          for s in true_suffixes)]
    return {
        "recall": len(hits) / len(true_suffixes),
        "hits": hits,
        "missed": [s for s in true_suffixes if s not in found],
        "composites_found": composites,
        "direction": mo["direction"],
        "top_found": found,
    }


def segmentation_f1(nospace_path, spaced_path, gold_lex):
    with open(spaced_path, encoding="utf-8") as f:
        gold_lines = [l.split() for l in f if l.strip()]
    with open(nospace_path, encoding="utf-8") as f:
        raw = [l.strip() for l in f if l.strip()]
    res = segment_mod.run(raw)

    def word_bounds(tokens):
        b = set()
        pos = 0
        for t in tokens[:-1]:
            pos += len(t)
            b.add(pos)
        return b

    def morph_bounds(tokens):
        """word boundaries plus gold-internal morpheme boundaries"""
        b, pos = set(), 0
        for i, t in enumerate(tokens):
            g = gold_lex[t]
            mpos = pos + len(g["stem"])
            for suf in g["suffixes"]:
                b.add(mpos)
                mpos += len(suf)
            pos += len(t)
            if i < len(tokens) - 1:
                b.add(pos)
        return b

    def prf(target_fn):
        tp = fp = fn = 0
        for gold_toks, pred_toks in zip(gold_lines, res["segmented"]):
            g = target_fn(gold_toks)
            p = word_bounds(pred_toks)
            tp += len(g & p)
            fp += len(p - g)
            fn += len(g - p)
        prec = tp / (tp + fp) if tp + fp else 0.0
        rec = tp / (tp + fn) if tp + fn else 0.0
        f1 = 2 * prec * rec / (prec + rec) if prec + rec else 0.0
        return {"precision": prec, "recall": rec, "f1": f1}

    return {"word": prf(word_bounds), "morph": prf(morph_bounds),
            "mean_word_length": res["mean_word_length"],
            "lexicon_size": res["lexicon_size"]}


def main():
    testdir = sys.argv[1] if len(sys.argv) > 1 else "testdata"
    with open(os.path.join(testdir, "gold.json"), encoding="utf-8") as f:
        gold = json.load(f)
    corp = corpus_mod.load(os.path.join(testdir, "corpus.txt"))

    print("=" * 64)
    print("XENOLANG VALIDATION SCORECARD")
    print(f"gold grammar: {gold['order']}")
    print("=" * 64)

    purity, breakdown, _ = cluster_purity(corp, gold["lexicon"])
    print(f"\n[1] Word-class discovery — cluster purity vs true POS: {purity:.1%}")
    for cid, maj, p, tot, top3 in sorted(breakdown, key=lambda r: -r[3]):
        print(f"    C{cid:<3} -> {maj:<5} purity {p:5.1%}  ({tot} tokens)  {top3}")

    sr = suffix_recovery(corp, gold["true_suffixes"])
    print(f"\n[2] Morphology — true-suffix recall in top-20 candidates: {sr['recall']:.1%}")
    print(f"    direction call: {sr['direction']}")
    print(f"    recovered: {sr['hits']}")
    if sr["missed"]:
        print(f"    missed:    {sr['missed']}")
    if sr["composites_found"]:
        print(f"    composite chains also found: {sr['composites_found']}")

    seg = segmentation_f1(os.path.join(testdir, "corpus_nospace.txt"),
                          os.path.join(testdir, "corpus.txt"), gold["lexicon"])
    w, m = seg["word"], seg["morph"]
    print(f"\n[3] Segmentation (no-space corpus)")
    print(f"    word-boundary  F1: {w['f1']:.1%} (P {w['precision']:.1%} / R {w['recall']:.1%})")
    print(f"    morph-boundary F1: {m['f1']:.1%} (P {m['precision']:.1%} / R {m['recall']:.1%})")
    print(f"    induced lexicon {seg['lexicon_size']} types, "
          f"mean word {seg['mean_word_length']:.2f} chars")
    print()


if __name__ == "__main__":
    main()
