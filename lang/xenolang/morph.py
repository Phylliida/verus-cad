"""Morphology induction: recover affixes and inflection paradigms.

Signature-based approach (after Goldsmith's Linguistica): a suffix is
credible when many distinct stems combine both with it and with other
suffixes (or stand alone). Stems sharing the same suffix set form a
"signature" — a candidate inflection paradigm, e.g. in English
{-∅, -s, -ed, -ing} over walk/talk/jump.

Run symmetrically on reversed words to detect prefixing languages.
"""

from collections import Counter, defaultdict

NULL = "∅"


def _affix_candidates(words, max_affix=5, min_stem=3):
    """Map suffix -> set of stems, over all splits of all word types."""
    stems_by_affix = defaultdict(set)
    for w in words:
        for k in range(1, max_affix + 1):
            if len(w) - k >= min_stem:
                stems_by_affix[w[-k:]].add(w[:-k])
    return stems_by_affix


def _score_affixes(stems_by_affix, words, min_stems=3):
    """An affix scores by the number of its stems that show independent
    evidence: the stem is itself a word, or combines with a different
    affix too.
    """
    affix_of_stem = defaultdict(set)
    for affix, stems in stems_by_affix.items():
        for st in stems:
            affix_of_stem[st].add(affix)

    scores = {}
    for affix, stems in stems_by_affix.items():
        ev = 0
        for st in stems:
            if st in words or len(affix_of_stem[st]) >= 2:
                ev += 1
        if ev >= min_stems:
            scores[affix] = ev
    return scores


def _signatures(words, kept_affixes, max_affix=5, min_stem=3):
    """Group stems by the exact set of kept affixes they take."""
    stem_affixes = defaultdict(set)
    for w in words:
        for k in range(1, max_affix + 1):
            if len(w) - k >= min_stem and w[-k:] in kept_affixes:
                stem_affixes[w[:-k]].add(w[-k:])
    for st in list(stem_affixes):
        if st in words:
            stem_affixes[st].add(NULL)

    sig_stems = defaultdict(list)
    for st, affs in stem_affixes.items():
        if len(affs) >= 2:
            sig_stems[tuple(sorted(affs))].append(st)

    sigs = []
    for sig, stems in sig_stems.items():
        if len(stems) < 2:
            continue
        # Robustness: letters saved by factoring the paradigm (Goldsmith).
        saved = (len(stems) - 1) * sum(len(a) for a in sig if a != NULL) \
            + (len(sig) - 1) * sum(len(s) for s in stems)
        sigs.append({
            "affixes": list(sig),
            "stems": sorted(stems),
            "n_stems": len(stems),
            "robustness": saved,
        })
    sigs.sort(key=lambda s: -s["robustness"])
    return sigs


def _analyze_side(type_counts, max_affix, min_stem, min_stems, reverse=False):
    words = set(type_counts)
    if reverse:
        words = {w[::-1] for w in words}
    stems_by_affix = _affix_candidates(words, max_affix, min_stem)
    scores = _score_affixes(stems_by_affix, words, min_stems)
    top = sorted(scores.items(), key=lambda kv: -kv[1])[:40]
    kept = {a for a, _ in top}
    sigs = _signatures(words, kept, max_affix, min_stem)
    if reverse:
        top = [(a[::-1], s) for a, s in top]
        for sig in sigs:
            sig["affixes"] = [a if a == NULL else a[::-1] for a in sig["affixes"]]
            sig["stems"] = sorted(s[::-1] for s in sig["stems"])
    total_evidence = sum(s for _, s in top)
    return {"affixes": top, "signatures": sigs[:25], "total_evidence": total_evidence}


def run(type_counts: Counter, max_affix=5, min_stem=3, min_stems=3):
    suffix = _analyze_side(type_counts, max_affix, min_stem, min_stems, reverse=False)
    prefix = _analyze_side(type_counts, max_affix, min_stem, min_stems, reverse=True)

    s_ev, p_ev = suffix["total_evidence"], prefix["total_evidence"]
    if s_ev + p_ev == 0:
        direction = "isolating (no productive affixation found)"
    elif s_ev >= 2 * p_ev:
        direction = "predominantly suffixing"
    elif p_ev >= 2 * s_ev:
        direction = "predominantly prefixing"
    else:
        direction = "mixed prefixing/suffixing"

    return {
        "direction": direction,
        "suffix": suffix,
        "prefix": prefix,
    }
