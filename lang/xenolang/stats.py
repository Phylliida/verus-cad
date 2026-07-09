"""Corpus statistics: is this corpus language-like?

Zipf's law fit, Heaps' law fit, character/token entropies, hapax
fraction, sentence-length profile — with a heuristic verdict for each
check. Human languages occupy known bands on all of these; ciphers,
random noise, and non-linguistic notation tend to fall outside.
"""

import math
from collections import Counter


def _loglog_fit(points):
    """Least-squares fit y = a + b*x on (log x, log y) points.

    Returns (slope, intercept, r_squared).
    """
    pts = [(math.log(x), math.log(y)) for x, y in points if x > 0 and y > 0]
    n = len(pts)
    if n < 3:
        return 0.0, 0.0, 0.0
    sx = sum(p[0] for p in pts)
    sy = sum(p[1] for p in pts)
    sxx = sum(p[0] * p[0] for p in pts)
    sxy = sum(p[0] * p[1] for p in pts)
    syy = sum(p[1] * p[1] for p in pts)
    denom = n * sxx - sx * sx
    if denom == 0:
        return 0.0, 0.0, 0.0
    slope = (n * sxy - sx * sy) / denom
    intercept = (sy - slope * sx) / n
    ss_tot = syy - sy * sy / n
    ss_res = sum((y - (intercept + slope * x)) ** 2 for x, y in pts)
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 0 else 0.0
    return slope, intercept, r2


def entropy(counter: Counter):
    """Plug-in Shannon entropy in bits."""
    total = sum(counter.values())
    if total == 0:
        return 0.0
    h = 0.0
    for c in counter.values():
        p = c / total
        h -= p * math.log2(p)
    return h


def conditional_entropy(bigrams: Counter, unigrams: Counter):
    """H(next | prev) = H(bigram) - H(prev), plug-in estimate in bits."""
    return entropy(bigrams) - entropy(unigrams)


def zipf(type_counts: Counter, max_rank=1000):
    freqs = sorted(type_counts.values(), reverse=True)[:max_rank]
    points = [(rank + 1, f) for rank, f in enumerate(freqs)]
    slope, intercept, r2 = _loglog_fit(points)
    return {"slope": slope, "r_squared": r2, "ranks_used": len(points)}

def heaps(sentences, checkpoints=40):
    """Heaps' law: vocabulary growth V = K * N^beta."""
    seen = set()
    n = 0
    points = []
    total = sum(len(s) for s in sentences)
    if total == 0:
        return {"beta": 0.0, "r_squared": 0.0}
    step = max(1, total // checkpoints)
    next_cp = step
    for s in sentences:
        for t in s:
            n += 1
            seen.add(t)
            if n >= next_cp:
                points.append((n, len(seen)))
                next_cp += step
    slope, intercept, r2 = _loglog_fit(points)
    return {"beta": slope, "r_squared": r2}


def char_stats(corpus):
    uni = Counter()
    bi = Counter()
    for line in corpus.char_stream(sep=" "):
        prev = None
        for ch in line:
            uni[ch] += 1
            if prev is not None:
                bi[(prev, ch)] += 1
            prev = ch
    h1 = entropy(uni)
    h_cond = conditional_entropy(bi, uni) if bi else 0.0
    return {
        "alphabet_size": len(uni),
        "unigram_entropy_bits": h1,
        "conditional_entropy_bits": h_cond,
        "entropy_drop": h1 - h_cond,
    }


def token_stats(corpus):
    counts = corpus.type_counts()
    total = sum(counts.values())
    hapax = sum(1 for c in counts.values() if c == 1)
    uni = counts
    bi = Counter()
    for s in corpus.sentences:
        for a, b in zip(s, s[1:]):
            bi[(a, b)] += 1
    h1 = entropy(uni)
    h_cond = conditional_entropy(bi, uni) if bi else 0.0
    lens = [len(s) for s in corpus.sentences]
    mean_len = sum(lens) / len(lens) if lens else 0.0
    var = sum((l - mean_len) ** 2 for l in lens) / len(lens) if lens else 0.0
    tok_lens = [len(t) for t in corpus.tokens]
    mean_tok_len = sum(tok_lens) / len(tok_lens) if tok_lens else 0.0
    return {
        "sentences": len(corpus.sentences),
        "tokens": total,
        "types": len(counts),
        "type_token_ratio": len(counts) / total if total else 0.0,
        "hapax_fraction_of_types": hapax / len(counts) if counts else 0.0,
        "unigram_entropy_bits": h1,
        "conditional_entropy_bits": h_cond,
        "mean_sentence_length": mean_len,
        "sd_sentence_length": math.sqrt(var),
        "mean_token_length": mean_tok_len,
    }


def verdicts(z, hp, cs, ts):
    """Heuristic language-likeness checks. Each: (name, status, comment).

    Status is 'pass' / 'warn' / 'info'. These are screening heuristics,
    not proofs — small corpora and unusual scripts can shift the bands.
    """
    out = []

    s = z["slope"]
    if -1.6 <= s <= -0.7:
        out.append(("Zipf slope", "pass",
                    f"slope {s:.2f} (R²={z['r_squared']:.3f}) — natural languages sit near -1"))
    else:
        out.append(("Zipf slope", "warn",
                    f"slope {s:.2f} (R²={z['r_squared']:.3f}) — outside the typical -0.7..-1.6 band"))

    b = hp["beta"]
    if 0.4 <= b <= 0.9:
        out.append(("Heaps exponent", "pass",
                    f"beta {b:.2f} — vocabulary growth in the natural-language band (0.4-0.9)"))
    else:
        out.append(("Heaps exponent", "warn",
                    f"beta {b:.2f} — unusual vocabulary growth (natural band 0.4-0.9)"))

    drop = cs["entropy_drop"]
    if drop >= 0.5:
        out.append(("Character predictability", "pass",
                    f"conditional entropy {cs['conditional_entropy_bits']:.2f} bits vs unigram "
                    f"{cs['unigram_entropy_bits']:.2f} — strong sequential structure (drop {drop:.2f} bits)"))
    else:
        out.append(("Character predictability", "warn",
                    f"entropy barely drops given context ({drop:.2f} bits) — "
                    "characters look near-independent, as in random noise or strong encryption"))

    hx = ts["hapax_fraction_of_types"]
    if 0.25 <= hx <= 0.7:
        out.append(("Hapax fraction", "pass",
                    f"{hx:.0%} of word types occur once — typical for natural text"))
    else:
        out.append(("Hapax fraction", "info",
                    f"{hx:.0%} of word types occur once — outside the common 25-70% band; "
                    "very low suggests a small closed vocabulary, very high suggests heavy morphology or noise"))

    out.append(("Scale", "info",
                f"{ts['sentences']} sentences, {ts['tokens']} tokens, {ts['types']} types — "
                "decipherment confidence grows with corpus size; results below are provisional at small scales"))
    return out


def run(corpus):
    counts = corpus.type_counts()
    z = zipf(counts)
    hp = heaps(corpus.sentences)
    cs = char_stats(corpus)
    ts = token_stats(corpus)
    return {
        "zipf": z,
        "heaps": hp,
        "char": cs,
        "token": ts,
        "verdicts": verdicts(z, hp, cs, ts),
        "top_words": counts.most_common(30),
    }
