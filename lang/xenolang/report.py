"""Full pipeline: stats → (segment) → clusters → morphology → syntax → report.md."""

import json
import os

from . import corpus as corpus_mod
from . import stats as stats_mod
from . import segment as segment_mod
from . import morph as morph_mod
from . import cluster as cluster_mod
from . import typology as typology_mod

STATUS_MARK = {"pass": "✅", "warn": "⚠️", "info": "ℹ️"}


def _fmt_verdicts(vs):
    lines = []
    for name, status, comment in vs:
        lines.append(f"- {STATUS_MARK.get(status, '')} **{name}** — {comment}")
    return "\n".join(lines)


def _fmt_clusters(clusters, max_members=14):
    lines = []
    for c in clusters:
        members = ", ".join(f"`{w}`" for w in c["members"][:max_members])
        more = f" … (+{c['n_types'] - max_members} more)" if c["n_types"] > max_members else ""
        lines.append(
            f"**C{c['id']}** — {c['n_types']} types, {c['token_share']:.1%} of tokens, "
            f"mean position {c['mean_norm_position']:.2f}, "
            f"P(initial)={c['p_sentence_initial']:.2f}, P(final)={c['p_sentence_final']:.2f}\n"
            f"  {members}{more}\n"
        )
    return "\n".join(lines)


def _fmt_signatures(sigs, max_sigs=10, max_stems=8):
    lines = []
    for s in sigs[:max_sigs]:
        affixes = " / ".join(f"-{a}" if a != morph_mod.NULL else "-∅" for a in s["affixes"])
        stems = ", ".join(f"`{st}`" for st in s["stems"][:max_stems])
        more = f" … (+{s['n_stems'] - max_stems})" if s["n_stems"] > max_stems else ""
        lines.append(f"- **{{{affixes}}}** × {s['n_stems']} stems (robustness {s['robustness']}): {stems}{more}")
    return "\n".join(lines)


def build_report(path, outdir, k=20, segment_mode="auto", lowercase=False):
    os.makedirs(outdir, exist_ok=True)
    artifacts = {}

    # ---- load, possibly segmenting first
    seg_info = None
    ws_frac = corpus_mod.whitespace_fraction(path)
    need_seg = (segment_mode == "yes") or (segment_mode == "auto" and ws_frac < 0.5)
    if need_seg:
        with open(path, encoding="utf-8") as f:
            raw_lines = [l.strip().replace(" ", "") for l in f if l.strip()]
        seg_info = segment_mod.run(raw_lines)
        seg_path = os.path.join(outdir, "segmented.txt")
        with open(seg_path, "w", encoding="utf-8") as f:
            for toks in seg_info["segmented"]:
                f.write(" ".join(toks) + "\n")
        corp = corpus_mod.load(seg_path, lowercase=lowercase)
    else:
        corp = corpus_mod.load(path, lowercase=lowercase)

    # ---- analyses
    st = stats_mod.run(corp)
    cl = cluster_mod.run(corp, k=k)
    mo = morph_mod.run(corp.type_counts())
    ty = typology_mod.run(corp, cl)

    artifacts["stats.json"] = {k2: v for k2, v in st.items() if k2 != "verdicts"}
    artifacts["clusters.json"] = {
        "clusters": cl["clusters"],
        "substitution_grid": cl["substitution_grid"],
    }
    artifacts["morphology.json"] = mo
    artifacts["syntax.json"] = ty
    for name, obj in artifacts.items():
        with open(os.path.join(outdir, name), "w", encoding="utf-8") as f:
            json.dump(obj, f, ensure_ascii=False, indent=1, default=str)

    # ---- report
    ts = st["token"]
    r = []
    r.append("# Decipherment report\n")
    r.append(f"Corpus: `{os.path.abspath(path)}`\n")

    r.append("## 1. Is it language-like?\n")
    r.append(_fmt_verdicts(st["verdicts"]))
    r.append("\nTop 30 tokens: " + ", ".join(f"`{w}`({c})" for w, c in st["top_words"]) + "\n")

    r.append("## 2. Segmentation\n")
    if seg_info is None:
        r.append("Word boundaries present in the input; no segmentation needed.\n")
    else:
        r.append(
            f"No word boundaries detected in the input (whitespace on {ws_frac:.0%} of lines), "
            f"so words were induced by branching entropy + MDL.\n\n"
            f"- boundary threshold: {seg_info['threshold']:.2f} bits\n"
            f"- induced lexicon: {seg_info['lexicon_size']} types\n"
            f"- mean induced word length: {seg_info['mean_word_length']:.2f} chars\n\n"
            f"Segmented corpus written to `segmented.txt`. **All results below depend on "
            f"this segmentation being right — treat with extra caution.**\n"
        )

    r.append("## 3. Word classes (distributional clusters)\n")
    r.append(
        f"{cl['n_vectorized']} word types clustered into {k} classes by their left/right "
        "neighbor profiles (PPMI + spherical k-means). Clusters approximate parts of speech; "
        "closed classes (few types, many tokens) are usually grammar words, open classes "
        "content words.\n"
    )
    r.append(_fmt_clusters(cl["clusters"]))

    r.append("### Substitution grid (most interchangeable word pairs)\n")
    r.append("Word pairs with near-identical contexts — the classic decipherment grid. "
             "These likely share a category and differ in one semantic feature:\n")
    for p in cl["substitution_grid"][:25]:
        r.append(f"- `{p['a']}` ≈ `{p['b']}` (cosine {p['cosine']})")
    r.append("")

    r.append("## 4. Morphology\n")
    r.append(f"Affixation profile: **{mo['direction']}**\n")
    r.append("### Top suffix candidates\n")
    r.append(", ".join(f"`-{a}`({s})" for a, s in mo["suffix"]["affixes"][:20]) or "none")
    r.append("\n### Suffix signatures (candidate inflection paradigms)\n")
    r.append(_fmt_signatures(mo["suffix"]["signatures"]) or "none found")
    r.append("\n### Top prefix candidates\n")
    r.append(", ".join(f"`{a}-`({s})" for a, s in mo["prefix"]["affixes"][:20]) or "none")
    pre_sigs = _fmt_signatures(mo["prefix"]["signatures"], max_sigs=5)
    if pre_sigs:
        r.append("\n### Prefix signatures\n")
        r.append(pre_sigs)
    r.append("")

    r.append("## 5. Syntax probes\n")
    r.append("### Cluster profiles\n")
    for row in ty["edge_profile"]:
        ex = ", ".join(f"`{w}`" for w in row["examples"])
        r.append(f"- **C{row['id']}** ({row['class_type']}, {row['n_types']} types, "
                 f"{row['token_share']:.1%} tokens): {row['position_habit']} — {ex}")
    def _clabel(c):
        return {"<s>": "START", "</s>": "END"}.get(c, f"C{c}")

    r.append("\n### Strongest cluster transitions (P(to | from) ≥ 0.05)\n")
    for t in ty["transitions"][:20]:
        r.append(f"- {_clabel(t['from'])} → {_clabel(t['to'])}: p={t['p']} (n={t['count']})")
    r.append("\n### High-PMI bigrams (collocations)\n")
    for b in ty["pmi_bigrams"][:20]:
        r.append(f"- `{b['a']} {b['b']}` (PMI {b['pmi']}, n={b['count']})")
    if ty["formulae"]:
        r.append("\n### Repeated formulae\n")
        for fm in ty["formulae"]:
            r.append(f"- \"`{fm['phrase']}`\" ×{fm['count']}")
    anch = ty["anchors"]["numeral_like_clusters"]
    if anch:
        r.append("\n### Numeral-like candidates\n")
        r.append("Closed classes that attach to one open class and avoid each other — "
                 "the distributional fingerprint of numerals/quantifiers/determiners:\n")
        for a in anch:
            r.append(f"- C{a['cluster']}: " + ", ".join(f"`{w}`" for w in a["members"]) +
                     f" (open-adjacency {a['open_adjacency']}, self-adjacency {a['self_adjacency']})")
    r.append("")

    r.append("## 6. What this can and cannot tell you\n")
    r.append(
        "Everything above is *structure*: word classes, paradigms, word order, formulae. "
        "None of it assigns meaning. To go further you need an anchor — proper names, "
        "numerals tied to countable context, images or objects the texts accompany, or a "
        "related language. The numeral-like candidates and formulae above are the best "
        "places to start looking.\n"
    )

    report_path = os.path.join(outdir, "report.md")
    with open(report_path, "w", encoding="utf-8") as f:
        f.write("\n".join(r))
    return report_path
