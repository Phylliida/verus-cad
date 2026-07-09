# xenolang — decipherment toolkit for unknown languages

Pure-stdlib Python tools for attacking an untranslated corpus with no
bilingual text: corpus statistics, word segmentation, morphology
induction, distributional word classes, and syntax probes. Built for
the "few thousand sentences of an alien language" scenario.

What it recovers is **structure** — word classes, inflection paradigms,
word order, formulae. It cannot recover *meaning*; that always needs an
external anchor (names, numerals, accompanying context, or a related
language). The report points at the most promising anchor candidates.

## Input format

One sentence per line, UTF-8. If the language marks word boundaries,
separate tokens with spaces. If it doesn't, just give raw character
lines — the pipeline detects this and induces word boundaries itself.

## Usage

```bash
# full pipeline: writes report.md + JSON artifacts to analysis/
python3 -m xenolang report corpus.txt -o analysis

# individual stages
python3 -m xenolang stats corpus.txt      # is it language-like?
python3 -m xenolang segment corpus.txt    # induce word boundaries
python3 -m xenolang morph corpus.txt      # affixes + paradigms (JSON)
python3 -m xenolang cluster corpus.txt    # word classes (JSON)
```

Useful flags for `report`: `-k N` cluster count (default 20; raise for
morphologically rich languages), `--segment yes|no|auto`, `--lowercase`.

## Pipeline

1. **stats** — Zipf slope, Heaps exponent, character/token entropies,
   hapax fraction. Screens language from noise/cipher/notation.
2. **segment** (only if no word boundaries) — branching-entropy boundary
   scoring, threshold chosen by minimum description length, then greedy
   MDL refinement with token-level boundary flips and Morfessor-style
   type-level merge/split moves.
3. **cluster** — PPMI vectors over left/right neighbors, spherical
   k-means with centroids initialized at the most frequent words
   (deterministic). Clusters approximate parts of speech. Also emits a
   substitution grid: the most mutually-interchangeable word pairs.
4. **morph** — Goldsmith-style signature induction: suffixes/prefixes
   validated by stems that occur with multiple affixes, grouped into
   candidate inflection paradigms; calls the language suffixing,
   prefixing, mixed, or isolating.
5. **typology** — cluster transition probabilities, sentence-edge
   affinities, high-PMI collocations, repeated formulae, and
   numeral-like closed classes (attach to one open class, avoid each
   other).

## Validation

`genlang.py` generates a synthetic agglutinative SOV language
(ergative-absolutive case, suffixing, Zipfian lexicon) with full ground
truth; `eval_synthetic.py` scores the toolkit against it:

```bash
python3 genlang.py -n 3000        # writes testdata/
python3 eval_synthetic.py testdata
```

Scores on the 3000-sentence benchmark (14k tokens, 571 surface types):

| metric | score |
|---|---|
| word-class purity vs true POS (k=20) | 88% |
| true-suffix recall (7/7, incl. composite chains) | 100% |
| affixation direction call | correct |
| word-boundary F1 on unsegmented text | 85% |
| morph-boundary precision of induced cuts | 97% |

Caveats: the segmenter converges to a morph-level lexicon when that
compresses better than whole words (linguistically defensible, but
downstream morphology then sees suffixes as separate tokens). All
verdict bands in `stats` are heuristics calibrated on human languages —
a genuinely alien language could legitimately fall outside them.
