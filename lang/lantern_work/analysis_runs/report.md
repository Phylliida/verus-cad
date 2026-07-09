# Decipherment report

Corpus: `/home/bepis/prog/verus-cad/lang/lantern_work/lamp_runs.txt`

## 1. Is it language-like?

- ✅ **Zipf slope** — slope -1.40 (R²=0.960) — natural languages sit near -1
- ✅ **Heaps exponent** — beta 0.51 — vocabulary growth in the natural-language band (0.4-0.9)
- ✅ **Character predictability** — conditional entropy 1.58 bits vs unigram 2.89 — strong sequential structure (drop 1.31 bits)
- ✅ **Hapax fraction** — 26% of word types occur once — typical for natural text
- ℹ️ **Scale** — 116 sentences, 1438 tokens, 108 types — decipherment confidence grows with corpus size; results below are provisional at small scales

Top 30 tokens: `2x1`(257), `4x1`(153), `0x1`(140), `2x2`(88), `17x1`(83), `16Fx1`(53), `2x3`(45), `7x1`(41), `13x1`(27), `9x1`(25), `0x2`(24), `16x1`(23), `2x4`(23), `4x2`(21), `5x1`(20), `10Fx1`(20), `11x1`(20), `6x1`(18), `4x3`(18), `17x2`(15), `2Fx1`(14), `8x1`(14), `17Fx1`(13), `2x5`(12), `2x6`(10), `11Fx1`(9), `2x8`(9), `7Fx1`(9), `2x9`(9), `2x12`(9)

## 2. Segmentation

Word boundaries present in the input; no segmentation needed.

## 3. Word classes (distributional clusters)

80 word types clustered into 10 classes by their left/right neighbor profiles (PPMI + spherical k-means). Clusters approximate parts of speech; closed classes (few types, many tokens) are usually grammar words, open classes content words.

**C0** — 6 types, 22.4% of tokens, mean position 0.53, P(initial)=0.03, P(final)=0.04
  `2x1`, `0x2`, `10Fx1`, `2x6`, `2x8`, `4x9`

**C1** — 6 types, 13.9% of tokens, mean position 0.47, P(initial)=0.04, P(final)=0.05
  `4x1`, `5x1`, `4x3`, `4x10`, `4x7`, `10x2`

**C2** — 5 types, 12.7% of tokens, mean position 0.51, P(initial)=0.03, P(final)=0.03
  `0x1`, `16x1`, `15x1`, `12x1`, `4x6`

**C4** — 10 types, 12.0% of tokens, mean position 0.50, P(initial)=0.10, P(final)=0.06
  `17x1`, `4x2`, `6x1`, `17x2`, `2Fx1`, `11Fx1`, `4x4`, `4x8`, `15x5`, `17x4`

**C6** — 19 types, 10.1% of tokens, mean position 0.50, P(initial)=0.14, P(final)=0.19
  `2x3`, `2x4`, `2x5`, `2x12`, `2x9`, `7Fx1`, `0x3`, `5x2`, `8Fx1`, `2x16`, `2x28`, `2x13`, `2x15`, `2x26` … (+5 more)

**C3** — 5 types, 7.6% of tokens, mean position 0.53, P(initial)=0.06, P(final)=0.12
  `2x2`, `2x7`, `4Fx1`, `2x20`, `2x21`

**C8** — 16 types, 6.5% of tokens, mean position 0.39, P(initial)=0.20, P(final)=0.12
  `13x1`, `8x1`, `10x1`, `8x2`, `14x1`, `13Fx1`, `13x3`, `11x2`, `2x10`, `14Fx1`, `11x3`, `13x2`, `14x2`, `17x3` … (+2 more)

**C9** — 8 types, 5.1% of tokens, mean position 0.47, P(initial)=0.16, P(final)=0.11
  `9x1`, `11x1`, `17Fx1`, `2x11`, `9Fx1`, `2x19`, `3x1`, `17x5`

**C5** — 3 types, 4.5% of tokens, mean position 0.51, P(initial)=0.08, P(final)=0.06
  `16Fx1`, `1x1`, `16x2`

**C7** — 2 types, 3.3% of tokens, mean position 0.61, P(initial)=0.04, P(final)=0.11
  `7x1`, `0x4`

### Substitution grid (most interchangeable word pairs)

Word pairs with near-identical contexts — the classic decipherment grid. These likely share a category and differ in one semantic feature:

- `2x26` ≈ `7x2` (cosine 0.884)
- `9Fx1` ≈ `2x11` (cosine 0.604)
- `11Fx1` ≈ `11x3` (cosine 0.583)
- `2x11` ≈ `2x15` (cosine 0.557)
- `5x2` ≈ `2x16` (cosine 0.549)
- `17x3` ≈ `14x2` (cosine 0.514)
- `2x35` ≈ `7x2` (cosine 0.508)
- `13Fx1` ≈ `4x10` (cosine 0.497)
- `2x16` ≈ `2x13` (cosine 0.494)
- `4x10` ≈ `14Fx1` (cosine 0.49)
- `2x26` ≈ `2x35` (cosine 0.485)
- `2x16` ≈ `5x3` (cosine 0.473)
- `2x16` ≈ `7x2` (cosine 0.47)
- `2x16` ≈ `4x8` (cosine 0.469)
- `2x13` ≈ `7x2` (cosine 0.457)
- `13Fx1` ≈ `2x37` (cosine 0.457)
- `2x20` ≈ `2x28` (cosine 0.455)
- `2x10` ≈ `2x37` (cosine 0.452)
- `2x16` ≈ `2x26` (cosine 0.448)
- `13Fx1` ≈ `14Fx1` (cosine 0.444)
- `2x13` ≈ `2x35` (cosine 0.439)
- `2x13` ≈ `2x26` (cosine 0.436)
- `2x28` ≈ `2x15` (cosine 0.429)
- `2x11` ≈ `2x28` (cosine 0.428)
- `0x4` ≈ `5x2` (cosine 0.426)

## 4. Morphology

Affixation profile: **mixed prefixing/suffixing**

### Top suffix candidates

`-1`(11), `-3`(8), `-2`(8), `-5`(6), `-0`(5), `-4`(5), `-6`(5), `-8`(4), `-7`(3)

### Suffix signatures (candidate inflection paradigms)

- **{-1 / -2}** × 3 stems (robustness 13): `10x`, `14x`, `16x`

### Top prefix candidates

`1-`(18), `2-`(8), `4-`(7)

### Prefix signatures

- **{-1 / -∅}** × 18 stems (robustness 75): `0x1`, `0x2`, `1x1`, `2Fx1`, `2x1`, `2x3`, `3x1`, `4Fx1` … (+10)
- **{-2 / -4}** × 7 stems (robustness 33): `Fx1`, `x10`, `x13`, `x14`, `x15`, `x16`, `x26`

## 5. Syntax probes

### Cluster profiles

- **C0** (closed, 6 types, 22.4% tokens): medial — `2x1`, `0x2`, `10Fx1`, `2x6`, `2x8`, `4x9`
- **C1** (closed, 6 types, 13.9% tokens): medial — `4x1`, `5x1`, `4x3`, `4x10`, `4x7`, `10x2`
- **C2** (closed, 5 types, 12.7% tokens): medial — `0x1`, `16x1`, `15x1`, `12x1`, `4x6`
- **C4** (small, 10 types, 12.0% tokens): medial — `17x1`, `4x2`, `6x1`, `17x2`, `2Fx1`, `11Fx1`, `4x4`, `4x8`
- **C6** (small, 19 types, 10.1% tokens): medial — `2x3`, `2x4`, `2x5`, `2x12`, `2x9`, `7Fx1`, `0x3`, `5x2`
- **C3** (closed, 5 types, 7.6% tokens): medial — `2x2`, `2x7`, `4Fx1`, `2x20`, `2x21`
- **C8** (small, 16 types, 6.5% tokens): medial — `13x1`, `8x1`, `10x1`, `8x2`, `14x1`, `13Fx1`, `13x3`, `11x2`
- **C9** (small, 8 types, 5.1% tokens): medial — `9x1`, `11x1`, `17Fx1`, `2x11`, `9Fx1`, `2x19`, `3x1`, `17x5`
- **C5** (closed, 3 types, 4.5% tokens): medial — `16Fx1`, `1x1`, `16x2`
- **C7** (closed, 2 types, 3.3% tokens): medial — `7x1`, `0x4`

### Strongest cluster transitions (P(to | from) ≥ 0.05)

- C2 → C0: p=0.467 (n=84)
- C1 → C0: p=0.399 (n=79)
- C0 → C2: p=0.247 (n=78)
- C0 → C1: p=0.228 (n=72)
- C0 → C4: p=0.168 (n=53)
- C4 → C0: p=0.271 (n=46)
- C1 → C6: p=0.182 (n=36)
- C0 → C0: p=0.108 (n=34)
- C6 → C1: p=0.203 (n=29)
- C6 → END: p=0.189 (n=27)
- C3 → C1: p=0.231 (n=25)
- C4 → C3: p=0.147 (n=25)
- C4 → C2: p=0.135 (n=23)
- C9 → C4: p=0.297 (n=22)
- C1 → C3: p=0.111 (n=22)
- START → C6: p=0.194 (n=21)
- C6 → C5: p=0.147 (n=21)
- C4 → C8: p=0.118 (n=20)
- C5 → C6: p=0.306 (n=19)
- C3 → C4: p=0.176 (n=19)

### High-PMI bigrams (collocations)

- `4x1 2x8` (PMI 2.51, n=5)
- `4x1 5x1` (PMI 2.2, n=9)
- `4x1 2x5` (PMI 2.09, n=5)
- `9x1 2x2` (PMI 2.09, n=6)
- `2x2 4x2` (PMI 2.08, n=5)
- `5x1 4x1` (PMI 1.84, n=7)
- `4x1 2x4` (PMI 1.64, n=7)
- `2x1 0x1` (PMI 1.45, n=63)
- `2x3 4x1` (PMI 1.45, n=12)
- `2x1 4x3` (PMI 1.44, n=8)
- `0x1 2x1` (PMI 1.41, n=61)
- `2x2 7x1` (PMI 1.38, n=6)
- `2x2 17x1` (PMI 1.36, n=12)
- `2x1 0x2` (PMI 1.34, n=10)
- `4x1 2x3` (PMI 1.32, n=11)
- `2x1 10Fx1` (PMI 1.28, n=8)
- `0x1 16x1` (PMI 1.28, n=5)
- `17x1 2x2` (PMI 1.24, n=11)
- `0x2 2x1` (PMI 1.19, n=9)
- `2x2 4x1` (PMI 1.14, n=19)

### Repeated formulae

- "`2x1 0x1 2x1`" ×41
- "`0x1 2x1 0x1`" ×38
- "`2x1 0x1 2x1 0x1`" ×29
- "`4x1 2x1 4x1`" ×27
- "`0x1 2x1 0x1 2x1`" ×23
- "`2x1 4x1 2x1`" ×19
- "`2x1 0x1 2x1 0x1 2x1`" ×18
- "`0x1 2x1 0x1 2x1 0x1`" ×15
- "`2x2 4x1 2x1`" ×12
- "`4x1 2x1 4x1 2x1`" ×11
- "`2x2 4x1 2x1 4x1`" ×9
- "`0x1 2x1 0x2`" ×8
- "`2x1 17x1 2x1`" ×8
- "`2x1 4x1 2x2`" ×8
- "`4x1 2x2 4x1`" ×8
- "`17x1 2x2 17x1`" ×7
- "`4x1 2x2 4x1 2x1`" ×6
- "`2x1 4x1 2x1 4x1`" ×6
- "`0x1 17x1 0x1`" ×6
- "`4x1 5x1 4x1`" ×6

## 6. What this can and cannot tell you

Everything above is *structure*: word classes, paradigms, word order, formulae. None of it assigns meaning. To go further you need an anchor — proper names, numerals tied to countable context, images or objects the texts accompany, or a related language. The numeral-like candidates and formulae above are the best places to start looking.
