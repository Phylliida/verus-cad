# Lantern Analysis — Claims to Verify

Each item states a claim, the statistic that supports it, and where/how to check it against `catalog.csv` + `flares.csv`. Join on `flare_id`; rebuild each flare's ordered gap list from `flares.csv` (`dark_s` by `flash_index`, last flash blank).

| # | Claim | Statistic | How to check |
|---|-------|-----------|--------------|
| 1 | Files are intact | 12,559 flares; 67,503 flashes; 8,719 RIDGE / 3,840 LAMP; 35 glyphs; 18 shapes | Row counts; `nunique` of `glyph`, `shape_id`, `beacon_id`, `night` vs `manifest.json` |
| 2 | Within-flare gaps are quantized, long ≈ 2× short | For `glyph=1+1+3`, the two larger gaps ≈ 2.0–2.2× the two smaller | Per-flare gap ratios for `1+1+3` |
| 3 | Glyph = flash-count + long-gap positions | R even; **i** last gap ~2×; **D** leading gaps ~2×; **a+b+c** grouped | Mean normalized gap-profile per glyph |
| 4 | Shape↔glyph bridge works | Nearest gap-profile rule recovers the RIDGE glyph ~85–86% | Self-classification accuracy on RIDGE |
| 5 | Two regional variants | R1 top: `1+1+3`/`5R1`; R2 ~66% `5R3`; region distribution-distance ≈ 0.76 | Glyph shares by `region`; Jensen–Shannon distance R1 vs R2 |
| 6 | Some nights are reproduced | N-025 vs N-027 inter-flare timing correlation ≈ 0.99998 (also 016/021, 017/022, 041/042, 018/023, 015/020) | Correlate `diff(since_dusk_s)` between each paired night |
| 7 | Answer-delay → letter, unit ≈ 0.078 s | Delays land on integer multiples; e.g. 1.57 s → 20 (T), 1.96 s → 25 (Y) | Cross-beacon answer delays in [0.18, 2.1] s ÷ 0.078; check nearness to integers |
| 8 | Message grammar (openers/closers) | `I`, `ED` start-biased; `RL`, `W`, `F` end-biased (position within the night) | First-message vs last-message word counts per night |
| 9 | Sequence is predictable | Per-flare uncertainty 2.08 → 1.28 bits given the previous unit | Unigram vs first-order conditional uncertainty on LAMP `shape_id` streams |
| 10 | Long-range structure | Dependence-vs-separation fits power law (R² ≈ 0.93) > exponential (0.70); stays above a shuffled baseline out to ~6–8 apart | Statistical dependence at lags 1..30 on per-beacon LAMP sequences vs shuffles |
| 11 | Four-level hierarchy | Top repeated 3-unit motif `1+1+3`×3 (1,433×); themes = dominant-unit runs; cycles repeat in long bouts (e.g. N-001 beacon 1) | 3-gram counts; theme-segment the longest per-beacon bouts |
| 12 | Variants don't mix | `5R3` share in R1 ≈ 0.2%, unchanged in overlap years 2008 & 2016 | `5R3` fraction within R1 per year |
| 13 | Gradual change over dates | Consecutive-year R1 distribution-distance small (0.05–0.17); no jump | Per-year R1 glyph distributions; distances between consecutive years |
| 14 | Night beats beacon | Same-night/diff-beacon distance 0.229 < same-beacon/diff-night 0.427 ≈ diff-both 0.422 | Pairwise glyph-distribution distances, grouped by (same night? / same beacon?) |
| 15 | Neighbour effect | Within-beacon flare length rises with a nearby other beacon (beacon 1: 0.81→0.91 s; beacon 2: 0.83→0.92 s) | Per-flare `flare_len_s` split by whether another beacon flared within ±15 s |

**Note on step 5.** Claims 1–15 are properties of the data and are independently checkable. The *literal meaning* of the open-vocabulary words (`GETY`, `RMMPHH`, …) is **not** among them: those words are mostly unique and do not resolve to real words under simple transformations, so their content is not determined by the dataset.
