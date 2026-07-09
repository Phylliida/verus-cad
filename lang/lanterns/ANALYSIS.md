# The Lantern Puzzle — Analysis

The records in this bundle are the nightly blink-exchanges of the Hollow Valley's ghost-lanterns — drifting, sentient lights that answer one another across the dark. What follows is a full pass over that data (README steps 0–5). **Steps 0–4 are solved.** For step 5, the *structure* of the lantern system is fully characterized; the literal meaning of the open-vocabulary words is shown to be unrecoverable from the data alone.

Files in this bundle:
- `README.md`, `field_guide.md`, `manifest.json` — the problem statement and column meanings.
- `catalog.csv`, `flares.csv` — the data (join on `flare_id`).
- `ANALYSIS.md` (this file) — findings.
- `CLAIMS.md` — a numbers-only checklist a second reader can verify independently.

---

## 0. Setup
- Verified both files match the manifest's counts (12,559 flares; 67,503 flashes; 8,719 RIDGE + 3,840 LAMP; 48 nights; 35 glyphs; 18 shapes).
- Joined `catalog.csv` ↔ `flares.csv` on `flare_id`; reconstructed each flare's ordered list of dark-gaps (`dark_s` by `flash_index`).

## 1. The alphabet
- Each flare is a run of identical flashes; **all the information is in the dark gaps between them.**
- The gaps are **quantized**: within a flare they land on integer multiples of a small base unit, with "long" gaps ≈ 2× "short."
- So a glyph = **(number of flashes) + (which gaps are long)**. The families:
  - **R** — all gaps equal (even spacing)
  - **i** — last gap doubled (an elongated tail)
  - **D** — long gaps at the front (front-loaded)
  - **a+b+c** — flashes bundled into runs of *a, b, c* (long gaps *between* the groups)
- The three extra dials (overall length/pace; a gentle tempo drift; an optional flourish flash) modify a glyph's delivery without changing its identity. The 35 glyphs = the 18 shapes × these variants.
- `*-SMUDGE` glyphs are ordinary flares corrupted by one anomalous gap (a zero-length or over-long dark); safe to discard.

## 2. Bridging the two logs (step 4)
- **RIDGE** = glyph + region/cluster/date, but no within-session order (each date+cluster is an unordered set).
- **LAMP** = beacon + exact time (orderable by `night`, `since_dusk_s`), but no glyph.
- Matched each LAMP shape to a RIDGE glyph by comparing their gap-profiles (~86% recoverable with a nearest-profile rule), so LAMP flares can be labelled with glyphs.

## 3. Who & where (step 3)
- **Two regions with distinct glyph-vocabularies.** R1 (clusters A, D, F, J, N, R, S, T, U, V) is dominated by `1+1+3` and `5R1`. R2 (clusters K, P, ZZZ) is ~two-thirds a single glyph, `5R3`.
- **~35 labelled beacons** in RIDGE (numbered ~5125–6070, plus a lone `9999` in cluster `ZZZ` acting as an end-marker), each with a characteristic glyph.
- In LAMP, beacons 1–4 dominate and form an **answer-chain 1↔2↔3↔4** (each mostly trades with its neighbour).

## 4. Turn-taking & the timing (steps 2 & 5)
- Ordered by `(night, since_dusk_s)`, several nights carry the **same exchange reproduced on a second night** — e.g. N-025 and N-027 have near-identical inter-flare timing (correlation 0.99998). Reproduction ⇒ deliberate, repeated content.
- The content is in **how fast a beacon answers**: the delay before an answer, divided by a fixed unit (~0.078 s), is a whole number 1–26 that reads as a letter A–Z. Clean checks: a **1.57 s** delay → 20 = **T**; a **1.96 s** delay → 25 = **Y** (both land on exact integers).
- Read the answers **in time order.** Near-instant answers (< ~0.18 s) are two beacons settling into a shared rhythm, not letters; removing them makes the reproduced pairs agree.
- Recovered a corpus of short "words" the lanterns trade — e.g. `GETY`, `VIEGD`, `RMMPHH`, `QJGI`, `FIGHGIL`, `CGHX`.

## 5. Grammar of the exchanges
- Words split cleanly by position:
  - short recurring words (`I`, `ED` at the start; `RL`, `W`, `F` at the end) behave like **function words / particles**;
  - longer, mostly-unique words behave like an **open vocabulary**.
- Each night is **framed**: an opening word early, then a closing word much later at the end — e.g. `GETY` opens N-041 and `VIEGD` closes it ~670 s later. Grammar: **[opening] … [content] … [closing]**.

## 6. Limit on literal meaning
The open-vocabulary words **cannot be read out to plain meaning from the data alone**: they are mostly unique (appear once), and their letters (`RMMPHH`, `QJGI`, …) don't resolve to real words under any simple re-mapping or reversal. They behave like proper names / an open lexicon. An early attempt to gloss them into a "dictionary" was **over-fitting**: the *structure* below is solid, but the literal content of the content-words is not fixed by the data.

## 7. Structural properties recovered from the data
- **Non-random.** Knowing the previous flare cuts per-flare uncertainty ~38% (from 2.08 to 1.28 bits). Statistical dependence between flares decays *slowly* with separation — fit far better by a power law (R² ≈ 0.93) than an exponential (0.70): the mark of **long-range, hierarchical structure**, not a short-memory pattern.
- **A four-level hierarchy:** unit → **phrase** (a unit repeated, e.g. `1+1+3` three-in-a-row, 1,433×) → **theme** (a stretch dominated by one phrase, with `1+1+3` as a recurring hub) → **nightly cycle** (a stereotyped, repeating order of themes — e.g. N-001 beacon 1 runs a five-theme cycle twice).
- **Two non-overlapping regional variants.** R1 vs R2 differ ~5× more than any year-to-year change within R1; R2's characteristic glyph `5R3` never appears in R1 — even in the years (2008, 2016) both were recorded. The two variants don't mix.
- **Gradual change over the dated span.** RIDGE dates run 2005–2016; R1's glyph-composition shifts gradually year to year, with no sudden wholesale replacement.
- **Night beats beacon.** A beacon's glyph-distribution is set by *which night* it flared, not *which beacon* it is: two different beacons on the same night are much closer (distance 0.229) than the same beacon on different nights (0.427 ≈ two unrelated beacons at 0.422). The pattern is a shared, time-varying property of the night.
- **Neighbour effect.** Within a single beacon, flares run ~10% longer when another beacon is active nearby (beacon 1: 0.81→0.91 s; beacon 2: 0.83→0.92 s) and the glyph-variety narrows.

## Bottom line
The lantern data is a genuine, richly-structured system: a finite alphabet modulated by prosody; two logs that bridge on shared shapes; two distinct, non-overlapping regional variants; gradual change across the dated span; a full unit→phrase→theme→cycle hierarchy with long-range structure; night-level over beacon-level regularity; and a neighbour effect on delivery — each backed by a computed number. The single thing **not** fixed by the data is the literal meaning of the open-vocabulary words; that would require information outside the dataset.
