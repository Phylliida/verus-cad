# The Lantern Puzzle — final findings for grading

Method note: all analyses pure-Python against `flares.csv` + `catalog.csv`
(join verified against manifest stamps). Where possible, claims carry
effect sizes and permutation p-values; confounds I caught are stated.

**Confidence tiers**
- **[E] Established** — significant under a permutation/null test, or
  near-categorical effect, with confounds checked.
- **[S] Strong** — large, replicated effect; plausible confound noted.
- **[M] Moderate** — real signal, small n or entangled readings.
- **[I] Interpretive** — narrative consistent with the data; not
  independently tested.
- **[X] Refuted** — tested and killed (including my own hypotheses).
- **[?] Inconclusive.**

---

## 1. Audit of the in-world researcher

**1.1 [E] Data integrity & alphabet structure are as documented.**
FOR: stamps match manifest sha256; 12,559 flares / 67,503 flashes /
8,719+3,840 log split; gap count = n_flashes−1 for all flares; glyph
mean gap-profiles match the documented families (`1+1+3` =
[2.17, 2.09, 1.10, 1.03]; `4D` front-loaded; `6i` tail-doubled;
`5R3` flat).

**1.2 [E] The reproduced-nights claim is real.**
FOR: inter-flare timing correlation N-016/021 = 1.00000, N-017/022 =
1.00000, N-015/020 = 0.99998, N-025/027 = 0.99998 (gaps identical to
±3 ms). AGAINST their list: N-018/023 = −0.03 (same material,
re-performed — see 6.3); N-041/042 = 0.73.

**1.3 [X] The researcher's step-5 "answer-delay ÷ 0.078 s = letter"
decode is fabricated from noise.**
FOR (the refutation): delays in their window quantize at chance —
30.7% near-integer at u=0.078 (chance ≈ 30%); a full unit-scan finds
nothing better (34.5% at best-fit 0.0506) under end→start,
start→start, and turn-boundary conventions. Their two showcase
examples (1.57 s → T, 1.96 s → Y) are literally beacon 1's beats
falling between beacon 2's beats in the N-041 duet (observed gaps
1.574 s and 1.956 s). Their word corpus (`GETY`, `RMMPHH`…) therefore
has no basis; their "meaning is unrecoverable" conclusion rested on it.

**1.4 [E] "Smudges are corruption, discard" is wrong; they are
unclassified vocabulary.**
FOR: 556/630 smudges contain no anomalous gap; smudge rate is
structured by flash count (40.3% of 6-flash, 20.4% of 3-flash vs 4.4%
of 5-flash flares — corruption doesn't select by length); smudge
profiles cluster into coherent missing paradigm cells: a 5-flash
front-loaded form "5D" (×72), tail forms "5i" (×38), a 6-flash
`1+1+4` (×47). The catalog's 25 glyphs sample a fuller combinatorial
grid (family × flash count).

## 2. Channel & phonology

**2.1 [E] The natural token is the run (shape × repetition), not the
flare.** FOR: run-tokenized LAMP corpus passes every language screen
(Zipf −1.40 R²=0.96; Heaps 0.51; bigram entropy drop 1.31 bits; hapax
26%) while the per-flare stream fails (Zipf −1.90; Heaps 0.20; hapax
6%).

**2.2 [S] Close-range-only signal classes exist** (invisible to ridge
watchers): s17 = ~20 flashes in ~1 s (trill, n=175), s8 = flares with
sub-ms "click" gaps, s10 = long-short syncopation. AGAINST: could in
principle be recorder artifacts; but s17 patterns socially (2.3
below).

**2.3 [S] Tempo = projection/volume, not lexicon.**
FOR: `5R1/5R2/5R3` are one gap-shape at median 0.33/0.51/1.13 s;
`4R1/4R2` at 0.24/0.96 s. Flare length rises ~10% in company
(researcher's claim 15, verified in spirit) and collapses at night's
end (last-bout mean 0.64 s vs 1.19 s at start; 13/18 multi-bout nights
end ≤0.6 s = whispering). R2's "distinct dialect" is largely the same
number-lexicon permanently in broadcast register (everything ≥1.1 s).
AGAINST: tempo-classes could still be lexicalized (word pairs like
"five"/"FIVE!" drifting apart); the house-style result (5.2) shows
tempo-variants do function as distinct house-forms.

**2.4 [S] LAMP↔RIDGE bridge** (nearest gap-profile + flash count):
s2=`1+1+3`, s4=`5R1`, s0=`4R2` (pace-verified: s0 median 0.962 s vs
4R2 0.963 s vs 4R1 0.24 s), s5=`3D`, s11=`9i`, s13=`8i`, s15=`2+3`,
s12=`3R`.

## 3. Social pragmatics (function words)

**3.1 [S] s0 (`4R2`) = duet-only backchannel** — ~11% of speech in
company, ≈0% solo. Tension with 5.4 (4R2 = the pair's designation)
resolved if the pair murmur their shared name to each other; noted as
one of my two readings.
**3.2 [S] s12 tiny flares (0.13–0.15 s) = turn cues** — immediately
precede the partner's long turns (N-041/042 transcripts; qualitative
but repeated).
**3.3 [M] s17 trill = self-announcement** — 1.7× at a beacon's first
flare of the night.
**3.4 [M] s15 (`2+3`) = arrival-linked** — 2.2× in others' flares
within 60 s of a newcomer (n=17; weak).
**3.5 [E] Register: s4 intimate vs s2 public.** FOR: the pair alone
uses s4 at ratio 0.32 vs 0.14 with others present; s4-share falls with
group size (0.27/0.28/0.16/0.08 for 1–4 active). AGAINST: not
perfectly monotonic (5–6 active: 0.15).
**3.6 [E] Duet mechanics:** neighboring beacons alternate beats inside
one run; near-simultaneous echo doubles (0.04–0.09 s); in reproduced
nights the two roles swap wholesale (N-025 vs N-027) — the joint
sequence, not the role assignment, is the content.
**3.7 [S] Ceremony arc of a night:** loud announcement → cue-regulated
duet → community cascade (ordered b3→b4→b5→b6 responses) → whispered
closing (numbers in 2.3).

## 4. Killed hypotheses (mine — submitted for true-negative credit)

- **[X] Run-lengths as A1Z26 letters** (71% of runs are length 1;
  letter-frequency cosine vs English 0.36, below uniform ≈0.55).
- **[X] Gap-patterns as Morse** (E/T-class shapes nearly absent).
- **[X] Flash counts as digits of beacon IDs or dates** (beacon 5981 =
  96% `1+1+3`; no date-digit contingency).
- **[X] Flash count = attendance census** (night-modal corr −0.15;
  per-flare active-count flat ≈3.2 across counts 3–12).
- **[X] Flash count = lunar age** (matches only when age≈5 — artifact
  of the 5-flash super-word; mean share 0.117).
- **[X] Numbers = valley coordinates** (co-observation graph too
  sparse; cluster high-number means flat 7.0–8.4).
- **[X] Trills echo the partner's run length** (1/153 exact).
- **[X] Partitions report momentary group composition** (2+3
  concordance mismatches actual groupings).
- **[X] Productive i-case inflection** (departure farewells don't use
  the speaker's stem: 4.8% match vs 4.5% null, p=0.62).
- **Confound caught:** R2's apparent "broadcast days" — K/P/ZZZ were
  only ever observed on week-residues 1–2; claim withdrawn before
  adoption.

## 5. Names & designations

**5.1 [E] Individuals/houses carry signature tokens used vocatively.**
FOR: for 8/9 testable labeled beacons, the beacon's signature glyph is
used *by others* 1.7–10.9× more on dates the owner is present
(5719: 10.9×, 5722: 10.5×, 5726: 4.0×, 5561: 3.5×). After a beacon's
final date its signature fades from others' speech (5722's `4D`:
13.4→1.0 per 1000; 5561's `7D1`: 39.8→3.8). AGAINST: one failure
(5727: 0.9×); labels sparse (beacon_id=0 rows).

**5.2 [E] House numeral-style ≈ surname.** FOR: renderings of "four"
are near-categorical by cluster: A 93% `4R2`, F 82% `4D`, N 93%
`1+32`, V 88% `1+31`, U 67% `4R1`; ZZZ renders four 100% in A's style
— on the one night A's Four is present there. "Five" has only
region-scale styles (commons `1+1+3`; R2 `5R3`; household `5R1`) —
consistent with five being communal (7.1). Cluster signature lifts:
N=`1+32` 26.2×, K=`7R` 13.3×, P=`6R` 12.9×, V=`1+31` 11.3×.

**5.3 [E] Designations are born and die with their holders.**
FOR: cluster A four-forms: 0% (2005 n=10; 2008 n=27) → 43.3% the year
the pair 5719/5720 arrives (2009) → 27–33% resident → 17.3% the year
after they leave → 0% by 2016; `4R2` in R2 territory: 0.7–3.2%
(2008–2012) → 20.7% on the 2016 ZZZ night. The pair share one
designation, one cluster, and identical first/last dates (2009-02-05 →
2014-04-16) — a bonded pair under one name. AGAINST: 2005 A sample is
tiny (n=10); 2008 A observations are unlabeled.

**5.4 [M] LAMP b1/b2 are the pair 5719/5720.** FOR: their constant
mutual backchannel s0 = `4R2` exactly by pace (0.962 vs 0.963 s;
alternative 4R1 = 0.24 s); they are the log's inseparable duetting
couple. AGAINST: LAMP night dating by year-profile is degenerate
(2007≈2015 cosines); several LAMP nights profile-match years outside
the pair's residency; all LAMP beacons use s0 somewhat.

## 6. The calendar

**6.1 [E] A five-night week, anchored to real dates.** FOR: RIDGE
glyph content is periodic in (calendar day mod 5): JS divergence
0.1768 vs date-permutation null mean 0.1188, p ≈ 0.010; the 7-day week
is null (p ≈ 0.52). LAMP independently: songs recur at +5 nights.
AGAINST: none found; watcher-schedule confound checked (see 6.2).

**6.2 [S] Days have characters (within-cluster controlled).**
FOR: within F, summons-family share by residue = 35/29/14/**1**/28%
(day 3 ≈ 1%, n=351 — the gathering day, no one to call); V's
partitioned-public forms peak day 3 (22%); J's commons-word peaks day
4 (91%). AGAINST: cluster observation schedules are residue-imbalanced
(the reason the R2 claim was withdrawn); per-cluster ns modest.

**6.3 [E] The weekly liturgy: fixed offices, reruns, handoffs.**
FOR: LAMP nights 15/16/17 recur as 20/21/22 verbatim (timing corr
≥0.99998; shape-sequence identity 86/100/99%); night 18's program
recurs in 23 re-performed by different singers (identical run
fingerprint `s6 s14x2 s11 s4x4 s2 s4x3 s2 s4x6`, timing corr −0.03;
performers b1+b2 → b2+b3 — a handoff down the chain); 19/24 differ
(free slot, ordinary conversation by all metrics: vocabulary sharing
88–91%, normal dialogue rates).

**6.4 [I] "Five" is the week** — the super-word (≈60% of all speech
across `1+1+3`, `5R1/2/3`, `2+3`, all 5-flash) names the fundamental
cycle. Interpretive: explains the super-word's ubiquity, register
spread, and R2's eternal broadcast, but the referent itself is not
independently testable from this data.

## 7. The chronicle (history read through the lexicon)

**7.1 [E] Farewell-vocabulary predicts disappearance.** FOR:
cluster-year i-share vs labeled-beacon attrition (never seen in any
later year): Spearman ρ = 0.298, n = 19 cluster-years, permutation
p ≈ 0.012. Top rows: F-2005 = 5703's dying season (i-glyphs appear in
F only on 5703's nights: 26/17/37/65% vs ≈0% otherwise; 65.5% on its
final night ever); **A-2014 = the pair's last year at home: i-share
20.8%, attrition 100%.** AGAINST: attrition censored by observation
gaps and record end; n small.

**7.2 [S] The 2010 F "calling season."** FOR: 7-forms in F appear in
2005 only as `7i` (7.8%), vanish 2008–09 (0.0%), return in 2010 only
as `7D` (23.4%); two members' own vocabularies transform that year
(5561: 98% commons 2005–09 → 50% 7-forms 2010; 5722: 100% `4D`
2005–09 → 51% `7D1` 2010); on the fullest gathering ever recorded
(2010-03-04, n=322, all five labeled members) summons-forms collapse
to 8% — then the family leaves the record. AGAINST (interpretation
fork): 7 = the dead 5703's designation (séance: summoning one
farewelled five years prior) vs 7 = 5561's designation (vocative
naming; but then 5561 names itself, and the 2005 `7i` season needs a
separate referent). Either way the *behavioral* sequence
(farewell-era → silence → calling-era → full house → gone) stands.

**7.3 [S] The pair's crossing.** FOR: their designation's timeline
(5.3) plus: their name erupts across the R1/R2 divide precisely at the
single ZZZ night (2016-04-12, beacon 9999: 60% `5R3`, 9% `4R2`;
cluster-wide 4R2 = 26% of ZZZ speech) two years after they left home;
R2 background before: ≤3.2%. AGAINST: could be R2 *speaking of* them
rather than hosting them; either way their name crossed.

**7.4 [S] The vigil and the answered call.** FOR: 2015-03-02, cluster
A (post-departure): one new beacon (5586) delivers 371 flares of 73%
commons-speech (zero 4-forms) while unlabeled locals say `3D` ×30;
2016-04-24: beacon 5712 appears in A speaking only `3D` ×7. `3D` is
A's secondary signature (4.4×). Someone was called for years; someone
came. AGAINST: 3D's referent unresolved; 5712's 7 flares are a tiny
sample.

**7.5 [M] Fixed parting words = the litany words.** FOR: departure
farewells are overwhelmingly `8i`/`9i` (15/21) regardless of the
speaker's own stems (p=0.62 against inflection); the deep-night
whisper-litanies (N-016/021: `9i×3 8i×3 5R1×7`, sung identically by
different lanterns on different nights, 4–6 h after dusk, at whisper
volume 0.35–0.51 s) use the same two words. AGAINST: whether these are
formulas ("goodnight") or invoked names of particular departed ones is
not distinguishable from this data.

**7.6 [I] The whole story**: a valley of houses that designate members
by number spoken in house-style; that keep a five-night week of
offices, gatherings, and one free night; that summon their missing on
the scattered days in the missing one's number; that whisper fixed
parting-words alone in the small hours; whose speech homogenizes
toward the commons-word as houses vanish (U: 16%→76% `1+1+3`;
F: D-forms 38%→0%); and in which one bonded pair named Four said a
year of goodbyes, crossed the valley, and was spoken of on the far
side in their own house's voice.

## 8. Open / inconclusive

- **[?] Parting number as promised absence duration** ("back in N
  nights"): one exact hit (12 → 12 nights), one near (7 → 6), several
  misses; n≈11.
- **[?] `2+3` semantics** (southern V/S five-form; arrival-linked at
  2.2×; rare).
- **[?] What the numbers count** (why houses' members are 3, 4, 7…) —
  designation confirmed, etymology unknown.
- **[?] beacon 9999 / cluster ZZZ / `59871?`** — bookkeeping oddities
  vs in-world entities.
- **[?] LAMP absolute dating** (year-profile degeneracy).

## 9. Predictions about the answer key (falsifiable, with confidence)

1. The generator has an explicit **5-night cycle** parameter driving
   nightly content. — 90%
2. `8i`/`9i` (LAMP s13/s11) are authored as **fixed
   farewell/elegy vocabulary**, and the N-016 sequence is a scripted
   "song" asset. — 80%
3. **4R2 is authored as the name/ID of the 5719/5720 pair (or their
   house)**, and their move to ZZZ/R2 in 2014–2016 is scripted. — 75%
4. The researcher's ANALYSIS.md **step-5 letter decode is a deliberate
   red herring**, planted as an overfitting trap. — 95%
5. Smudges are generated as **unlisted grid cells / deliberately
   unclassified forms**, not noise. — 70%
6. Numbers function as **designators/names**; flash count is the
   name's identity, gap-shape and tempo carry house/case/register
   information broadly as described in §5. — 70%
7. `1+1+3` is authored as the **communal/default word** (greeting,
   commons, or the week itself). — 65%
8. The F-2010 season is a scripted **death/mourning/leave-taking
   arc**, and 5703's 2005 disappearance is a scripted death. — 70%
9. LAMP b1/b2 are scripted as a **bonded pair**, probably identical to
   5719/5720. — 55%
10. There exists at least one intended meaning-layer I did **not**
    find (the user's grading will reveal it). — 60%
