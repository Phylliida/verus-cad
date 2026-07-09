# Decipherment report

Corpus: `/home/bepis/prog/verus-cad/lang/testdata/corpus_nospace.txt`

## 1. Is it language-like?

- ✅ **Zipf slope** — slope -1.14 (R²=0.726) — natural languages sit near -1
- ⚠️ **Heaps exponent** — beta 0.09 — unusual vocabulary growth (natural band 0.4-0.9)
- ✅ **Character predictability** — conditional entropy 2.68 bits vs unigram 3.87 — strong sequential structure (drop 1.19 bits)
- ℹ️ **Hapax fraction** — 5% of word types occur once — outside the common 25-70% band; very low suggests a small closed vocabulary, very high suggests heavy morphology or noise
- ℹ️ **Scale** — 3000 sentences, 15348 tokens, 249 types — decipherment confidence grows with corpus size; results below are provisional at small scales

Top 30 tokens: `nu`(634), `ka`(466), `zirven`(463), `rakon`(433), `karos`(367), `kotur`(354), `nepiro`(324), `rateza`(299), `mo`(258), `rori`(250), `lela`(229), `koturne`(218), `ku`(217), `koturka`(216), `nukamir`(215), `pennon`(208), `nepihi`(207), `neka`(199), `ne`(195), `vesra`(191), `perlu`(175), `su`(174), `ros`(168), `numuro`(159), `mu`(156), `zalu`(153), `vesrane`(149), `ro`(141), `litakis`(141), `lusi`(140)

## 2. Segmentation

No word boundaries detected in the input (whitespace on 0% of lines), so words were induced by branching entropy + MDL.

- boundary threshold: 2.11 bits
- induced lexicon: 249 types
- mean induced word length: 5.26 chars

Segmented corpus written to `segmented.txt`. **All results below depend on this segmentation being right — treat with extra caution.**

## 3. Word classes (distributional clusters)

236 word types clustered into 20 classes by their left/right neighbor profiles (PPMI + spherical k-means). Clusters approximate parts of speech; closed classes (few types, many tokens) are usually grammar words, open classes content words.

**C6** — 68 types, 18.7% of tokens, mean position 0.98, P(initial)=0.00, P(final)=0.93
  `nepiro`, `nepihi`, `numuro`, `numuhi`, `nepiroku`, `narposro`, `nepihiku`, `mavezoro`, `kuzazenro`, `lezervoro`, `narposhi`, `kuzazenhi`, `numuroku`, `vepovurro` … (+54 more)

**C7** — 22 types, 7.9% of tokens, mean position 0.45, P(initial)=0.16, P(final)=0.00
  `rateza`, `litakis`, `lusi`, `pazi`, `ruri`, `titeki`, `viti`, `kapan`, `kiri`, `lirso`, `vutunna`, `noluvi`, `ketur`, `lero` … (+8 more)

**C1** — 5 types, 7.7% of tokens, mean position 0.39, P(initial)=0.00, P(final)=0.00
  `ka`, `karos`, `su`, `kanu`, `kara`

**C15** — 17 types, 7.6% of tokens, mean position 0.42, P(initial)=0.19, P(final)=0.00
  `pennon`, `zalu`, `vesrane`, `mavo`, `kunmin`, `rosru`, `voraran`, `soslotes`, `patu`, `lesa`, `lunlivu`, `kipinvu`, `posato`, `vesi` … (+3 more)

**C2** — 12 types, 7.4% of tokens, mean position 0.31, P(initial)=0.28, P(final)=0.00
  `zirven`, `tovo`, `tonpe`, `tarze`, `pinu`, `kasti`, `semu`, `murno`, `rinlon`, `sosva`, `nirlun`, `mime`

**C14** — 22 types, 7.0% of tokens, mean position 0.41, P(initial)=0.18, P(final)=0.00
  `nukamir`, `zola`, `larnu`, `nosa`, `menmer`, `kupo`, `memesa`, `nokurse`, `kulir`, `sinmonlu`, `sevi`, `rema`, `tila`, `male` … (+8 more)

**C3** — 7 types, 6.2% of tokens, mean position 0.26, P(initial)=0.38, P(final)=0.01
  `rakon`, `ro`, `ra`, `taser`, `piri`, `rasmi`, `ve`

**C5** — 14 types, 5.9% of tokens, mean position 0.56, P(initial)=0.11, P(final)=0.00
  `kotur`, `koturne`, `koturmu`, `koturmo`, `koturros`, `ratezane`, `pennonne`, `vesramu`, `meko`, `lusine`, `mavone`, `rurine`, `oros`, `rurim`

**C0** — 6 types, 5.1% of tokens, mean position 0.22, P(initial)=0.47, P(final)=0.00
  `nu`, `kanesika`, `kotursu`, `zaretaka`, `vutotaka`, `lu`

**C13** — 10 types, 4.5% of tokens, mean position 0.18, P(initial)=0.41, P(final)=0.00
  `koturka`, `koturkaros`, `vesraka`, `ratezaka`, `pennonka`, `vesrakaros`, `koturneka`, `lusika`, `kanesikaros`, `pazika`

**C17** — 7 types, 3.9% of tokens, mean position 0.52, P(initial)=0.00, P(final)=0.06
  `neka`, `mu`, `nekaros`, `nemu`, `nesu`, `nenepihi`, `inesu`

**C10** — 6 types, 3.8% of tokens, mean position 0.00, P(initial)=1.00, P(final)=0.00
  `lela`, `monla`, `pinzi`, `sursi`, `loros`, `zanto`

**C9** — 4 types, 3.7% of tokens, mean position 0.30, P(initial)=0.30, P(final)=0.00
  `rori`, `perlu`, `maku`, `ripi`

**C8** — 5 types, 3.5% of tokens, mean position 0.65, P(initial)=0.02, P(final)=0.00
  `mo`, `ros`, `neros`, `nemo`, `mopipe`

**C19** — 5 types, 2.1% of tokens, mean position 0.50, P(initial)=0.21, P(final)=0.00
  `vesra`, `nisvi`, `kanesi`, `vesraros`, `zalune`

**C12** — 1 types, 1.4% of tokens, mean position 1.00, P(initial)=0.00, P(final)=1.00
  `ku`

**C18** — 1 types, 1.3% of tokens, mean position 0.74, P(initial)=0.00, P(final)=0.00
  `ne`

**C11** — 11 types, 1.2% of tokens, mean position 0.09, P(initial)=0.73, P(final)=0.00
  `tizine`, `vistates`, `zareta`, `pazisin`, `kenunri`, `namaris`, `zesulu`, `tesvonrur`, `vesine`, `tenono`, `vutota`

**C4** — 4 types, 0.6% of tokens, mean position 0.90, P(initial)=0.00, P(final)=0.80
  `roku`, `hiku`, `kave`, `tinapihi`

**C16** — 9 types, 0.5% of tokens, mean position 0.78, P(initial)=0.00, P(final)=0.00
  `lonmar`, `nesalun`, `kesino`, `tisra`, `mise`, `rovesa`, `namolon`, `pito`, `mulu`

### Substitution grid (most interchangeable word pairs)

Word pairs with near-identical contexts — the classic decipherment grid. These likely share a category and differ in one semantic feature:

- `roku` ≈ `hiku` (cosine 0.889)
- `ka` ≈ `karos` (cosine 0.732)
- `kesino` ≈ `tisra` (cosine 0.717)
- `kesino` ≈ `rovesa` (cosine 0.715)
- `zirven` ≈ `rori` (cosine 0.69)
- `rori` ≈ `perlu` (cosine 0.675)
- `vepovurro` ≈ `namasiro` (cosine 0.67)
- `mo` ≈ `ne` (cosine 0.665)
- `namolon` ≈ `mulu` (cosine 0.654)
- `zirven` ≈ `perlu` (cosine 0.652)
- `mise` ≈ `mulu` (cosine 0.645)
- `kesino` ≈ `mulu` (cosine 0.645)
- `kesino` ≈ `pito` (cosine 0.641)
- `kotur` ≈ `vesra` (cosine 0.635)
- `rovesa` ≈ `mulu` (cosine 0.634)
- `nepiro` ≈ `mavezoro` (cosine 0.631)
- `kesino` ≈ `namolon` (cosine 0.63)
- `mise` ≈ `namolon` (cosine 0.629)
- `ka` ≈ `kanu` (cosine 0.629)
- `kesino` ≈ `mise` (cosine 0.626)
- `tizine` ≈ `vistates` (cosine 0.622)
- `zirven` ≈ `rakon` (cosine 0.619)
- `pito` ≈ `mulu` (cosine 0.619)
- `zirven` ≈ `tovo` (cosine 0.617)
- `zirven` ≈ `tonpe` (cosine 0.613)

## 4. Morphology

Affixation profile: **predominantly suffixing**

### Top suffix candidates

`-hi`(30), `-ro`(29), `-o`(15), `-i`(13), `-a`(13), `-ne`(12), `-ku`(10), `-ka`(10), `-u`(7), `-ros`(6), `-oku`(5), `-roku`(5), `-oro`(5), `-ahi`(5), `-ero`(5), `-uro`(5), `-aro`(5), `-ohi`(5), `-iku`(5), `-hiku`(5)

### Suffix signatures (candidate inflection paradigms)

- **{-hi / -ro}** × 16 stems (robustness 138): `kuzazen`, `line`, `loko`, `lute`, `milatu`, `mora`, `noma`, `nuposte` … (+8)
- **{-hi / -hiku / -ro / -roku}** × 5 stems (robustness 129): `lezervo`, `mavezo`, `narpos`, `nepi`, `numu`
- **{-hi / -ro / -∅}** × 8 stems (robustness 112): `kesino`, `mise`, `mulu`, `namasi`, `namolon`, `pito`, `rovesa`, `tisra`
- **{-ku / -∅}** × 10 stems (robustness 92): `lezervohi`, `lezervoro`, `mavezohi`, `mavezoro`, `narposhi`, `narposro`, `nepihi`, `nepiro` … (+2)
- **{-ka / -karos / -ne / -ros / -su / -∅}** × 2 stems (robustness 64): `kotur`, `vesra`
- **{-o / -oku}** × 5 stems (robustness 48): `lezervor`, `mavezor`, `narposr`, `nepir`, `numur`
- **{-i / -iku}** × 5 stems (robustness 48): `lezervoh`, `mavezoh`, `narposh`, `nepih`, `numuh`
- **{-ne / -∅}** × 7 stems (robustness 44): `kupo`, `kurpoza`, `mavo`, `nisvi`, `ruri`, `vesi`, `zalu`
- **{-ehi / -ero}** × 5 stems (robustness 42): `lin`, `lut`, `mis`, `nupost`, `sez`
- **{-ka / -ne / -∅}** × 3 stems (robustness 40): `lusi`, `pennon`, `rateza`

### Top prefix candidates

`ne-`(5), `lu-`(4), `l-`(3), `vesr-`(3), `k-`(3), `n-`(3), `kotur-`(3)

### Prefix signatures

- **{-ne / -kotur / -∅}** × 2 stems (robustness 23): `karos`, `ros`

## 5. Syntax probes

### Cluster profiles

- **C6** (open, 68 types, 18.7% tokens): strongly sentence-final — `nepiro`, `nepihi`, `numuro`, `numuhi`, `nepiroku`, `narposro`, `nepihiku`, `mavezoro`
- **C7** (small, 22 types, 7.9% tokens): medial — `rateza`, `litakis`, `lusi`, `pazi`, `ruri`, `titeki`, `viti`, `kapan`
- **C1** (closed, 5 types, 7.7% tokens): medial — `ka`, `karos`, `su`, `kanu`, `kara`
- **C15** (small, 17 types, 7.6% tokens): medial — `pennon`, `zalu`, `vesrane`, `mavo`, `kunmin`, `rosru`, `voraran`, `soslotes`
- **C2** (closed, 12 types, 7.4% tokens): medial — `zirven`, `tovo`, `tonpe`, `tarze`, `pinu`, `kasti`, `semu`, `murno`
- **C14** (small, 22 types, 7.0% tokens): medial — `nukamir`, `zola`, `larnu`, `nosa`, `menmer`, `kupo`, `memesa`, `nokurse`
- **C3** (closed, 7 types, 6.2% tokens): early in sentence — `rakon`, `ro`, `ra`, `taser`, `piri`, `rasmi`, `ve`
- **C5** (small, 14 types, 5.9% tokens): medial — `kotur`, `koturne`, `koturmu`, `koturmo`, `koturros`, `ratezane`, `pennonne`, `vesramu`
- **C0** (closed, 6 types, 5.1% tokens): early in sentence — `nu`, `kanesika`, `kotursu`, `zaretaka`, `vutotaka`, `lu`
- **C13** (closed, 10 types, 4.5% tokens): early in sentence — `koturka`, `koturkaros`, `vesraka`, `ratezaka`, `pennonka`, `vesrakaros`, `koturneka`, `lusika`
- **C17** (closed, 7 types, 3.9% tokens): medial — `neka`, `mu`, `nekaros`, `nemu`, `nesu`, `nenepihi`, `inesu`
- **C10** (closed, 6 types, 3.8% tokens): strongly sentence-initial — `lela`, `monla`, `pinzi`, `sursi`, `loros`, `zanto`
- **C9** (closed, 4 types, 3.7% tokens): medial — `rori`, `perlu`, `maku`, `ripi`
- **C8** (closed, 5 types, 3.5% tokens): medial — `mo`, `ros`, `neros`, `nemo`, `mopipe`
- **C19** (closed, 5 types, 2.1% tokens): medial — `vesra`, `nisvi`, `kanesi`, `vesraros`, `zalune`
- **C12** (closed, 1 types, 1.4% tokens): strongly sentence-final — `ku`
- **C18** (closed, 1 types, 1.3% tokens): late in sentence — `ne`
- **C11** (small, 11 types, 1.2% tokens): strongly sentence-initial — `tizine`, `vistates`, `zareta`, `pazisin`, `kenunri`, `namaris`, `zesulu`, `tesvonrur`
- **C4** (closed, 4 types, 0.6% tokens): strongly sentence-final — `roku`, `hiku`, `kave`, `tinapihi`
- **C16** (small, 9 types, 0.5% tokens): late in sentence — `lonmar`, `nesalun`, `kesino`, `tisra`, `mise`, `rovesa`, `namolon`, `pito`

### Strongest cluster transitions (P(to | from) ≥ 0.05)

- C6 → END: p=0.926 (n=2659)
- C5 → C6: p=0.711 (n=641)
- START → C10: p=0.193 (n=579)
- C8 → C6: p=0.862 (n=462)
- C7 → C6: p=0.366 (n=442)
- C15 → C6: p=0.366 (n=424)
- START → C0: p=0.121 (n=364)
- START → C3: p=0.12 (n=360)
- C14 → C1: p=0.322 (n=346)
- C15 → C1: p=0.292 (n=338)
- C14 → C6: p=0.309 (n=332)
- START → C2: p=0.106 (n=319)
- START → C13: p=0.095 (n=284)
- C7 → C1: p=0.229 (n=276)
- C2 → C7: p=0.216 (n=246)
- C2 → C15: p=0.213 (n=243)
- C19 → C6: p=0.734 (n=240)
- C7 → C17: p=0.196 (n=237)
- C2 → C14: p=0.205 (n=234)
- START → C15: p=0.075 (n=225)

### High-PMI bigrams (collocations)

- `namolon roku` (PMI 8.87, n=5)
- `tisra hiku` (PMI 8.63, n=5)
- `kesino roku` (PMI 8.28, n=5)
- `lonmar hiku` (PMI 7.73, n=5)
- `lonmar ro` (PMI 5.76, n=6)
- `milatuhi ku` (PMI 5.1, n=7)
- `vikuhi ku` (PMI 5.1, n=7)
- `tinapiro ku` (PMI 4.93, n=9)
- `lutehi ku` (PMI 4.87, n=6)
- `zareta ros` (PMI 4.87, n=8)
- `ve maku` (PMI 4.82, n=5)
- `pozi ne` (PMI 4.8, n=6)
- `kanesi ros` (PMI 4.79, n=10)
- `pokiro ku` (PMI 4.78, n=5)
- `lokoro ku` (PMI 4.74, n=7)
- `nupostero ku` (PMI 4.67, n=9)
- `nupostehi ku` (PMI 4.65, n=8)
- `vikuro ku` (PMI 4.65, n=6)
- `kotur rovesaro` (PMI 4.61, n=5)
- `mo nomahi` (PMI 4.56, n=7)

### Repeated formulae

- "`karos nu zirven`" ×7
- "`ka rakon zirven`" ×6
- "`nu kotur nepiro`" ×6
- "`nu zirven rateza`" ×6
- "`nu rakon kotur`" ×6
- "`rateza su nu`" ×5
- "`zirven kotur nepihi`" ×5
- "`rateza mo nepiro`" ×5
- "`koturne mo nepiro`" ×5
- "`vesrane karos nu`" ×4
- "`ka zirven vesra`" ×4
- "`neka zirven kotur`" ×4
- "`zola ka zirven`" ×4
- "`karos vesrane mu`" ×4
- "`neka nu rakon`" ×4
- "`nu rateza ros`" ×4
- "`pennon karos nu`" ×4
- "`koturka nu rakon`" ×4
- "`karos zirven kotur`" ×4
- "`ka rakon kotur`" ×4

### Numeral-like candidates

Closed classes that attach to one open class and avoid each other — the distributional fingerprint of numerals/quantifiers/determiners:

- C12: `ku` (open-adjacency 0.98, self-adjacency 0.0)

## 6. What this can and cannot tell you

Everything above is *structure*: word classes, paradigms, word order, formulae. None of it assigns meaning. To go further you need an anchor — proper names, numerals tied to countable context, images or objects the texts accompany, or a related language. The numeral-like candidates and formulae above are the best places to start looking.
