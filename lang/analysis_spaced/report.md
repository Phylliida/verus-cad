# Decipherment report

Corpus: `/home/bepis/prog/verus-cad/lang/testdata/corpus.txt`

## 1. Is it language-like?

- ✅ **Zipf slope** — slope -1.37 (R²=0.915) — natural languages sit near -1
- ⚠️ **Heaps exponent** — beta 0.31 — unusual vocabulary growth (natural band 0.4-0.9)
- ✅ **Character predictability** — conditional entropy 2.71 bits vs unigram 3.88 — strong sequential structure (drop 1.17 bits)
- ℹ️ **Hapax fraction** — 12% of word types occur once — outside the common 25-70% band; very low suggests a small closed vocabulary, very high suggests heavy morphology or noise
- ℹ️ **Scale** — 3000 sentences, 14029 tokens, 571 types — decipherment confidence grows with corpus size; results below are provisional at small scales

Top 30 tokens: `ros`(922), `nu`(763), `zirven`(463), `rakon`(433), `kotur`(423), `mo`(353), `nepiro`(324), `koturka`(322), `rori`(250), `nepihi`(246), `lela`(229), `vesra`(211), `rateza`(180), `perlu`(175), `ra`(173), `numuro`(159), `koturne`(154), `vesraka`(150), `tovo`(131), `ro`(129), `pennon`(123), `numuhi`(122), `monla`(116), `nepiroku`(109), `narposro`(102), `ratezaka`(97), `nukamir`(96), `koturneka`(93), `nepihiku`(93), `maku`(91)

## 2. Segmentation

Word boundaries present in the input; no segmentation needed.

## 3. Word classes (distributional clusters)

500 word types clustered into 20 classes by their left/right neighbor profiles (PPMI + spherical k-means). Clusters approximate parts of speech; closed classes (few types, many tokens) are usually grammar words, open classes content words.

**C2** — 12 types, 13.8% of tokens, mean position 0.29, P(initial)=0.32, P(final)=0.00
  `nu`, `zirven`, `perlu`, `maku`, `tonpe`, `piri`, `tarze`, `pinu`, `kasti`, `sosva`, `nirlun`, `pizumu`

**C4** — 51 types, 9.4% of tokens, mean position 0.58, P(initial)=0.10, P(final)=0.00
  `kotur`, `pennon`, `lusi`, `vesrane`, `ratezane`, `zola`, `pazi`, `ruri`, `menmer`, `viti`, `nukamirne`, `sevi`, `patu`, `kapan` … (+37 more)

**C7** — 64 types, 9.2% of tokens, mean position 0.18, P(initial)=0.42, P(final)=0.00
  `koturka`, `ratezaka`, `koturneka`, `kanesika`, `pennonka`, `nukamirka`, `lusika`, `ratezaneka`, `litakiska`, `zolaka`, `larnuka`, `nosaka`, `voraranka`, `rosruka` … (+50 more)

**C9** — 35 types, 9.0% of tokens, mean position 1.00, P(initial)=0.00, P(final)=1.00
  `nepihi`, `numuhi`, `nepiroku`, `narposro`, `nepihiku`, `lezervoro`, `numuroku`, `kuzazenhi`, `salunro`, `numuhiku`, `mavezoroku`, `namasiro`, `linehi`, `vepovurhi` … (+21 more)

**C0** — 16 types, 7.5% of tokens, mean position 0.43, P(initial)=0.00, P(final)=0.00
  `ros`, `koturmu`, `ratezamu`, `vesranesu`, `nukamirsu`, `kunminsu`, `litakismu`, `menmermu`, `nisvimu`, `noluvimu`, `titekimu`, `vitineka`, `vutunnamu`, `kurpozanemu` … (+2 more)

**C11** — 42 types, 7.3% of tokens, mean position 0.55, P(initial)=0.14, P(final)=0.00
  `vesra`, `nukamir`, `litakis`, `mavo`, `pennonne`, `kunmin`, `kanesi`, `rosru`, `larnu`, `nosa`, `nisvi`, `zalune`, `voraran`, `mavone` … (+28 more)

**C6** — 43 types, 7.3% of tokens, mean position 1.00, P(initial)=0.00, P(final)=1.00
  `nepiro`, `mavezoro`, `kuzazenro`, `mavezohi`, `lezervohi`, `vepovurro`, `vilaro`, `milaturo`, `narposroku`, `lezervoroku`, `mavezohiku`, `nupostero`, `tisraro`, `tinapiro` … (+29 more)

**C17** — 73 types, 6.1% of tokens, mean position 0.21, P(initial)=0.39, P(final)=0.00
  `vesraka`, `vesraneka`, `zaluka`, `mavoka`, `zaretaka`, `pazika`, `vesramu`, `kunminka`, `kupoka`, `vistateska`, `nukamirneka`, `zaluneka`, `zolaneka`, `memesaka` … (+59 more)

**C15** — 36 types, 4.8% of tokens, mean position 1.00, P(initial)=0.00, P(final)=1.00
  `numuro`, `narposhi`, `salunhi`, `morahi`, `narposhiku`, `linero`, `namasihi`, `nomaro`, `moraro`, `misero`, `nupostehi`, `namolonro`, `kuzazenroku`, `povuro` … (+22 more)

**C10** — 8 types, 4.2% of tokens, mean position 0.00, P(initial)=0.99, P(final)=0.00
  `lela`, `monla`, `pinzi`, `sursi`, `loros`, `zanto`, `tesvonrurka`, `kipinvusu`

**C3** — 4 types, 4.1% of tokens, mean position 0.26, P(initial)=0.36, P(final)=0.00
  `rakon`, `taser`, `ve`, `vutunnaka`

**C12** — 36 types, 4.1% of tokens, mean position 0.59, P(initial)=0.08, P(final)=0.00
  `rateza`, `zalu`, `kotursu`, `vesrasu`, `soslotes`, `vutunna`, `litakisne`, `koturnesu`, `rurine`, `sinmonlu`, `kulir`, `male`, `kupone`, `pizu` … (+22 more)

**C5** — 7 types, 2.8% of tokens, mean position 0.76, P(initial)=0.01, P(final)=0.09
  `mo`, `tinapihi`, `nupostehiku`, `lutehiku`, `mopipe`, `vilahiku`, `povuroku`

**C8** — 8 types, 2.5% of tokens, mean position 0.31, P(initial)=0.28, P(final)=0.00
  `rori`, `murno`, `mime`, `larnuneka`, `nisvinesu`, `kipinvuneka`, `korinesu`, `lunlivusu`

**C19** — 17 types, 2.1% of tokens, mean position 0.31, P(initial)=0.32, P(final)=0.00
  `ro`, `rasmi`, `ripi`, `ratezasu`, `vusakoka`, `litakissu`, `pazisu`, `rurisu`, `lirsomu`, `titekisu`, `vesimu`, `zolanesu`, `kirimu`, `letovonemu` … (+3 more)

**C16** — 18 types, 1.5% of tokens, mean position 0.58, P(initial)=0.13, P(final)=0.00
  `koturne`, `letovo`, `lunlivune`, `ratezanemu`, `mavomu`, `mekone`, `kipinvune`, `vesine`, `sapine`, `tilamu`, `kuponesu`, `mavonesu`, `menmernesu`, `posatone` … (+4 more)

**C18** — 8 types, 1.4% of tokens, mean position 0.32, P(initial)=0.24, P(final)=0.00
  `tovo`, `rinlon`, `nokurseka`, `lerone`, `letovoka`, `sapimu`, `tetane`, `tetasu`

**C14** — 5 types, 1.3% of tokens, mean position 0.28, P(initial)=0.34, P(final)=0.00
  `ra`, `nisvineka`, `nossuka`, `mavosu`, `rununaka`

**C13** — 7 types, 0.6% of tokens, mean position 0.28, P(initial)=0.33, P(final)=0.00
  `semu`, `sinmonluka`, `nosaneka`, `kapanmu`, `lusinemu`, `kurpozasu`, `lesamu`

**C1** — 10 types, 0.4% of tokens, mean position 0.30, P(initial)=0.31, P(final)=0.00
  `lusisu`, `rosruneka`, `remaka`, `sevika`, `pennonsu`, `lusinesu`, `mavonemu`, `mornakinneka`, `namaris`, `soslotesmu`

### Substitution grid (most interchangeable word pairs)

Word pairs with near-identical contexts — the classic decipherment grid. These likely share a category and differ in one semantic feature:

- `rosruneka` ≈ `vitika` (cosine 0.68)
- `vesi` ≈ `titekine` (cosine 0.571)
- `patuka` ≈ `lesaka` (cosine 0.565)
- `noluvika` ≈ `lunlivuka` (cosine 0.562)
- `nomaro` ≈ `vikuro` (cosine 0.507)
- `litakisneka` ≈ `namariska` (cosine 0.507)
- `zaretaka` ≈ `zesuluka` (cosine 0.498)
- `vutotaka` ≈ `pazisinka` (cosine 0.493)
- `nepihi` ≈ `narposro` (cosine 0.491)
- `pokiro` ≈ `lineroku` (cosine 0.49)
- `vistateska` ≈ `maleka` (cosine 0.489)
- `zesuluka` ≈ `tesvonrur` (cosine 0.488)
- `kupoka` ≈ `remaka` (cosine 0.487)
- `nepiro` ≈ `mavezoro` (cosine 0.483)
- `salunhi` ≈ `povuro` (cosine 0.481)
- `kuzazenroku` ≈ `povuro` (cosine 0.477)
- `memesaka` ≈ `rurika` (cosine 0.472)
- `sursi` ≈ `zanto` (cosine 0.472)
- `leroka` ≈ `kipinvuka` (cosine 0.471)
- `kurpoza` ≈ `kipinvu` (cosine 0.47)
- `tinapihi` ≈ `lutehiku` (cosine 0.47)
- `tilaka` ≈ `pizuka` (cosine 0.469)
- `maleka` ≈ `tetaka` (cosine 0.463)
- `moraro` ≈ `nuposteroku` (cosine 0.462)
- `kuzazenroku` ≈ `lineroku` (cosine 0.456)

## 4. Morphology

Affixation profile: **predominantly suffixing**

### Top suffix candidates

`-ka`(130), `-su`(85), `-mu`(75), `-eka`(65), `-e`(64), `-ne`(60), `-neka`(59), `-ku`(59), `-i`(45), `-esu`(40), `-o`(39), `-nesu`(36), `-emu`(31), `-hi`(30), `-ro`(30), `-oku`(30), `-roku`(30), `-iku`(29), `-hiku`(29), `-nemu`(28)

### Suffix signatures (candidate inflection paradigms)

- **{-hi / -hiku / -ro / -roku}** × 29 stems (robustness 783): `kesino`, `kuzazen`, `lezervo`, `line`, `loko`, `lonmar`, `lute`, `mavezo` … (+21)
- **{-ka / -mu / -ne / -neka / -nemu / -nesu / -su / -∅}** × 13 stems (robustness 695): `kotur`, `kunmin`, `kupo`, `litakis`, `lusi`, `mavo`, `menmer`, `pennon` … (+5)
- **{-e / -eka / -emu / -esu}** × 20 stems (robustness 562): `koturn`, `kunminn`, `kupon`, `kurpozan`, `letovon`, `litakisn`, `lusin`, `mavon` … (+12)
- **{-ku / -∅}** × 59 stems (robustness 536): `kesinohi`, `kesinoro`, `kuzazenhi`, `kuzazenro`, `lezervohi`, `lezervoro`, `linehi`, `linero` … (+51)
- **{-ka / -mu / -ne / -neka / -nesu / -su / -∅}** × 11 stems (robustness 496): `ketur`, `kipinvu`, `kiri`, `nisvi`, `nosa`, `nukamir`, `pazi`, `sapi` … (+3)
- **{-ka / -mu / -su / -∅}** × 18 stems (robustness 492): `koturne`, `kunminne`, `kupone`, `kurpozane`, `letovone`, `litakisne`, `lusine`, `mavone` … (+10)
- **{-e / -eka / -esu}** × 19 stems (robustness 348): `keturn`, `kipinvun`, `kirin`, `korin`, `lesan`, `mal`, `malen`, `mekon` … (+11)
- **{-ka / -mu / -ne / -neka / -nemu / -su / -∅}** × 7 stems (robustness 336): `kulir`, `larnu`, `lero`, `lirso`, `nokurse`, `sinmonlu`, `titeki`
- **{-i / -ika / -imu / -ine / -ineka / -inesu / -isu}** × 8 stems (robustness 311): `kir`, `lus`, `nisv`, `paz`, `rur`, `sap`, `ves`, `vit`
- **{-ka / -su / -∅}** × 17 stems (robustness 304): `keturne`, `kipinvune`, `kirine`, `korine`, `lesane`, `malene`, `mekone`, `memesane` … (+9)

### Top prefix candidates

`ko-`(11), `lu-`(10), `ti-`(7), `menme-`(7), `ke-`(7), `kotu-`(7), `ratez-`(7), `penno-`(7), `rur-`(7), `kunmi-`(7), `vesr-`(7), `zal-`(7), `mav-`(7), `kup-`(7), `lus-`(7), `vit-`(7), `l-`(6), `lirs-`(6), `titek-`(6), `ki-`(6)

### Prefix signatures

- **{-titek / -sap / -kir / -rur / -ves / -lus / -vit / -nisv / -paz}** × 5 stems (robustness 256): `ika`, `imu`, `ine`, `ineka`, `isu`
- **{-kup / -ler / -lirs / -mav / -letov}** × 5 stems (robustness 148): `oka`, `one`, `oneka`, `onemu`, `osu`
- **{-zol / -rem / -vesr / -nos / -ratez}** × 5 stems (robustness 148): `aka`, `ane`, `aneka`, `anesu`, `asu`
- **{-menme / -kuli / -kotu}** × 6 stems (robustness 109): `rka`, `rmu`, `rne`, `rneka`, `rnemu`, `rsu`
- **{-kunmi / -penno}** × 7 stems (robustness 87): `nka`, `nmu`, `nne`, `nneka`, `nnemu`, `nnesu`, `nsu`

## 5. Syntax probes

### Cluster profiles

- **C2** (closed, 12 types, 13.8% tokens): early in sentence — `nu`, `zirven`, `perlu`, `maku`, `tonpe`, `piri`, `tarze`, `pinu`
- **C4** (open, 51 types, 9.4% tokens): medial — `kotur`, `pennon`, `lusi`, `vesrane`, `ratezane`, `zola`, `pazi`, `ruri`
- **C7** (open, 64 types, 9.2% tokens): early in sentence — `koturka`, `ratezaka`, `koturneka`, `kanesika`, `pennonka`, `nukamirka`, `lusika`, `ratezaneka`
- **C9** (open, 35 types, 9.0% tokens): strongly sentence-final — `nepihi`, `numuhi`, `nepiroku`, `narposro`, `nepihiku`, `lezervoro`, `numuroku`, `kuzazenhi`
- **C0** (small, 16 types, 7.5% tokens): medial — `ros`, `koturmu`, `ratezamu`, `vesranesu`, `nukamirsu`, `kunminsu`, `litakismu`, `menmermu`
- **C11** (open, 42 types, 7.3% tokens): medial — `vesra`, `nukamir`, `litakis`, `mavo`, `pennonne`, `kunmin`, `kanesi`, `rosru`
- **C6** (open, 43 types, 7.3% tokens): strongly sentence-final — `nepiro`, `mavezoro`, `kuzazenro`, `mavezohi`, `lezervohi`, `vepovurro`, `vilaro`, `milaturo`
- **C17** (open, 73 types, 6.1% tokens): early in sentence — `vesraka`, `vesraneka`, `zaluka`, `mavoka`, `zaretaka`, `pazika`, `vesramu`, `kunminka`
- **C15** (open, 36 types, 4.8% tokens): strongly sentence-final — `numuro`, `narposhi`, `salunhi`, `morahi`, `narposhiku`, `linero`, `namasihi`, `nomaro`
- **C10** (closed, 8 types, 4.2% tokens): strongly sentence-initial — `lela`, `monla`, `pinzi`, `sursi`, `loros`, `zanto`, `tesvonrurka`, `kipinvusu`
- **C3** (closed, 4 types, 4.1% tokens): early in sentence — `rakon`, `taser`, `ve`, `vutunnaka`
- **C12** (open, 36 types, 4.1% tokens): medial — `rateza`, `zalu`, `kotursu`, `vesrasu`, `soslotes`, `vutunna`, `litakisne`, `koturnesu`
- **C5** (closed, 7 types, 2.8% tokens): late in sentence — `mo`, `tinapihi`, `nupostehiku`, `lutehiku`, `mopipe`, `vilahiku`, `povuroku`
- **C8** (closed, 8 types, 2.5% tokens): medial — `rori`, `murno`, `mime`, `larnuneka`, `nisvinesu`, `kipinvuneka`, `korinesu`, `lunlivusu`
- **C19** (small, 17 types, 2.1% tokens): medial — `ro`, `rasmi`, `ripi`, `ratezasu`, `vusakoka`, `litakissu`, `pazisu`, `rurisu`
- **C16** (small, 18 types, 1.5% tokens): medial — `koturne`, `letovo`, `lunlivune`, `ratezanemu`, `mavomu`, `mekone`, `kipinvune`, `vesine`
- **C18** (closed, 8 types, 1.4% tokens): medial — `tovo`, `rinlon`, `nokurseka`, `lerone`, `letovoka`, `sapimu`, `tetane`, `tetasu`
- **C14** (closed, 5 types, 1.3% tokens): early in sentence — `ra`, `nisvineka`, `nossuka`, `mavosu`, `rununaka`
- **C13** (small, 7 types, 0.6% tokens): early in sentence — `semu`, `sinmonluka`, `nosaneka`, `kapanmu`, `lusinemu`, `kurpozasu`, `lesamu`
- **C1** (small, 10 types, 0.4% tokens): medial — `lusisu`, `rosruneka`, `remaka`, `sevika`, `pennonsu`, `lusinesu`, `mavonemu`, `mornakinneka`

### Strongest cluster transitions (P(to | from) ≥ 0.05)

- C9 → END: p=1.0 (n=1266)
- C6 → END: p=1.0 (n=1029)
- C15 → END: p=0.997 (n=669)
- START → C2: p=0.21 (n=628)
- START → C10: p=0.194 (n=582)
- START → C7: p=0.18 (n=539)
- C4 → C9: p=0.352 (n=461)
- C7 → C0: p=0.322 (n=414)
- C2 → C4: p=0.206 (n=396)
- C2 → C7: p=0.185 (n=356)
- START → C17: p=0.112 (n=334)
- C11 → C9: p=0.295 (n=304)
- C11 → C6: p=0.288 (n=296)
- C4 → C6: p=0.222 (n=291)
- C2 → C11: p=0.151 (n=291)
- C7 → C2: p=0.215 (n=276)
- C0 → C2: p=0.25 (n=262)
- C17 → C0: p=0.28 (n=238)
- C4 → C15: p=0.166 (n=218)
- START → C3: p=0.07 (n=209)

### High-PMI bigrams (collocations)

- `tovo nukamirne` (PMI 4.83, n=5)
- `kotur rovesaro` (PMI 4.26, n=5)
- `ve maku` (PMI 4.24, n=5)
- `titeki nepiro` (PMI 4.2, n=5)
- `mo nomahi` (PMI 3.92, n=6)
- `mo nomaro` (PMI 3.88, n=7)
- `ruri mo` (PMI 3.71, n=8)
- `rosruneka ros` (PMI 3.69, n=6)
- `vitika ros` (PMI 3.69, n=6)
- `remaka ros` (PMI 3.6, n=5)
- `lesaka ros` (PMI 3.6, n=5)
- `mo salunhi` (PMI 3.54, n=9)
- `lela kanesi` (PMI 3.51, n=6)
- `koturne lezervoro` (PMI 3.47, n=7)
- `rosru mo` (PMI 3.45, n=8)
- `nukamir mavezoro` (PMI 3.45, n=5)
- `mo narposhiku` (PMI 3.44, n=6)
- `nukamirne mo` (PMI 3.4, n=5)
- `mo vepovurro` (PMI 3.37, n=9)
- `vesrane nepiroku` (PMI 3.37, n=5)

### Repeated formulae

- "`koturka ros nu`" ×21
- "`ros nu zirven`" ×12
- "`nu koturka ros`" ×9
- "`kotur mo nepihi`" ×7
- "`ros nu kotur`" ×7
- "`ros zirven kotur`" ×7
- "`koturka ros rakon`" ×7
- "`kotur mo nepiro`" ×6
- "`nu kotur nepiro`" ×6
- "`nu kotur ros`" ×6
- "`vesraka ros nu`" ×6
- "`rakon koturka ros`" ×6
- "`koturka ros kotur`" ×6
- "`nu rakon kotur`" ×6
- "`ros nu rakon`" ×6
- "`ros kotur nepihi`" ×5
- "`ros kotur mo`" ×5
- "`ro koturka ros`" ×5
- "`nu zirven kotur`" ×5
- "`zirven kotur nepihi`" ×5

### Numeral-like candidates

Closed classes that attach to one open class and avoid each other — the distributional fingerprint of numerals/quantifiers/determiners:

- C5: `mo`, `tinapihi`, `nupostehiku`, `lutehiku`, `mopipe`, `vilahiku`, `povuroku` (open-adjacency 0.92, self-adjacency 0.01)
- C18: `tovo`, `rinlon`, `nokurseka`, `lerone`, `letovoka`, `sapimu`, `tetane`, `tetasu` (open-adjacency 0.62, self-adjacency 0.0)
- C8: `rori`, `murno`, `mime`, `larnuneka`, `nisvinesu`, `kipinvuneka`, `korinesu`, `lunlivusu` (open-adjacency 0.62, self-adjacency 0.0)

## 6. What this can and cannot tell you

Everything above is *structure*: word classes, paradigms, word order, formulae. None of it assigns meaning. To go further you need an anchor — proper names, numerals tied to countable context, images or objects the texts accompany, or a related language. The numeral-like candidates and formulae above are the best places to start looking.
