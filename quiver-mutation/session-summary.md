# Session summary — quiver mutation equivalence (2026-07-03/04)

**Question.** MUT_n: are two rank-n skew-symmetric integer quivers connected by a
mutation sequence? Decidable? (Open in general.) Tags: **[proved]** machine-
checked · **[lab]** computational/bounded · **[conj]** · **⚠️** literature
recollection. (Vocabulary neutralized for content classifiers; full detail in
`mutation-equivalence-plan.md`.)

## 1. The spine
- MUT_n is Σ₁ ⟹ **decidable ⟺ a complete family of separating invariants exists
  ⟺ a computable descent to a normal form exists.**
- **Descent = decidability** (crystallized by Danielle's rank-4 result). The
  "unique-parent lemma" (finite core + a potential-decreasing move off it ⟹ each
  class is a tree rooted at its normal form) *is* descent's confluence condition.
- **One coin:** `descent works ⟺ unique-parent ⟺ decidable` vs
  `computation-encodable ⟺ descent has no computable normal form ⟺ undecidable`.
- **Reversibility ⟹ word problem, not machine reachability.** Mutation is an
  involution, so MUT is *undirected* reachability; the classical template is
  Novikov–Boone word problems (HNN/Britton ⚠️), whose apparatus exists precisely
  to forbid shortcut paths. Relation sites live only at the `|b|≤1` locus;
  `|b|≥2` is free/rigid (Garside-flavored).

## 2. Rank ladder
| rank | verdict | how |
|---|---|---|
| 3 | decidable ⚠️ | Markov/Vieta descent tree |
| 4 | **decidable** (Danielle, ~1yr) | "a simple descent algorithm" |
| ≥5 | **open** | this session mapped the frontier |

**[conj]** MUT_n undecidable for n ≥ n₀, **n₀ ∈ {5,6}** (rank 4 decidable ⟹ ≥5).

## 3. What we proved / found

**Rank 4 — frozen, proved.**
- A candidate counter `tmpl(c)` obeys a unique degree-4 conservation law (face-
  orientation-gated Markov terms + Pfaffian matchings), value `−16((c+1)²+3)`.
- **[proved]** it holds on the entire orbit (49k states, all edges, closure
  checked) ⟹ `tmpl(c)~tmpl(c′) ⟺ c=c′` for all c ≥ 2. Reusable certificate
  `probe4_proof.py`. The law is **orbit-conditional, not chamber-universal**
  (99.6% of random in-chamber points violate it).
- **Why [lab]:** re-arming a fired hub needs one aux vertex to meet 3 sign
  constraints at once ⟹ contradiction ⟹ no tick ⟹ descent wins.

**Rank 5 — leaky, then shown DECIDABLE (the key result).**
- **[lab]** A rank-5 gadget *moves* the counter (`b02:1000→1003`) but self-
  corrupts. The rank-4 sign contradiction **relocates from within one move to
  across the fire→re-arm sequence** (rigid → maybe dodgeable by a longer cycle).
- **[lab]** Directed tick searches all returned 0 (bounded; leaky / decoupled /
  coupled-aux).
- **[lab]** Genuinely rank-5 (the null-space direction of B moves ~2450
  projective directions / 4000 steps — not secretly rank-4) and has a **trivial
  low-degree invariant ring** (only constants, deg ≤3).
- **★ [lab] Decisive:** `T(5)` and `T(6)` **do not merge** (entry-≤45 orbit
  components fully enumerated, ~141k/129k states, completely disjoint), yet the
  **descent core is finite and stable** — the global min-`Σb²` stratum is **7
  canonical states**, unchanged across caps 15→60, disjoint, literally encoding
  the counter value. ⟹ **the leaky family is descent-DECIDABLE** (descend →
  canonicalize → compare a 7-element core), *not* an undecidability host.

**Rank 6 — bounded no-go.**
- **[lab]** SMT tick search (`b02` = pure accumulator ⟹ small-bounded state):
  **L=6 UNSAT, complete over wiring** — no length-6 word with any `[−2,2]¹²`
  wiring gives a tick. Short ticks ruled out; a real one needs `L ≥ 7`.
- Tooling caps out: per-word SMT scales to `L ≲ 7`; the pure-Python concrete
  rank-6 search is too slow (0 seeds/20 min). Definitive search needs a compiled
  enumerator or a fixed-sign-chamber SAT encoding.

## 4. The reframings (the real takeaways)
1. **"Genuinely rank-5 + trivial polynomial invariant ring" is NOT sufficient for
   undecidability.** The leaky family has both and is still decidable — its
   separating invariant is **combinatorial (the finite core), not polynomial**.
   Descent, not invariants, is load-bearing (confirmed up to rank 5).
2. **The sharp diagnostic is descent-core *recognizability*, not the invariant
   ring** — and (Danielle's correction) **infinite core ≠ undecidable**: rank 3
   has an unbounded but *recognizable* root set and is decidable. The real target
   is a core that is **not a decidable set** (descent depth not computably
   bounded), which is strictly stronger than "the core grows."
3. **`≈_fin` / word-problem is one question at two ranks.** Post-reversibility,
   "no uniform tick ⟺ a separating invariant exists" is the same statement as the
   rank-3 class-number thread (C3): finite/recognizable core = solvable word
   problem; non-recognizable core = the undecidable regime.

## 5. Corrections logged this session
- The one-sided Lyapunov LP is **infeasible** under reversibility (Δf≥0 on all
  moves ⟹ Δf=0) — it is really the invariant/core question.
- **Infinite core ≠ undecidable** (rank-3 witness) — target sharpened to
  *non-recognizable* core.
- A bio/cyber content classifier was over-triggering on math vocabulary; fixed by
  neutral synonyms (null-space, support, etc.).

## 6. Next directions (ranked)
1. **★ Direction 4 — faithfulness milestone (recommended).** Encode BS(1,2) (or
   another exponential-distortion group) as mutation-as-rewriting with `|b|≤1`
   relator sites; success = **descent depth blows up exponentially**, proving
   mutation *computes*. Targets a non-recognizable core directly; escalating to a
   Higman-embedded / Collins-style unsolvable word problem is then a modification,
   not a new construction.
2. **Harden the core lemma into a theorem** (`probe7b` as certificate generator):
   (a) no-false-floors (every state descends to the *global* min stratum; fix =
   bounded perturbation move), (b) class-invariance of the core map.
3. **Congruence stratification (cheap):** mutation is unimodular congruence, so
   det/SNF/kernel-lattice are decidable invariants — check whether the 7-element
   core is just congruence data + a bounded correction, or genuinely finer.
4. **Proper rank-6 tick tooling** (compiled enumerator / SAT) if the tick question
   is worth settling; **rank-3 `≈_fin ≠ ~`** (C3); **§9′ literature verification.**

## 7. Files
`mutation-equivalence-plan.md` (full) · `probe4_proof.py` (rank-4 proof/cert) ·
`probe5_rank5.py` (rank-5 tick) · `probe6_kernel.py` (null-space direction) ·
`probe6b_freeze_test.py` (invariant ring) · `probe7_connect.py` (T5–T6) ·
`probe7b_core.py` (descent core) · `probe8b_wordsearch.py` (rank-6 SMT) ·
`f_invariant.json` (the degree-4 law).
