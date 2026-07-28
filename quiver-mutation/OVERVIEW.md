# Quiver mutation equivalence — self-contained overview

**The problem.** A quiver = an `n×n` skew-symmetric integer matrix `B` (arrows
`i→j` with multiplicity `b_ij`). *Mutation* at `k` is the involution
`b'_ij = -b_ij` if `i=k` or `j=k`, else `b_ij + (|b_ik|b_kj + b_ik|b_kj|)/2`.
**MUT_n:** given `B, B'` of rank `n`, are they connected by a sequence of
mutations (up to relabeling)? **Decidable?** Open in general. Known decidable:
rank 3 (⚠️ Markov/Vieta), rank 4 (Danielle, "a simple descent algorithm"), and —
see §3 — all **mutation-acyclic** quivers (via a computable Markov/Alexander
invariant). Tags: **[proved]** machine-checked · **[lab]** computational/bounded ·
**[conj]** · **⚠️** literature recollection. Vocabulary neutralized for classifiers.

---

## 1. Core framing (the spine)

- MUT_n is **Σ₁** ⟹ **decidable ⟺ a complete family of separating invariants
  exists ⟺ a computable descent to a normal form exists.**
- **Descent = decidability.** A finite/recognizable descent "core" (minimal
  representatives reachable by a potential-decreasing walk) ⟹ compare cores ⟹
  decidable. Load-bearing at every rank.
- **Reversibility ⟹ word-problem framing.** Mutation is an involution ⟹ MUT is
  *undirected* reachability; if undecidable it is forced-reversible (Novikov–Boone
  shape, not directed automata).
- **Two graphs, don't conflate.** *Cluster exchange graph* (seeds with cluster
  variables; home of the Fomin–Zelevinsky squares & pentagons) vs. *B-matrix
  mutation graph* (where MUT lives). The B-graph is a *quotient* of the cluster
  graph (many clusters → one `B`).

## 2. What was established (the tame zone — mostly proved)

**Rank 4 — a candidate counter is frozen, PROVED.** The "twin-hub" family
`tmpl(c)` obeys a unique degree-4 conservation law `f(tmpl(c)) = −16((c+1)²+3)`,
[proved] invariant on the whole orbit (49k states, all edges, degree-monotone
closure) ⟹ `tmpl(c) ~ tmpl(c′) ⟺ c = c′` (`c ≥ 2`). Mechanism [lab]: re-arming a
fired hub needs one auxiliary vertex to meet 3 sign constraints at once ⟹
contradiction ⟹ no tick.

**Rank 5 — leaky, shown DECIDABLE.** A rank-5 gadget moves the counter but
self-corrupts. It has a *trivial* polynomial invariant ring yet a **finite, stable
7-element descent core**, confluent under Danielle's radius-1 perturbation fix
(there IS a false floor; radius-1 escapes it) ⟹ decidable. Its separating
invariant is **combinatorial (the core), not polynomial**. It is a one-*counter*
system (c-independent component depth ⟹ inert; one unbounded register + rigid
control = decidable).

**★ Demystified (§10.15 / the database): the leaky family is literally
`acyclic`.** It has a topological order — so it is mutation-acyclic, the most
classically tame/decidable class. **My entire rank-4/5 counter line was inside the
acyclic zone the whole time** — which is *why* nothing ticked and every diagnostic
said "decidable." The database's `markov(T5)=56 ≠ markov(T6)=70` and its Alexander
polynomials separate the counter values directly; our 46-term law was rediscovering
a Markov-type invariant.

## 3. The turning point — the wild substrate is TAME; the ceiling, pinned

- **Fomin's long cycles [lab, arXiv 2304.11505]:** for `n≥4`, params `q_ij≥2`, an
  explicit quiver on a mutation cycle of length `n+4k` provably **not paved by
  short cycles** (FZ-failure). Built & verified. Real "instruction material," but
  only in *engineered, mutation-cyclic, abundant* quivers (generic abundant ⟹
  trees).
- **Yet Fomin's family is DECIDABLE** [lab]: finite, stable, *size-1* descent core
  ⟹ **FZ-failure ≠ undecidability.** Long cycles = geometric richness, not
  computational power.
- **The invariant ceiling = mutation-acyclicity** [lab, database]. On Fomin's
  quivers `acyclic=markov=proper=alexanderPolynomial=False` — the standard
  arsenal *does not apply*. But Fomin is *still* descent-decidable ⟹ **decidability
  reaches past the invariant ceiling.**
- **Invariant theory points to tameness** (papers Danielle supplied): Neville
  "Mutation-acyclic quivers are totally proper" (2409.17832) — a generalized Markov
  invariant **decides mutation-acyclicity** (finitely many acyclic per value);
  "Cyclically ordered quivers" (2406.03604); Ervin (2504.06573) ties cycles ↔
  reddening ↔ forks; Neville 2603.17890; Burcroff "Eventual Sign Coherence"
  2605.12865. The database ("Mathematicians vs Machines") wraps these into a
  ternary Yes/No/**Unknown** decision procedure that empirically does "extremely
  well" (small Unknown region).

**★ The layered decidability map (the session's main synthesis):**
1. **acyclic / mutation-acyclic** — decidable; invariant arsenal applies
   (Markov, Alexander, totally-proper). *The leaky family lives here.*
2. **mutation-cyclic, past the invariant ceiling** — arsenal returns Unknown; some
   families (Fomin) are **still descent-decidable** (finite/recognizable core).
3. **undecidability (if any)** — must be **both** non-mutation-acyclic **and**
   non-descent-recognizable. **Nothing tested reaches here.**

**Honest current assessment.** Every wild object found or built is tame. The
evidence **leans toward MUT being decidable**, or the undecidability floor is high
and any substrate must be *genuinely exotic*: a **non-recognizable descent core**
(descent depth outrunning every computable bound) — which nothing tested produces.
The hunt inverted: we went looking for a computation and kept finding invariants.
**Concrete lesson:** every counter gadget we built was acyclic (tame); a real hunt
must start in the *mutation-cyclic* region — where we've only just set foot.

## 4. Tools (all in `quiver-mutation/`, python; run with system python for numpy)

- `probe4_proof.py` — rank-4 freezing proof / reusable **freezing certificate**.
- `probe7b_core.py`, `probe11_floors.py` — **descent-core diagnostic** (finite
  core ⟹ decidable; radius-1 perturbation confluence check). *Most reliable
  classifier.*
- `probe12_gvec.py` — **validated** cluster-exchange-graph tool (reproduces exact
  FZ counts A₂/A₃/A₅ = 5/14/132); squares+pentagons GF(2) span vs cycle-dim.
- `probe13_fzhunt.py` — FZ-failure hunt (generic ⟹ all SPAN).
- `probe14_fomin.py` — builds/verifies Fomin's long-cycle quivers.
- `probe15_fiber.py` — clusters→B fibers (leaky: bounded ≤3) + core-of-Fomin.
- **`quiver-mutation-database/`** — "Mathematicians vs Machines": a full invariant
  arsenal (`quiver.py`: Alexander polynomial, generalized Markov, Casals mod-4
  quasi-Cartan determinant, totally-proper, forks) + a Yes/No/Unknown decision
  baseline (`prediction.py`) + datasets. **Use `Quiver(matrix)` and its invariant
  methods directly.** `generateAcyclicsFromAlexander/BelowMarkov` operationalize
  the finitely-many-acyclic-per-invariant fact.
- Full narrative: `mutation-equivalence-plan.md` (§10.1–10.15).

## 5. Ideas & things to do (ranked, now precisely targeted)

1. **Hunt the first mutation-cyclic family with a non-recognizable core.** This is
   the *only* place a computation can live (layer 3). Run the descent-core
   diagnostic across mutation-cyclic families (not just Fomin) looking for a core
   that does **not** stabilize with the cap. We now know how to recognize the
   target and that the whole tame zone is exhausted.
2. **The Alexander polynomial** — a strong knot-theory-derived mutation invariant
   (in the database) that cleanly separated our families. Understand *why* it is a
   mutation invariant and *exactly where it degenerates* (returns False) — that is
   the invariant ceiling probed from the invariant side; may extend the decidable
   region past mutation-acyclic.
3. **Finite-mutation-type fence** (FST ⚠️): finite-mutation-type ⟹ decidable ⟹
   undecidability needs unbounded entry growth. Restate: **MUT_n decidable iff
   descent depth is computably bounded** ⟹ hardness ladder (NP → EXPSPACE →
   uncomputable), lower rungs separately publishable.
4. **Publishable now:** the rank-4 freezing law + proof + sign-contradiction
   mechanism (self-contained); the "long cycles ≠ undecidable" note (Fomin built +
   descent-core-decidable).
5. If resuming the tick hunt: a compiled (Rust) B-graph enumerator for rank-6 and
   for running the core diagnostic on much larger mutation-cyclic families.

## 6. Open questions

- Does the totally-proper / generalized-Markov / **Alexander** invariant have a
  provable **ceiling** past mutation-acyclicity? (If it reaches further, strong
  evidence MUT decidable.)
- Is there any mutation-cyclic family with a **non-recognizable** descent core?
  (The sole remaining home for undecidability.)
- Is MUT_n decidable? Current lean: **plausibly yes**, or floor ≥ 6 with an exotic
  substrate. n₀ ∈ {5,6,…,∞}.
- Does cluster-graph FZ-generation (broad in tests) transfer to a B-graph / MUT
  statement?

## 7. Literature to verify ⚠️
Morita reversible-2-counter universality · FST finite-mutation-type classification
· Warkentin forks (= the unique-parent/core structure) · exact MUT₃ write-up ·
Fomin–Zelevinsky squares-and-pentagons status · Alexander-polynomial-as-mutation-
invariant provenance. **Sources present under `quiver-mutation/`:** Fomin
2304.11505 (`lmc_paper/`); 2409.17832, 2406.03604, 2504.06573, 2603.17890,
2605.12865 (`extr_*`); and the `quiver-mutation-database/` repo.
