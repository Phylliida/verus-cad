# Quiver mutation equivalence — findings summary

**Question.** MUT_n: given two skew-symmetric integer matrices (quivers) of rank
n, are they connected by a mutation sequence? Decidable? (Open in general.)
Dates 2026-07-03/04. Detail: `mutation-equivalence-plan.md`. Tags: **[proved]**
machine-checked · **[lab]** computational, bounded · **[conj]** · **⚠️**
literature recollection, unverified.

---

## 1. Framing

- **MUT_n is Σ₁** (search words) ⟹ **decidable ⟺ inequivalence r.e. ⟺ complete
  separating-invariant family ⟺ computable mutation-distance bound** (the
  groupoid's "Dehn function").
- **Descent = decidability** (Danielle's rank-4 result). A computable normal form
  (descend to a canonical rep) decides MUT_n; the "unique-parent lemma" (finite
  minimal core + unique potential-decreasing move off it ⟹ each class is a tree)
  *is* descent's termination+confluence.
- **One coin:** `descent works ⟺ unique-parent ⟺ decidable` vs
  `machine-encodable ⟺ descent non-confluent ⟺ undecidable`. Undecidability
  program = build a rank-≥5 family where no descent works.
- **Meta-pattern.** Every solved family (finite-type, surfaces, positroid, dimer,
  rank 3) has an ambient model of which quivers are shadows. **[conj]**
  decidability boundary = geometric-modelability boundary.
- Padding `B ↦ B⊕0` gives MUT_n ≤ MUT_{n+1}; hardness climbs with rank.

## 2. Rank facts

| rank | status | note |
|---|---|---|
| 3 | decidable **⚠️** (Markov/Vieta tree) | anchor; descent is load-bearing |
| 4 | **decidable** (Danielle, ~1yr, "simple descent") | we reconstruct *why* (§4) |
| ≥5 | **open** — undecidability target | rank 5 is *leaky, not frozen* (§5) |

**[conj] C1:** MUT_n undecidable for n ≥ n₀, **n₀ ∈ {5,6}** (rank 4 decidable ⟹
floor ≥ 5; 6 if rank 5 is also descent-tame).

## 3. Invariants (Probe 1)

Exact mod-p search (2 primes, integer anchors) over signed-monomial features
`∏ sgn(bᵢ)^{sᵢ}|bᵢ|^{tᵢ}` (plain polynomials miss the semi-algebraic ones).

- **[lab]** Rank-3 cyclic Markov constant `a²+b²+c²−abc` is **not** polynomial in
  signed entries; needs the signed basis (recovered exactly).
- **[lab]** Rank-3 acyclic invariants = `{1, b01², b02², b12², b01b02b12}` ⟹
  **acyclic rank-3 mutation is always a sink/source move** (free corollary).
- **[lab]** Rank-4 **global** deg-≤4 invariants = **exactly `{1, Pf²}`**.
- **[lab]** mod-m congruence class of `B` is invariant but does **not** separate
  counter states (obstruction finer than congruence).

## 4. Rank 4 is frozen — proved (Probe 1b/4)

"Twin-hub" `tmpl(c)` = candidate counter holding value c.

- **[lab]** Extracted a **unique 46-term degree-4 conservation law**:
  `−16·Σ_edges|b|²` + face-orientation-gated Markov terms (one per K₄ triangle,
  gate = its cyclic/acyclic orientation) + Pfaffian perfect-matching terms;
  value `f(tmpl(c)) = −16((c+1)²+3)`.
- **[proved]** `F ≡ −16c²−32c−64` on the *entire* orbit (49,296 states; all
  197,184 edges preserve F incl. boundary; degree-monotone completeness checked)
  ⟹ **twin-hub frozen for all c ≥ 2**: `tmpl(c) ~ tmpl(c′) ⟺ c=c′`. Engine
  `probe4_proof.py` = reusable **freezing certificate**.
- **Correction:** `f` is **orbit-conditional, not chamber-universal** (99.6% of
  random in-chamber points violate it) ⟹ the clean finite chamber-identity proof
  fails; real invariants are of the **Zariski closure of the orbit**.
- **Why rank 4 freezes [lab]:** re-arming a fired hub via the correction term
  needs one aux vertex to satisfy 3 sign constraints at once (hold `b02`, re-arm
  `b01`, re-arm `b12`) ⟹ forces one entry both + and −. **Contradiction ⟹ no
  tick ⟹ descent wins.** Likely the obstruction Danielle's descent exploits.

## 5. Rank 5 is leaky, not frozen (Probes 2/5/6)

- **[lab]** Firing a rank-5 split gadget **moves** the counter (`b02:1000→1003`)
  but self-corrupts (arm stays disarmed, aux lines grow). Obstruction shifts from
  *can't increment* (rank 4) to *increments but leaks* — the decidable↔machine
  boundary. Leak = firing perturbs re-arm lines via the correction term, which
  bleed into `b02`.
- **[lab]** Fire-decoupling works (arms opposite the hub ⟹ `b02+=1` exactly) but
  then kills the next re-arm step ⟹ the rank-4 contradiction **relocates from
  within one move to across the fire→re-arm sequence** (rigid → maybe-dodgeable
  by a longer cycle).
- **[lab] Ratchet searches all 0 ticks, all bounded:** leaky (DEGCAP 3), decoupled
  (DEGCAP 4), coupled auxiliaries `b34≠0` (DEGCAP 4). Bounds real (tick may spike
  degree past cap; weights ≤2; long cycles invisible). **Not a no-go** — the
  "patched rank-4 gadget" just doesn't close a *short, small-weight* cycle.
- **[lab] Genuinely rank-5** (Probe 6, kernel vector `v_i=(−1)^i Pf(B_î)`,
  `v↦E^{−T}v`): `v` **moves** (~2450 projective dirs / 4000 steps) on all three
  families ⟹ not secretly rank-4; the "v-fixed ⟹ import freezing" pruner doesn't
  fire.
- **[lab] Trivial low-degree invariant ring** (Probe 6b): frozen twin-hub has a
  rich ring (dim 138/1198 at deg 2/3); the rank-5 gadgets have **dim 1 (constants
  only)** through deg 3 — the profile of a family that *could* host a machine.
  *Caveats:* dim 1 is consistent with `T(5)~T(6)` but not a proof; and the
  known-frozen twin-hub is also unseparated at deg ≤3 (its law is deg 4), so
  certifying freezing needs the expensive deg-4-over-10-vars search. Cheap
  separators are out — twin-hub is Pfaffian-degenerate (`Pf=0`) so SNF/`d₁d₂`=0.
- **Reversibility note:** `μ_k` is an involution ⟹ `Δf≥0` on all moves ⟹ `Δf=0`;
  so a one-sided "strict-on-fire" Lyapunov is infeasible. Ratchet-nonexistence ⟺
  separating-invariant-exists (equality form); the directed fork potential is a
  *separate* tool (certifies decidability, not ratchet-freeness).

## 6. Mapped, not yet run

- **Piecewise-affine machine framing** (Danielle dir 3): freeze small-entry
  control ⟹ correction term is affine in the "register" coordinates ⟹ induced PAM;
  PAM reachability undecidable in dim 2 (⚠️ Koiran–Cosnard–Garzon) — a much lower
  bar than a clean Minsky counter. **Highest-leverage next step.**
- **Orbit-closure ideal, degree-by-degree** (dir 6): stabilize the largest
  deg-≤d subspace invariant under pullback by the (quadratic) mutation maps —
  finite-dim descending chains stabilize ⟹ terminating; turns "dim 1 at deg ≤3"
  into a *proof* and systematizes the 46-term discovery.
- **Fork theory** (Warkentin ⚠️) as the name of the unique-parent lemma /
  freezing; **`≈_fin ≠ ~` at rank 3** (⚠️ Ghosh–Sarnak Hasse failures, Chen mod-p
  connectivity); **groupoid/Garside** (relations only at |b|≤1, |b|≥2 locally
  free); **complexity lower bounds from the leak** (no poly Dehn function ⟹ MUT_5
  maybe not in NP).

## 7. Open threads (ranked)

1. **Rank-5 counter** via the **PAM framing** — 2 registers + rich branching, not
   a clean reset; or a 6th vertex (⟹ n₀=6). Use `probe4_proof.py` as a tameness
   pruner.
2. **Orbit-closure ideal** — prove the rank-5 invariant ring is trivial (or find
   its generators); connect rank-4's to Danielle's descent potential. What dies at
   rank 5? Pfaffian ≡ 0 at odd rank is the loud suspect (the matching half of the
   rank-4 law has no rank-5 analog).
3. **Deg-4 freeze certificate** over 10 vars — the only way to *certify* a rank-5
   family frozen (vs. the current deg-≤3-bounded evidence).
4. **`≈_fin ≠ ~` at rank 3** (C3); **§9′ literature verification.**

## Files
`mutation-equivalence-plan.md` (full) · `mutation_lab.py` · `probe1_invariants.py`
· `probe1b_extract.py` · `probe1c_scope.py` · `probe4_chambers.py` ·
`probe4_proof.py` (freezing proof/certificate) · `probe5_rank5.py` (rank-5 hunt) ·
`probe6_kernel.py` (kernel vector) · `probe6b_freeze_test.py` (invariant-ring) ·
`f_invariant.json` (the 46-term law) · `poem-the-obstruction-moves.md`.
