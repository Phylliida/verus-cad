# PLAN: the papers — v1.0 (2026-07-19)

The remaining non-Lean deliverable. Two papers (possibly three), with the
Lean endgame (DESIGN-anyk3d-endgame.md) as the only hard dependency for
the strongest claims.

## Paper 1 (main): "No aperiodic single-tile Wang cube at any resolution"

**Claim ladder** (each independently citable):
1. K=3: no aperiodic binary Wang cube (machine-checked; trust base in
   RESULT.md) — with the screw structure (SCREW_STRUCTURE.md) and the
   sharp minimal certificate: 33 irredundant patterns (anyk-05: 30
   load-bearing, ≤3 pending), minimal box 4×3×3 = 36 cells (anyk-04 ✓).
2. K=2 (and K=1 by lifting): closed via cube-and-conquer, 151 leaf certs
   (anyk-02/03).
3. **Any K (the headline)**: the relation-level reduction — tilings =
   24-letter orientation SFTs, compat factors through 84 face equations,
   achievability = gain-structure census (1,445,865 profiles / 66,134
   canonical, triple-witnessed), every profile empty (≤6³) or periodic
   (≤ index 64). 2D analogue as fully-kernel-checked warm-up theorem
   (`AnyK2D.no_aperiodic_wang_square`).

**Narrative arc**: the einstein question → the symbolic family → the K=3
sweep and its screw reading → "you cannot build an irrational screw out of
a finite group" made rigorous for ALL K via the K-vanishing reduction →
the census → the two deepest screws (even-K-only, index 64, invisible to
every fixed-K sweep) as the dramatic finalists → the theorem.

**Sections sketch**: intro/history (hat, SCD, Culik–Kari — absorb
anyk-09's literature pass); the model; the K=3 result (compressed; cite
the artifact); the reduction (face equations, gain structures — the
mathematical heart, written as clean mathematics with the Lean names in
footnotes); the census + classification (methods: three independent
implementations); the frontier + certificates; formalization section
(trust bases, table of axioms per theorem); what is NOT claimed
(EXPLAINER.md §8 formalized); open problems (other matching relations,
reflections, non-cubic solids, the real 3D einstein).

**Venue thoughts**: Discrete & Computational Geometry / Combinatorial
Theory tier; or a shorter announcement + full arXiv. Decide with Danielle.

**Dependencies**: none for a draft NOW (empirical results complete);
the "fully machine-checked" headline for 3D waits on M5. Draft can begin
immediately with the 3D formalization described as "in progress" or the
paper timed to land with M5.

**TODO list**:
- [ ] absorb anyk-09 literature pass (Culik–Kari tile counts, Kari method,
      SCD/Danzer, hat/spectre citations, Socolar–Taylor for 2D context)
- [ ] figures: a decoration (K=3 bump cube render — k3-wang-cubes.html
      exists as a start); a screw motif; the census pipeline diagram;
      the frontier picture (empty/periodic antichains)
- [ ] statistics tables from the ledgers (indices histograms, census
      composition, cert dims histogram)
- [ ] the two index-64 finalists as worked examples (their held-equation
      anatomy is genuinely beautiful)
- [ ] decide single-paper vs. main+formalization split

## Paper 2 (formalization / ITP-CPP track): "A census born in a prover"

**Claim**: methodology paper — collapsing an infinite tile family to a
finite relation census INSIDE the prover: the K-vanishing factorization,
the gain-structure enumeration with completeness by construction
(census_count as a cross-implementation validation), frontier-compressed
certificates, and the trust-base ladder (pure kernel → +native_decide →
+verified-LRAT → external-checker, with each theorem placed on its rung).
The 2D theorem as the complete worked example; 3D as the scaled instance.

Also worth reporting: the engineering lessons (destutter/tail-recursion
in native hot paths; maxRecDepth and big literals; the 2D dress-rehearsal
discipline — every 3D lemma shape pre-validated in 2D compiled first-try).

**Dependencies**: strongest after M5; viable after M3b (the census
completeness is the novel formal content).

## Paper 3 (optional, small): CubeCover / cube-and-conquer → kernel
composition note — if not folded into Paper 2. The K=3 artifact + K=2
reuse demonstrates the library claim.

## Order of operations

1. Draft Paper 1's skeleton + figures now-ish (parallel to Lean S1-S3).
2. Literature pass (one session, WebSearch/WebFetch — the old anyk-09
   scope).
3. Paper 1 full draft once M5 lands (or before, with status-marked
   formalization section).
4. Paper 2 after M3b/M5, harvesting the session logs and design docs.
