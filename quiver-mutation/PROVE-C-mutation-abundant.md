# Prove: the quiver `C` is mutation-abundant

Self-contained. **Goal in §2.** The problem is *exactly* reduced (§3, proven) to one
global statement (R1). (R1) is proven **not** closable by any *local* or *finite-state*
certificate (§4 obstruction + §6 phantoms). The remaining route is a **tameness normal
form** (§5), whose finite skeleton — a 110-state automaton — is now identified. Do not
retry local certificates or finite sign/comparison automata; §6 rules them out.

## 1. Definitions

A **quiver** is a `5×5` skew-symmetric integer matrix `B`, stored as the upper tuple
`(b_01,b_02,b_03,b_04,b_12,b_13,b_14,b_23,b_24,b_34)`; `b_ij>0` is an arrow `i→j`,
weight `|b_ij|`. **Mutation** `μ_k`: `b'_ij=−b_ij` if `i=k` or `j=k`; else
`b'_ij=b_ij+(|b_ik|·b_kj+b_ik·|b_kj|)/2`. `[B]` = mutation class. `B` is **abundant**
if all `|b_ij|≥2`, **mutation-abundant** if every quiver in `[B]` is.

## 2. Goal

`C = (-3,-2,-2,2,-2,2,-3,3,-2,-2)`.

> **Prove `C` is mutation-abundant.**

This makes `[C]` the first known **mutation-abundant, vortex-free** class with
**infinite forkless part** (already proven: `w=μ_2μ_0` is a linear hairpin, so
`X_m=w^m(C)` are infinitely many abundant vortex-free non-forks) — the open side of
Burcroff's finite-forkless problem (arXiv 2605.12865), in the clean regime.

**Restatement.** Every entry of every quiver in `[C]` is `≡±2 (mod 5)` (residues
`{2,3}` exclude `0,±1`, forcing `|b|≥2`). Verified true on the whole component to
entry-cap 900 (**87,620 quivers, 0 exceptions**); the task is a proof for all of `[C]`.

## 3. Exact reduction (proven): Goal ⟺ (R1)

For a quiver with all residues in `{2,3}`, set `τ_ij = +1` if `|b_ij|≡2`, `−1` if
`≡3` (`τ` symmetric); `τ_△=τ_ijτ_jkτ_ik`. Call `B` **coherent** if all residues are
in `{2,3}` and **(T)** holds: `τ_△=+1` on cyclic triangles, `−1` on transitive ones,
for all 10 triangles. (`C` is coherent — checked.)

**Case-5c config.** At a vertex `k`, a triple `{i,j,l}` of the other four with
`sgn(b_ik)=sgn(b_jk)=−sgn(b_lk)` such that `{i,k,l}` and `{j,k,l}` are both cyclic
(then `{i,j,l}` is transitive with a middle vertex `m∈{i,j}` and other `o`). Set
`a=|b_kl|`, `p_x=|b_xk|`, `q_x=|b_xl|`, `flip_x ⟺ q_x<a·p_x`. A **bad window** is a
Case-5c config with `flip_m ∧ ¬flip_o`.

**Reduction theorem** (Lemmas 0–3, proven). If `B` is coherent, then `μ_k(B)` is
coherent **unless** `B` has a bad window at `k`; conversely a bad window makes `μ_k(B)`
violate (T), and residues leave `{2,3}` one step later. Every non-Case-5c
configuration is automatically safe (in particular all triangles through `k`, and all
`k`-containing tetrahedra, are safe — the earlier "open core" is *closed*). Therefore,
by induction from coherent `C`:

> **Goal ⟺ (R1): no quiver reachable from `C` has a bad window.**

Equivalent forms of (R1), all verified on the component: with `r_x=q_x/p_x`,
**never `r_m<a<r_o`**; equivalently, `μ_k` never creates a **vortex** on `{m,o,k,l}`;
equivalently, **mutation-abundant ⟺ vortex-free** for `[C]`. (R1) is verified: 0 bad
windows in 526,756 Case-5c configs on the component.

## 4. Obstruction (proven): (R1) is NOT local

Let `Y = (2,-2,-2,3,2,7,-2,3,2,2)`. `Y` is **coherent** (abundant, all residues `±2`,
(T) on all 10 triangles) and **vortex-free**, yet has a **bad window** at
`(k,l,m,o)=(0,1,2,3)`: `a=2`, `v_m=(q_m,p_m)=(2,2)`, `v_o=(7,2)`, so `flip_m` (`2<4`)
but not `flip_o` (`7≮4`); and `μ_1μ_0(Y)` has an entry `≡4 (mod 5)`.

> **Consequence.** (R1) does **not** follow from abundance + (T) + vortex-freeness,
> nor from any property they imply. Any proof **must** use reachability from `C`
> (i.e. distinguish `[C]` from `Y`). No pointwise/local certificate can exist.

This is why the `(residue,sign)` automaton never saturates, and why every pointwise
inequality tested has failed.

## 5. The route: tameness normal form (finite skeleton identified)

The clean form of the remaining problem. `(R1) ⟺ [C] vortex-free ⟺ forkless part of
`[C]` vortex-free` (unification + forks are vortex-free, Burcroff), and vortex-freeness
is a pure **sign-pattern** (tournament) condition. So:

> **Remaining lemma (⟺ R1):** the forkless part of `[C]` realizes exactly **22**
> sign-patterns (all verified vortex-free). Then `[C]` is vortex-free, hence
> mutation-abundant.

`[C]` grows **quadratically** (`#{maxent≤t} ~ t^1.93`), so it is *tame*: the forkless
part is the **stratum tree** `X_m=(μ₂μ₀)^m C → Y_m=μ₄X_m → Z_m=μ₂Y_m → …`, each stratum
an affine family with entries linear in a parameter. Though infinite and quadratic in
*magnitude*, it realizes only **22 sign-patterns**, saturated by cap 100 and constant
through ~250× growth (to 249,342 forkless quivers at cap 1600).

**The finite skeleton (computed).** Enrich each state to `(σ, cvec)` where `cvec` = the
30 flip-predicates `[|b_ij| < |b_ik||b_kj|]`. The forkless part realizes exactly **110
refined states** (saturated cap 100, constant through 80× growth), and the **sign-successor
`σ'` is deterministic** given `(σ,cvec,k)` (0/332 non-unique; residual nondeterminism is
only in `cvec'`, ≤3 outcomes). This 110-state, sign-deterministic automaton is almost
certainly the **finite shadow of the stratum tree**: 110 refined states ↔ stratum
families, deterministic sign-transitions ↔ the *tropical* (leading-coefficient) mutation
dynamics (for large parameter, `|b_ik||b_kj| ~ t²` dominates `|b_ij| ~ t`, so flip
decisions stabilize and the transition becomes deterministic).

**The 110 states are listed in `forkless-110-states.md`** — each with its sign-pattern,
a small and a large representative quiver (the affine family is the interpolation:
entries linear in the parameter, `±2`s fixed), and the full transition automaton. All
110 are *attractors* (recur at unbounded magnitude — no transient near-core states), so
the 110 refined states **are** the stratum families (≈5 per sign-pattern). E.g. `s0`:
small `(-17,-18,-2,2,-2,-8,-7,-7,-8,-2)`, large `(-1197,-1198,-2,2,-2,-598,-597,-597,-598,-2)`
— affine with the `±2`s fixed and the rest growing linearly (note: coordinates can have
*different* slopes, e.g. entries 0–1 by 10/step and 5–8 by 5/step, so the family may be
multi-parameter; the small/large reps fix the direction to fit). Classify these 110
families in closed form and the proof reduces to finitely many mutation identities.

**★ The mechanism (verified) — mutation is piecewise-affine on the forkless part.**
Each family has several coordinates **frozen at ±2** (the rest grow linearly in ≤2
parameters). So every product `b_ik·b_kj` that fires under a forkless-preserving mutation
has a **frozen ±2 factor**, making `μ_k` an **affine map** on the family. Verified:
in 60,000 forkless→forkless mutations of large quivers, **0** fire a product of two
growing coordinates. The *only* nonlinearity is fork exits: **100%** of forkless→fork
mutations fire a quadratic (both-growing) product — the entry blows up, the result is a
fork (vortex-free, harmless by Burcroff). So *quadratic product ⟺ fork exit*. Concrete
anchor: `μ_0(s0-small) = s83-small` exactly. The families have affine **dimension ≤ 2**
(12 one-parameter, 98 two-parameter — hence the quadratic growth), so the closure is
finite linear algebra over 2-D parameter cones.

**Proof skeleton (now concrete and bounded).** (i) Classify the 110 families as affine
forms in ≤2 parameters, identifying the frozen ±2 coordinates — once these are pinned,
"every fired product has a ±2 factor" is a *structural fact* (affine at all scales, not
just observed). (ii) Verify mutation maps each family to its successor family (or a fork)
by a finite affine identity over the 2-D parameter cone, with the cvec-constancy
inequalities delimiting the cone pieces (affine functions are monotone, so endpoint
agreement extends across the cone). (iii) Read off that all 22 sign-patterns are
vortex-free ⟹ (R1). The invariant is **membership in the union of the 110 explicit affine
families** — magnitude-sensitive, `Y`-false, and *not* the `(σ,cvec)` shadow (so the §6
phantoms do not apply). This is paper-scale but a fully **bounded, finite** computation.

**Supporting proven structure (available to the classification).** The Reduction
Theorem (§3); windows are **chain-terminal** (`μ_k` breaks coherence, `μ_l` kills or
role-swaps the window; `⟨μ_k,μ_l⟩`-chain from a window visits ≤2 quivers — validated by
`μ₁(Y)`); the **creation taxonomy** (first-window `B_n=μ_j(B_{n−1})` has `j≠k`; `j=l`
parameterized; open core `j∈{m,o,f}`); conserved along windowless stretches `a`,
`e=|b_mo|` (frozen), `Q_a(v_x)`, `g`, `|D|`; flips strict (`q_x≠ap_x mod 5`); `5∣D` in
Case-5c. A *descent* organized around window creation (not transport) is the alternative
to classification, with `D2` (creation by `μ_f`, 5-dimensional) the open core.

## 6. Ruled out — do not retry

- **Any certificate reading only `(residue,sign)` data** — impossible by §4 (`Y` is
  coherent+vortex-free with a window). A *magnitude*-sensitive, mutation-stable,
  `Y`-false invariant is **not** excluded (that is the goal, §5) — but every concrete
  candidate has failed:
  - Inequalities in `(a,q_m,p_m,q_o,p_o)`: `g_o≥g_m`, `q_m≥q_o` on `(T,T)`, `D≥0`;
    and in `e`: `q_o≤q_m e`, `p_m≤e p_o`. All FALSE.
  - Conserved-tuple degeneracies: `Q_a(v_m)=0` (95,620 configs), `g=0` (191,236) —
    both occur throughout `[C]` in *safe* configs, so they don't separate `Y`. The
    whole tuple `(a,e,Q_m,Q_o,g,|D|)` fails to separate.
- Global congruence invariants: **Smith normal form does NOT separate `[C]` from `[Y]`**
  (`C≅Y`, both `(1,1,1,1,0)`) — no linear-algebra invariant will; the separation is
  purely reachability. The radical vector `u` (magnitude unbounded, `sum(u)` not
  conserved) also gives no clean separator.
- The `(residue,sign)` finite automaton (non-saturating). Even-sector lemma (`C` has
  odd entries); vertex gauge `ε_ij=t_ij u_i u_j` (inconsistent at `C`).
- **Local One-Step Closure of the 22 sign-patterns — FALSE.** For the sign-pattern
  automaton, of 392 escaping `(σ,k,S)` triples, **0** are killed by the log-linear flip
  constraints; and **phantoms exist** — abstract forkless quivers with a 22-pattern whose
  forkless mutation escapes the 22 (incl. to vortex patterns), *even when abundant*. So
  no local "sign + one-step magnitude" argument proves the remaining lemma.
- **Comparison-abstraction CEGAR — does not close.** The 110-refined-state automaton
  (above) is finite and closed *on `[C]`*, and it correctly excludes the sign-phantoms
  (their `cvec ∉` the 110). But **refined-phantoms exist too** (a non-`[C]` forkless
  quiver with a legitimate 110-state whose forkless mutation escapes, found in ~35
  samples). Phantoms recur at every finite abstraction level ⟹ the reachability
  separation is **not finitely abstractable**; only the global classification (§5) works.
  Use the 110-state automaton as the *skeleton to classify*, not as a self-contained
  invariant.

## 7. Harness

Python; `probe17_forkless.mutate(tuple,k,PAIRS,5)` is §1's rule. Any proposed
invariant must hold on the cap-900 component (87,620 quivers / 526,756 Case-5c
configs), be mutation-stable, and be false at `Y`.
