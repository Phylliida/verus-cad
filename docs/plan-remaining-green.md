# Plan — closing the remaining green gap in tactus-algebra

*2026-07-19. State: **98 verified / 102 errors**, 8 Rational axioms
fully green (`axiom_eqv_transitive`, `axiom_le_transitive`,
`axiom_add_associative`, `axiom_mul_associative`, `lemma_add_parts`,
`lemma_denom_pos`, `lemma_eqv_zero_iff_num_zero`, `lemma_mul_parts`);
72% of the corpus (627/874 theorems) script-authored. Tracker:
`tactus-quadratic-extension/board/cad-15-lean-gate-blocker.md`.*

***Update 2026-07-20.** State: **107 verified / 86 errors**. Items 1
(apply-guard + den-small), 3 (one_ne_zero), and the Eq half of 2
(congruence) LANDED — via four mechanisms rather than the two
sketched: the eliminator apply-guard (item 1a as planned), the
trait-impl body-refs closure (1b turned out to be the projection
unfolding stranding `from_int_spec`, not the rung), form G
(goal-only collapse for trait-projection heads — the den-small
postconditions were maxRecDepth loops, not unfold gaps), and the
NONLIN-scope hoist + rewrite-ladder (item 2: the cancel
generalization that actually landed is `rw` of definition hyps +
kernel×monomial, NOT a smarter `cancel_target`; mul_congruence and
the `le_*` half remain — their certificates need num-atom monomials
and inequality kernels). recip_congruence 5→4 as a side effect.
Remaining: the `le_`/mul-congruence half of 2, item 4 (distributes,
2), item 5 (recip family, now 4+1), item 6 (pmul family, ~60), and
2 divmod whnf timeouts. Full mechanism notes: N3 design doc lessons
13–17.*

***Update 2026-07-20 (pm).** State: **112 verified / 76 errors**.
Items 2 (full congruence family) and 4 (distributes) LANDED, under
the transparency/predictability law (compute certificates, never
menu for them): the menu sketched under item 2 was replaced by the
quotient derivation (multiset-diff of goal vs kernel monomials),
the R3/R4 le-multipliers (shape-derived positivity proofs,
complement rule for two-sided congruence), the partial hoist
(Bool-lets as goal-position residue lets — distributes' anonymous
requires), and the denom-injectivity arm (`.den` equalities from
`denom` equations). Two emission-bug classes found and fixed:
by-haves swallowing `;`-chains (`:= by tac;` → `(by tac)`), and
application-precedence on bare pp-atoms as function args
(`mul_self_nonneg (…)`). Remaining: item 5 (recip family, 3), item 6
(pmul family, ~60), divmod timeouts. N3 design doc lessons 18–23.*

The remaining 102 errors fall into six shapes, each with a known
mechanism. Ordered by yield-per-risk; every item names the files and
the failure mode it retires.

---

## 1. den-small equalities + the apply-arm misfire (7 obligations)

**Sites:** `axiom_add_zero_right` (241, 244), `axiom_mul_one_right`
(345, 348), `axiom_mul_zero_right` (356), `axiom_add_inverse_right` (280).

**Shape.** `az.num = a.num * 1 + 0 * a.denom()`, `a1.den = a.den`,
`s.num * 1 = 0 * s.denom()`. The reported error is
`apply failed: could not unify lib.seq.lemma_seq_two_subranges_index`
— an eliminator arm firing a seq lemma against an arithmetic goal it
can't possibly match. That error is *masking*: the real failure is
upstream (the structural rung not closing the
`zero`/`from_int_spec`/`add_spec`/`mul_spec` definition chain), and
the eliminator misfire is just the last error standing.

**Fix (two parts).**
- (a) Guard eliminator arms by a head-symbol match: only emit
  `apply <lemma>` when the goal's head symbol unifies with the
  eliminator's conclusion head (`Seq.index`/`Seq.subrange` vs
  `Rational.num`). One-line check in `derived_closer`'s elim-arms
  construction (`tactic_select.rs`). Kills the misleading error and
  avoids a wasted arm everywhere.
- (b) The underlying close: the goals need the
  `zero → from_int_spec → add_spec/mul_spec → field projections`
  unfold chain then omega/nlinarith. The transitive closure (landed)
  covers the spec-fn bodies; verify per-site whether the rung's
  failure is the `zero` class-projection unfolding (should work —
  it's a trait method in the unfold set) or the
  `from_int_spec`-of-zero reduction. Expect (a) to reveal that most
  of these close with the current rung once the eliminator arm stops
  wasting the error slot.

**Mechanics:** tiny. Do first.

---

## 2. Congruence chains — cancel in more shapes (8 obligations)

**Sites:** `axiom_add_congruence_left` (257), `axiom_mul_congruence_left`
(397), `axiom_le_add_monotone` (472), `axiom_le_congruence` (434),
`axiom_le_mul_nonneg_monotone` (491, 493), `axiom_neg_congruence`,
`axiom_sub_is_add_neg`.

**Shape.** `ac.num * bc.denom() = bc.num * ac.denom()` (or ≤), with
the eqv fact and the closed forms (from `lemma_add_parts` /
`lemma_mul_parts`) in context. The ladder's cancel branch fires but
its single-denominator cancel is insufficient: the shared factor is
a *product* (`dc·dc` for add/mul-congruence, `da·db·dc` for the
associativity-shaped ones, `dc` for transitivity). Current error:
`by(nonlinear_arith) scope: could not close`.

**Fix.** Generalize `cancel_target` (tactic_select.rs) to compute the
cancel atom as the **shared factor of the goal's cross-multiplied
sides**: walk the two sides of the Eq/Le goal, take the
denominator-application atoms appearing in *both* sides'
multiplicative factors, and use their product as `D`. Validated
shapes: `dc` (transitivity, landed), `dc²` (congruence), `da·db·dc`
(assoc-shaped). Positivity for a product of denominators: derive
`D ≠ 0` from the per-factor positivity hyps (or
`simp only [denom, denom_nat]; omega` on the factors — positive by
construction). Everything else in the branch (the
congrArg-multiplied pool + `mul_eq_zero.mp + resolve_left`) is
unchanged.

**Mechanics:** contained in `cancel_target` + the positivity
derivation. The pool already works (proven on transitivity).

---

## 3. `axiom_one_ne_zero` (1 obligation)

**Shape.** `¬eqv(from_int 1, from_int 0)` = `¬(1·1 = 0·1)`. With eqv
inlined and `from_int_spec` in the closure, this is
`simp only [eqv-instance, from_int_spec]; omega` — or even
`by decide` after unfolding. Investigate why the rung misses it
(likely the `from_int_spec` value-of-`zero`/`one` projection needs
the class-projection `zero`/`one` unfolded *through the instance*,
then `from_int_spec` of a literal). Expect a one-line unfold-set or a
`decide` arm addition.

**Mechanics:** tiny; pairs with item 1(b).

---

## 4. `axiom_mul_distributes_left` (2 obligations, 378, 383)

**Shape.** The `r.num = a.denom() * l.num` scaling form (the
`lemma_distrib_scale` helper's output consumed in-place). Needs the
`a.denom()` scaling cancellation (`r.num = da · l.num`,
`r.denom() = da · l.denom()` ⟹ cross-multiplied equality). A cancel
shape with `da` as the cancel atom — item 2's generalized cancel
covers it. Verify after item 2; expected to close for free.

---

## 5. The recip sign-split family (6 obligations)

**Sites:** `axiom_mul_recip_right` (531), `axiom_recip_congruence`
(549, 569, 588, 589, 590).

**Shape.** `reciprocal_spec` is a three-way if (`num > 0` / `num < 0`
/ `num = 0`). The goals are per-case: sign agreement from the eqv
hyp, then the per-case cross-multiplied equality. The proof already
has the case structure in the Rust body (`if a.num > 0 { … } else {
… }`), so the obligations arrive with the case conditions as branch
hyps — form A's `split` family should fire once the
`reciprocal_spec` definition is in the unfold set. The real work:
unfold `reciprocal_spec` (it's in the non-recursive closure) on the
goal, split the sign cases, and close each with the
congruence/transitivity machinery from items R1/2. `num = 0` case is
the contradiction-by-eqv branch (`a ≡ 0` is excluded by the
requires).

**Mechanics:** form A with `reciprocal_spec` in the unfold set +
per-case nlinarith with the sign hyps. Expect a small new script
arm only if the generic split doesn't fire; validate on 531 first
(single site, cleanest case).

---

## 6. The pmul eqv-family (~95 obligations, the big one)

**Sites:** `lemma_pmul_push` (10), `lemma_pmul_comm` (8),
`lemma_pmul_singleton_right` (8), `divmod` (6),
`lemma_pmul_shiftk_right` (6), `lemma_cons_as_padd` (5), `lemma_pmul_pad`
(5), `lemma_pmul_padd_right` (5), `lemma_pmul_pneg_right` (5),
`lemma_pmul_scale_right` (5), `lemma_drop_last_peqv` (4),
`lemma_pmul_assoc` (4), `lemma_pmul_empty_right` (4), and ~15 singles.

**Shape.** `peqv` congruence/distributivity chains where the goal's
final fact is a 2-link transitivity away, not a direct hyp (form C
covered the 1-link case). E.g. `peqv (pmul (push p c) q) (padd (pmul
p q) (shiftk (scale c q) (len p)))` from the IH + the shiftk/padd
congruence facts. The proof needs `peqv`-trans/cong *applied* to the
named facts, not just `exact`.

**Fix (form C+).** A new move `ApplyLemma(name, args)` rendering
`exact <lemma-app>` or `apply <lemma>` where the lemma is the
crate's own `lemma_peqv_trans` / `lemma_padd_cong` /
`lemma_shiftk_cong` / `lemma_pmul_cong_*` — with the args taken from
the goal's two endpoints and the middle term read off the available
hyps (the emitter holds all the texts: goal `peqv X Z`, hyps `peqv X
Y`, `peqv Y Z` → `lemma_peqv_trans(X, Y, Z)`). Sequenced as a
bounded chain search over 1–2 links (find `peqv X Y` and `peqv Y Z`
in the shape, emit the trans application; for congruence, emit
`padd_cong`/`shiftk_cong` on the goal's top structure). divmod's
structural remnants (the `pad`/`push` positional quotient cases) get
the same 2-link treatment via `lemma_padd_cong` + the divmod IH.

**Mechanics:** the biggest single item (~95 obligations), but highly
repetitive — one good chain-author covers the family. Prerequisite:
nothing new; the shape/CallFact provenance is all there.

---

## Ordering & gates

1. **Item 1** (apply-guard + den-small) — tiny, unmasks the real
   failures; expect several of 1/3 to fall out.
2. **Item 2** (generalized cancel) — retires the congruence class
   (8) and probably item 4 for free.
3. **Item 3 + 4** — verify; small.
4. **Item 5** (recip family) — the only new script shape if the
   generic split doesn't fire.
5. **Item 6** (form C+, pmul family) — the bulk of what remains
   (~95 obligations); the chain-author is the main deliverable of the
   next milestone.

**Gate discipline (unchanged):** every item lands with
`./check.sh` on tactus-algebra (error count + verified count, no
fn-level regressions), `vargo test -p rust_verify_test` (138/140
modulo the 2 known pre-existing state_machines failures), and the
lean_verify unit suite. The N4 census line must never lose script
share (the ratchet).

**Success metric:** 102 → ≤ 30 errors, ≥ 105 verified fns, all 24
Rational impls green. The pmul family is the long tail; everything
else is known shapes.
