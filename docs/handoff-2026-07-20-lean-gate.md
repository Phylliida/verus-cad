# Handoff — Lean-gate arc, 2026-07-20

*For the next session. State on entry: **98 verified / 102 errors** in
tactus-algebra. State now: **114 verified / 72 errors**, all 24 Rational
impls green, bare `simp_all` extinct in emitted tactic text. The work is
committed; the pmul family (~60 obligations) is the only big item left.*

---

## 1. The principles (load-bearing, evolved this session)

Danielle's rules, in order of how much they shaped the work:

1. **Transparency** — what the automation does is visible to the user:
   every certificate is a readable `have` in the artifact, every arm is
   a named step, every failure names its obligation.
2. **Predictability** — each rule is statable in one sentence and fires
   deterministically. Compute certificates; never menu for them. Caps
   and menus are silent luck and are out.
3. **Inline proofs are PREFERRED to more emitter machinery.** A loud
   failure pointing at a `proof {}` block beats another arm. When an
   obligation is awkward, prove it in the crate, predictably — do not
   grow the emitter to cover it.
4. **Bare `simp`/`simp_all` without named things is out** — it is both
   opaque and version-unstable (the default simp set drifts with
   Mathlib). Every emitted simp is `simp only [named things]` now.

The daily application: every arm/mechanism was judged by "is it one
sentence, and does it fail loud?"

## 2. What landed, arc by arc

### Congruence arc (tactus `edd5a51`)

Mechanisms: eliminator apply-guard (eliminator arms only fire when the
conclusion's LHS head matches the goal's); `spec_fn_body_refs` closure
through trait-impl bodies (simp's projection unfolding strands
`from_int_spec` — `zero := from_int_spec 0` inline); form G (goal-only
collapse for trait-projection-headed goals: `intros; simp +zetaDelta
only [COLLAPSES, unfolds] at ⊢; first | omega | done`); NONLIN-scope
hoist (`by(nonlinear_arith)` AssertQuery obligations hoist so requires
arrive NAMED) + the rw-ladder (rw definition hyps into the goal, then
congrArg-multiply the kernel hyp by a denom monomial — `dc*dc` falls
out of the multiset quotient `{a.num,dc,db,dc} − {a.num,db}`).

Green: den-small family complete, `one_ne_zero`, `div_is_mul_recip`,
`neg_congruence`, `sub_is_add_neg`, `add_congruence_left`.

### Certificate-computation arc (tactus `8dcac64`)

The rw-ladder's capped monomial MENU was replaced by the **quotient
derivation** (compute the certificate as multiset difference of the
definition-folded goal's and kernel's monomials — never enumerate).
R3/R4 le-multipliers: `mul_le_mul_of_nonneg_right` with shape-derived
positivity proofs (square → `mul_self_nonneg`, hyps otherwise);
two-sided congruence via the complement rule (each fact multiplied by
the denominators it does NOT mention; cancel by the inequality's own
denominators, `mul_le_mul_iff_left₀`). Partial hoist: Bool-lets become
goal-position residue lets, everything else hoists (Prop equations stay
out of the telescope — the nested_if simp hazard). Denom-injectivity
arm (`.den` equalities from `denom` equations; `denom x = ↑(x.den+1)`).

Green: `mul_congruence_left`, `le_add_monotone`, `le_congruence`,
`le_mul_nonneg_monotone`, `mul_distributes_left`, add/mul associativity
healed.

### Pool experiment + infra review (tactus `6242e26`)

`TACTUS_NONLIN_NO_POOL=1` corpus: **132 obligations across ~45 fns fail
without the congrArg pool arm** — it is the workhorse, not search-debt.
The menu-vs-tactic distinction (lesson 24): the pool arm is ONE
deterministic `nlinarith` call with a fixed, visible, computed fact set
— the internal search lives inside nlinarith, same genus as omega's.
Rule + caps (≤8 multiplier atoms, ≤12 haves, emission order) now
documented at the emission site. The R-arms are the cap-free computed
backstop behind it. The env flag stays as an attribution tool.

### Recip sign-split arc (tactus `6e5be0d`)

Two mechanisms: (a) False-elim arm in the kernel ladder — `cases h` on
`LitBool(false)` binders (`False` is NOT a `Var` node — the first
version silently never fired; `assert(false)` in a branch makes every
downstream obligation in that branch vacuous); (b) targeted ite-collapse
leg `simp_all only [if_pos, if_neg, if_true, if_false] <;> omega` as
BACKSTOP behind the wild `simp_all`. The recip sign legs need the ite
collapse AFTER `split` peels the outer guard.

Green: all 24 Rational impls (item 5 of the plan complete).

### Named-simp arc (tactus `76eafee`)

Every leg simp is now `simp_all only [LEG_SIMP_LEMMAS]` (ite-collapse +
a trimmed arithmetic normalizer; deliberately NO `ofNat_toNat`). Zero
semantic delta vs the wild-set baseline. The wild simp's work decomposed
(lesson 29): broadcast-have rewrites fire under `only` regardless; the
DEFAULT-SET arithmetic collapse (`mul_zero`, `ofNat_eq_coe`) was the
invisible, version-unstable part now made explicit.

### Termination pass (tactus `cb1ebc4`)

Every termination/`decreasing_by` arm named (`TERM_SIMP_LEMMAS` =
LEG + `Int.natCast_sub` — the `↑(n - m)` collapse divmod's
`toNat (n - len b)` termination needs). Covered: datatype-height
`simp_all`, WF-height `simp [height]`, the DecreasingKind ladder family
(SeqSubrange/SeqDropFirst/SeqDropLast/Div/Ladder + the mono chain), and
the mono-companion theorem. e2e gate held (138/140, 2 pre-existing).
Bare simp is extinct in emitted tactic text outside the legacy
`tactus_auto` discover-mode path.

### Wrapper fixes + seq-rw experiment → reverted (tactus `2b036a9`)

Kept at zero delta: `let_descend` (gates now look THROUGH N1's trailing
equation wrapper `let tmp := v; tmp` instead of landing on the bare
`tmp` var — it was hiding every pmul goal's Eq core from the gates);
Trigger-peel in the eliminator head extraction (the seq axioms' ensures
arrive `Unary(Trigger, …)`-wrapped — every eliminator head was `None`,
so the apply-guard was blind); `comparison_core` gets the same wrapper
treatment.

Reverted: the seq-rw arm (`rw [broadcast lemma]; simp_all [13 axioms]
<;> omega` for side-conditioned seq rewrites). Validated on hand probes
(t92–t94 closed instantly), but on the corpus it burned the 800k
heartbeat budget on divmod/pmul-sized contexts — consistently
net-negative no matter how the firing was tuned. That was the tell that
its economics, not its shape, were wrong for this family.

## 3. The emission bug classes (worth memorizing)

These cost real hours; each is now a lesson in
`tactus/DESIGN-N3-provenance-scripts.md` (lessons 13–30):

- **By-swallow**: `have x : T := by tac;` inside a `;`-separated
  single-line chain SWALLOWS the rest of the sequence into the by-block.
  The by's goal closes, then "No goals to be solved" kills the arm
  invisibly. Always `(by tac)` in emitted chains. Latent in the cancel
  branch since R2.
- **Application-precedence**: bare pp-atoms spliced as function ARGS
  need parens — `mul_self_nonneg lib.Rational.denom c` parses as
  `(mul_self_nonneg lib.Rational.denom) c` (the FUNCTION squared).
  Same class as the congrArg pool's `(X + Y) * d ≠ X + Y * d` (not
  defeq → elaboration kills the primary).
- **Trigger wrappers**: VIR ensures arrive `Unary(Trigger, …)`-wrapped;
  head extraction must peel them or every match is `None`.
- **The trailing equation wrapper** (`let tmp := v; tmp`): hides the
  goal core from any gate that peels `Let → body`. Look through to the
  VALUE when the body is the same var (N1's spine rule). It has now
  broken three separate gates (denom-inj, seq-rw, elim-guard).
- **`False` is `ExprNode::LitBool(false)`**, not a `Var` — any
  shape-sniff on it must match that node.
- **congrArg is a TYPE CHECK**: Rational-Eq hyps must be excluded from
  the Int-multiplier pool by a structural Int-side check.
- **simp's side-condition discharger can't do arithmetic** — the seq
  broadcast lemmas' `0 ≤ i ∧ i < …` conditions exceed it; `rw` (which
  leaves conditions as plain goals) + omega is the robust discharge, but
  the 13-axiom simp_all version of that discharge is too expensive on
  big contexts.
- **`simp_all only [X]` DOES use context hyps as rewrites** (probed);
  `simp only [X] at ⊢` doesn't need hyps.
- **Heartbeat budget classes**: `simp_all` whole-context mangling is a
  CATCHABLE failure; maxRecDepth / whnf timeout is UNCATCHABLE (kills
  the whole chain before backstops run); `+zetaDelta` on big contexts is
  substitution blowup.
- **`nlinarith` is NOT import-safe**: per-obligation artifacts import
  `Mathlib.Tactic.Linarith` only when the fn has a
  `by(nonlinear_arith)` scope (the 32/275 "unknown tactic" regression).
  `omega`, `simp`, `rfl`, `cases` are always safe.

## 4. Measurement caveats (do not re-learn these)

- **The census double-reports**: `error: Lean tactic failed for X:`
  lines can appear 2–3× per obligation (fn-level + package-gate).
  fn-level uniq counts are ±1–2 fuzzy. The verifier's totals
  (`N verified, M errors`) are the truth; reconcile fn counts against
  them before believing a regression.
- **Budget-edge flakes are real**: byte-identical theorems can fail
  under corpus load and close standalone (pmul_push 223:16,
  coeff_shiftk 178:13). Heartbeats are supposedly deterministic but
  diverge between standalone and corpus contexts — MECHANISM UNKNOWN
  (a reproducibility hazard worth its own investigation).
- **Always verify a suspected regression standalone** before chasing it
  (extract the theorem, run `lean` with the right LEAN_PATH).
- **Emission caching masks tactic changes**: `find target/tactus-lean
  -name '*.lean' -delete` before a check run when artifacts look stale.
- **Build**: `cd tactus/source && source ../tools/activate && vargo
  build --release` (activate in EVERY new shell).

## 5. Current state (the 72)

`verification results:: 114 verified, 72 errors, 233 cached`; N4 census
`627 script (A:416 B:31 C:180) / 213 rung:formE / 34 rung-only` (72%
script share, unchanged all session). rust_verify_test 138/140 (2
pre-existing state_machines failures, Z3-path, not ours). lean_verify
unit 407/407.

Failing obligations by fn: pmul_push 8, pmul_singleton_right 7,
cons_as_padd 5, pmul_shiftk_right 4, pmul_padd_right 4, pmul_comm 4,
drop_last_peqv 4, divmod 4, pmul_scale_right 3, pmul_pneg_right 3,
pmul_pad 3, shift1_left 2, pmul_one_left 2, pmul_empty_right 2,
pmul_cong_right 2, pmul_assoc 2, coeff_shiftk 2, + 15 singles
(shiftk_zero/pneg_swap/padd/compose_inner/compose, scale_shiftk,
pmul_psub_right/left, pmul_padd_left, coeff_padd, coeff_pad).

Failing obligations by closer class (the real shape map):
**script:formA 45, rung:formE 18, rung-only 4, formC 3, formB 2.**

Their shapes, from the triage (2026-07-20):

- **The seq side-condition family** (dominant): asserts like
  `p.push(c)[0] == c`, `index (new n f) i = f i` — the broadcast seq
  lemmas are conditional rewrites whose bounds (`0 ≤ i ∧ i < len`) simp's
  discharger can't prove. `rw [lemma]; <bc rewrites>; omega` discharges
  trivially by hand (probes t92–t94). The emitter arm version of that
  discharge was too expensive on big contexts and is reverted.
- **Let-wrapped guard conjunctions** (drop_last_peqv 367:27-style):
  `let tmp := 0; let tmp1 := i; let tmp2 := len p - 1; tmp ≤ tmp1 ∧
  tmp1 < tmp2` as a hyp — omega can't consume the let-wrapped form.
- **Budget-edge flakes** (223:16, 204:9, coeff_shiftk 178:13):
  byte-identical closers that pass standalone.
- **A few transitivity/congruence chains** (the plan's original form C+
  shape — rare in the census, ~5 obligations).

## 6. The path forward (start here)

Per Danielle's steer (2026-07-20, this session): **inline proofs in the
crate, not more emitter machinery.** The goal is not for automation to
prove everything; a loud failure + a predictable `proof {}` block wins.

First batch (cleanest, highest-value): **pmul_push's rung-only asserts**
(poly_mul.rs:165, 166, 190, 191 — the `p.push(c)[0] == c` /
`p.push(c)[i] == p[i-1]` shapes). Each is one broadcast-lemma
application + one arithmetic guard. In Verus terms the proof is small
and mechanical — assert the intermediate facts so Z3/Lean both see the
chain:

```rust
// before: assert(p.push(c)[0] == c);
proof {
    // len (push p c) = len p + 1 = 1 (branch: len p = 0);
    // index (push p c) 0 = c by push_index_same with 0 = len p.
    assert(p.push(c).len() == 1);
    assert(p.push(c)[0] == c);
}
```

Note the Z3-vs-Lean asymmetry: Z3 closes these via broadcast lemmas +
nlsat already; the Lean path needs the manual discharge chain spelled
out — the proof block makes the steps explicit AND predictable, which is
exactly what the principles ask for.

Then the rest of the seq side-condition family in pmul_singleton_right,
cons_as_padd, pmul_shiftk_right, padd_right, drop_last_peqv — same
pattern (assert the intermediate len/index facts inline; the closers'
remaining work collapses).

Do NOT rebuild the seq-rw arm. If a general mechanism ever returns for
this family, it must be budget-shaped (no 13-axiom simp_all after `rw`).

## 7. Session commits

tactus: `edd5a51` (congruence arc), `6242e26` (pool resolution),
`6e5be0d` (recip arc), `76eafee` (named-simp, amended), `cb1ebc4`
(termination pass), `2b036a9` (wrapper fixes + seq-rw revert).

verus-cad root: `a73a7b0`, `30bf68c`, `853860d`, `e9a1746`, `75d51a3`
(plan doc updates through the session).

board (tactus-quadratic-extension): `2eeae7c`, `f849014`, `ed25416`,
`5cc4a32`, `64186f7`.

Design doc `tactus/DESIGN-N3-provenance-scripts.md`: lessons 1–30 are
the running record (13–17 congruence arc, 18–23 certificate computation,
24 pool, 25–28 recip, 29 named-simp decomposition, 30 termination).

## 8. Remaining debt (documented in `docs/plan-remaining-green.md`)

- `take(3)` on `structural_rung`'s cases targets — hidden cap, make it
  visible in the census.
- Failure legibility for default-scope obligations — add a trailing
  `fail` arm with the `proof {}` remedy (AssertQuery has it; default
  scope doesn't).
- Broadcast haves consumed by simp search — watch item; direction is
  more goal-directed application.
- Heartbeat variance (corpus vs standalone) — mechanism unknown,
  reproducibility hazard.
- The pool arm's caps are documented but still caps — fine for now
  (the R-arms are the cap-free backstop).
