# Handoff — Lean-gate arc, 2026-07-21

*For the next session. State on entry: **114 verified / 72 errors** in
tactus-algebra. State now: **117 verified / 51 errors** (118 without
`-V cache` — one budget-edge fn flaps). pmul_push
8→2 (both budget-class), pmul_one_left green, all 9 recursive-pmul
termination obligations green, pmul_comm 890-class green. Census:
scripts 627→648 (formC 180→381, formA 416→236) — the ratchet gained
share. Gates: lean_verify unit 409/409; rust_verify_test 138/140
(the 2 failures are the pre-existing state_machines ones —
`examples_state_machines_tutorial_fifo`,
`examples_state_machines_flat_combine` — Z3-path, not ours).
Work is committed in both repos.*

---

## 1. What landed, arc by arc

### Inline seq-axiom calls (tactus-algebra `ef41603`)

The handoff's batch-1 directive: crate-inline proofs, not emitter
machinery. The working pattern for the seq side-condition family is
**explicit `vstd::seq::axiom_*` calls in the proof body**. Each call's
`requires` becomes an omega-closable *arithmetic* obligation (the
rung closes those fine), and its `ensures` arrives as a *ground*
rewrite hyp the closers apply with no side conditions — the inline
alternative to the reverted seq-rw arm, and it respects the "compute,
never menu" law: the facts are named and visible in the artifact.

Recipes (all validated — see §3 for the failure shapes they retire):

- **`s.push(c)[0] == c`** (or any literal index): call
  `axiom_seq_push_index_same(s, c, 0)` — the ret-hyp IS the goal;
  `requires 0 == s.len()` discharges by omega from the branch hyp.
  For `0 <= i < s.len()` positions use `axiom_seq_push_index_different`.
- **`skip(1)` termination/len facts**: call
  `axiom_seq_subrange_len(p, 1, p.len() as int)` right after
  `let t = p.skip(1);` — the recursive-call decreases obligation
  becomes omega-closable. Landed at 9 sites; every one went green.
- **`skip(1) =~= empty/t.push(c)`** (seq-level `=~=`): decompose via
  `axiom_seq_subrange_len` + a len assert + an
  `assert forall|i| 0 <= i < s.skip(1).len() implies ... by {}`
  (empty by-block; omega closes the vacuous/body cases from the len
  fact) + `axiom_seq_ext_equal(a, b)` before the final assert.
  pmul_push 166/191 and pmul_one_left 1000 green this way.
- **Congruence bridges** (e.g. `shiftk(shiftk(x, t.len()), 1) ==
  shiftk(x, p.len())`): restate the lemma's ensures verbatim as an
  assert (closes by assumption on the ret-hyp), then a **cast-free**
  arithmetic bridge assert (`(t.len() + 1) as nat == p.len()` —
  omega), then the congruence step as its own assert, then the goal.
  Ground rewrites only; no `Int.sub_add_cancel` needed.

Z3-side cost is zero (the axioms were already broadcast).

### RefineExact syntax fix (tactus `fe8ea4c`)

`refine ⟨exact h1, exact h2⟩` is a parse error (`exact` is not a
term) — every 2-conjunct precondition obligation whose conjuncts
matched ret-hyps (form C) died on the arm and reported the LAST arm's
error (the "last error standing" class). Now renders `refine ⟨h1, h2⟩`.
Validated standalone on pmul_comm's 877. Unit test updated (it
enshrined the buggy string).

### form-C exact-match repairs (tactus `dd3c4e9`, `5fb9624`)

Two independent reasons form C declined real matches:

1. **Transparent wrappers**: antecedent props arrive as `(P : Prop)`;
   trait-zero atoms carry `(zero (Self := (T)) : T)`; SpanMarks pp as
   `/- @rust:LOC -/`. New `strip_transparent` (SpanMark + TypeAnnot)
   in `apply_let_substs` / `apply_hoist_substs`.
2. **Substitution ordering**: hoist values mention earlier-bound
   names (`tmp19 := …(t)…` with `t := subrange …`). A single ordered
   pass expanded `t` on the candidate side (direct occurrence) but
   not on the goal side (arrives only via tmp19's value, inserted
   after `t`'s subst ran). Now substitutes **to a fixpoint** (acyclic
   hoist graph; 16-iteration cap). Diagnosed via the named decline
   dump; regression test fails with a single pass, closes with the
   fixpoint.

pmul_comm 890 (and its form-C siblings) fire `script:formC` now.

### Debug tooling (tactus `7d9b75a`)

`TACTUS_DEBUG_FORMC=1` dumps `[formc] OBLIGATION / V1 / ENTER /
DECLINE / cand` lines, each suffixed with `@<obligation name>` from a
thread-local. **Emission is parallel** — unnamed dumps interleave
across obligations and pair WRONG (cost an hour: a pmul_one_left
DECLINE read as padd_right's). Off by default.

## 2. Iteration recipes (do not rediscover)

- **Standalone artifact check** (handoff's flake protocol, now
  scripted): `/tmp/lean-probe.sh <file.lean>` —
  LEAN_PATH = `~/.cache/tactus/prelude-84090a2752909865` +
  `tactus-algebra/target/tactus-lean/lib` + Mathlib path from
  `tactus/lean-project`. Reproduces corpus failures exactly.
- **Scoped verify** (~30s vs ~6min):
  `verus --lean-backend --crate-type=lib src/lib.rs
  --verify-only-module poly_ring --verify-function lemma_pmul_comm`
  (note: `--verify-only-module`, not `--verify-module`, when combined
  with `--verify-function`; and `-V cache` SKIPS authoring for cached
  fns — debug runs must omit it).
- **Full gate**: `cd tactus-algebra && ./check.sh` (writes
  /tmp/tactus-algebra-check.log). Delete
  `target/tactus-lean/**/*.lean` first when artifacts look stale.
- **Emitter rebuild**: `cd tactus/source && source ../tools/activate
  && vargo build --release`. Unit tests:
  `cargo test -p lean_verify --release` (409/409 — plain cargo, NOT
  vargo; vargo rejects the package).
- **Probing closer shapes**: extract the failing theorem into
  /tmp/probeN.lean with the bc haves + the rung's exact simp set and
  test candidate tactic shapes — 30s per probe, saved several wrong
  source edits. (Probes from this session: /tmp/probe165.lean,
  probe2/3/4/5, decline890.txt, formc-named.txt.)

## 3. The remaining 51, by class

- **Form C+ chain search (~10, the big one).** lemma-call
  preconditions whose requires need a 2–3 link transitivity chain,
  not a single-hyp match. Canonical: padd_right 564 — requires
  `peqv (pmul p (padd q r)) (padd (padd shq shr) (padd sq1 sr1))`,
  available only as the COMPOSITION of the pmul-unfold + scale_padd +
  shiftk_cong + shiftk_padd + padd_cong ret-hyps. form C matches
  single hyps only. This is the plan doc's item 6 "form C+"
  (bounded 1–2 link chain author) — the documented next mechanism.
  Sites: padd_right 564, shiftk_right 764/773, singleton_right 729,
  assoc 989, psub_right 682, shiftk_padd 126, pmul_pad 287,
  cons_as_padd 416, scale_shiftk 293, shiftk_pneg_swap 648.
- **Seq::new `=~=` family (~8).** `shiftk/scale/pad` ext-equalities.
  Structurally blocked crate-side: the goal needs poly-def unfold +
  bc_4 (new_index, arith side cond) + arith ite-collapse IN ONE
  closer. formA's split lacks the bc_4 rewrite (no ite ever appears);
  the simp_all-with-unfold arm's split legs lack omega (the
  `i < ↑0` case dies). shiftk_zero was the probe case — reverted to
  its original form after the analysis (see git history for the
  experiment). Needs a budget-shaped emitter leg (unfold + bc_4 +
  split-with-omega), NOT the reverted 13-axiom seq-rw arm.
  Sites: shiftk_zero 48, shiftk_compose 55, pmul_pad 279,
  singleton_right 705/707, shift1_left 791/792, shiftk_compose_inner 477.
- **Let-wrapped guard conjunctions (~11).** `¬(let tmp := 0; … tmp ≤
  tmp1 ∧ tmp1 < ↑tmp2)` as a branch hyp — omega can't consume the
  wrapped form. coeff_padd/coeff_shiftk/coeff_pad postconditions,
  drop_last_peqv 367/372, cons_as_padd 415/433/434/454. Emitter-side
  (the intro+subst legs DO unwrap; the failing arms don't intro
  first). Note cons_as_padd 434 also needs `x[i-1+1] ≡ x[i]` — an
  `assert((i - 1) + 1 == i)` bridge (omega) makes it a hyp-rewrite;
  probe-validated but not yet applied.
- **Postcondition assemblies (~6).** pmul_empty_right 486,
  pmul_cong_right 509, padd_right 533, pneg_right 578,
  scale_right 801, singleton_right 691 — final peqv/zpoly goals whose
  chains involve the classes above.
- **divmod (4).** 33 whnf heartbeat timeout (budget class), 57/58
  Seq::new-index of shiftk∘scale (needs new_index with the closure —
  fragile), 64 drop_last len (emits as `lib.Seq.drop_last`, not
  subrange — the axiom call won't match textually).
- **Budget flakes (2).** pmul_push 234 (simp max-steps) and 253
  (whnf timeout) — the known budget-edge class from the previous
  handoff; byte-identical closers pass standalone sometimes.

## 4. Session commits

tactus-algebra: `ef41603` (inline seq-axiom family, 72→55),
`5c5438d` (shiftk_zero revert, documented).
tactus: `fe8ea4c` (RefineExact), `dd3c4e9` (strip_transparent),
`5fb9624` (fixpoint subst), `7d9b75a` (named debug output).

## 5. Watch items / debt notes

- The shiftk_zero revert means poly_mul.rs:48 still fails — intended,
  documented above, don't "fix" it crate-side again.
- `TACTUS_DEBUG_FORMC` stays (env-gated, off by default) — same
  status as `TACTUS_NONLIN_NO_POOL`.
- The form-C fixpoint cap (16) is a bound, not a menu — the hoist
  graph is acyclic, so it always converges in ≤ spine length.
- lean_verify unit 409/409. rust_verify_test 138/140 (the 2 failures
  are the pre-existing state_machines ones — Z3-path, not ours).
