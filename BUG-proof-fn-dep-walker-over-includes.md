# Bug: proof-fn dep walker over-includes, breaking forward references

## RESOLVED 2026-06-01 — proof-fn files include only the root's transitive deps, topologically sorted

**Confirmed both issues** (over-inclusion + forward-reference order), exactly as
described. Root cause: `generate.rs`'s `krate_preamble` built `helpers_to_emit`
as *every* proof fn in the krate, emitted into *every* proof fn's file; with the
root emitted last, any over-included proof fn that depended on the root forward-
referenced it. The prior code even flagged the ordering half: *"source order
works in the common case … True forward-refs between proof fns would need
topological sort; deferred until a case surfaces."* This was that case.

**Correction to the suggested fix.** The doc's fix (1) — "apply the same
`collect_references` filter to proof fns" — *wouldn't work*. A proof fn's body is
raw Lean tactic text (a `TacticBlock` span), so VIR dep-walking can't see the
`have := double_nonneg` lemma calls — there's no VIR edge to find. The references
exist *only as text*. (That's precisely why the original code over-included all
proof fns: it had no VIR signal for "which proof fns does this one call.")

**Fix.** For proof-fn files (`PreambleConfig::ProofFn`), `helpers_to_emit` is now
the root's **transitive downward closure** — the proof fns its tactic body
references, recursively — found by **textually scanning** each tactic body for
proof-fn short names (word-boundary, `--`-comment-stripped), and returned in
**topological order** (deps first) via DFS post-order. So:
- `double_nonneg.lean` includes only `{double, double_nonneg}` — `use_double_nonneg`
  (which depends on it) is no longer dragged in → no forward reference.
- `use_double_nonneg.lean` includes `{double, double_nonneg, use_double_nonneg}`
  with `double_nonneg` first → still correct.

This does **both** the doc's (1) over-inclusion fix and (2) the proper
topological sort in one DFS pass (the closure-from-roots and the deps-first
ordering fall out together). Exec-fn files keep the safe over-approximation (all
emittable proof fns) — an exec root can't be forward-referenced by a helper (no
proof fn depends on an exec fn), so the bug doesn't arise there, and an exec
root's helper references live in `proof { }`/`assert by { }` blocks not available
at preamble time.

Known limitation: the textual scan over-approximates on a proof-fn name mentioned
in a non-comment string (rare), and a true cycle of mutually-referencing proof
fns would need a Lean `mutual` block (out of scope, not observed). Neither
affects soundness — at worst a loud forward-reference error, never a silent pass.

**Pinned by** `test_proof_fn_helper_not_over_included` (the reproducer) and
`test_proof_fn_helper_chain_topo_order` (a 3-level A←B←C chain pinning the topo
order). 477 e2e, 0 regressions. See DESIGN § "Proof-fn helper emission".

Everything below is the original report, preserved.

---

## Summary

After the recent fix that made helper proof fns visible to exec fn theorems, proof-fn → proof-fn calls *almost* work — but the dep walker that decides which proof fns to emit into each generated Lean file is **over-inclusive**. It emits proof fns that aren't referenced by the target, and the emission order causes forward-reference errors when the target's file gets a proof fn that references the target declared *before* the target.

The practical consequence: a file with two proof fns where the SECOND references the FIRST fails to verify, even though the call shape is now supported in principle.

## Minimal reproducer

```rust
use verus_builtin::*;
use verus_builtin_macros::*;

verus! {

spec fn double(n: nat) -> nat { n + n }

proof fn double_nonneg(n: nat)
    ensures double(n) >= 0
by {
    unfold double
    omega
}

proof fn use_double_nonneg(n: nat)
    ensures double(n) >= 0
by {
    have h := double_nonneg n
    exact h
}

fn main() {}

} // verus!
```

Expected: both proof fns verify. `use_double_nonneg` legitimately calls `double_nonneg`; the call shape works (matching `have _ := helper args` in Lean syntax).

Actual: `double_nonneg.lean` (the file emitted for verifying `double_nonneg`) contains BOTH proof fns, with `use_double_nonneg` declared *before* `double_nonneg`. `use_double_nonneg`'s body references `double_nonneg` — which hasn't been declared yet at that point — so Lean raises:

```
error: Lean tactic failed for double_nonneg:
       tactic line 2: Unknown identifier `double_nonneg`
```

(The "tactic line 2" attribution is wrong-shaped — the error is really at the `have h := double_nonneg n` in `use_double_nonneg`'s body, not in `double_nonneg` itself. But the file as a whole is what fails to elaborate, so the error gets attributed to whichever theorem the verifier was checking.)

## Generated `double_nonneg.lean` (excerpt)

```lean
namespace t2
noncomputable def double (n : Nat) : Nat :=
  n + n

theorem use_double_nonneg (n : Nat) :
    double n ≥ 0 := by
  have h := double_nonneg n     -- ← Forward reference: `double_nonneg` not yet declared
  exact h

theorem double_nonneg (n : Nat) :
    double n ≥ 0 := by
  unfold double
  omega

end t2
```

`use_double_nonneg.lean` (the file emitted for verifying `use_double_nonneg`) gets it right — `double_nonneg` is emitted first because the dep walker correctly identifies it as a dependency, and `use_double_nonneg` is emitted last because it's the target.

So the pattern: **target's file = dependencies first, target last**. That's the correct shape *for `use_double_nonneg.lean`*. But `double_nonneg.lean` shouldn't include `use_double_nonneg` at all — `double_nonneg` doesn't depend on it.

## Diagnosis

Two coupled issues in `dep_order` / `generate.rs`'s proof-fn emission:

1. **Over-inclusion.** When emitting `double_nonneg.lean`, the dep walker is including *every* proof fn in the krate, not just `double_nonneg`'s transitive dependencies. Since `double_nonneg`'s dependencies are just `{double}` (a spec fn), `use_double_nonneg` shouldn't appear.

2. **Wrong topological order in the included set.** Even when the over-included set is what gets emitted, the order in `double_nonneg.lean` is `use_double_nonneg` then `double_nonneg`. The target should be last (good — that contract is correct), and the included references should be sorted topologically so dependencies precede dependents. Here `use_double_nonneg` depends on `double_nonneg`, so the latter should be first.

Both manifest together: the over-inclusion drags `use_double_nonneg` into the file at all; the order issue places it before its dependency.

## Suggested fix

The clean fix addresses (1) — the over-inclusion. If `double_nonneg.lean` only includes `double_nonneg`'s actual transitive dependencies (the spec fns it uses), `use_double_nonneg` simply isn't there to cause the order problem. The dep walker probably already has the right `collect_references` infrastructure (it's used for spec fns); applying the same filter to proof fns would fix it.

A defensive backup: even with (1) addressed, run a topological sort on whatever set ends up in the file, with the target placed last. That makes the emission contract robust against future changes to the walker's "what to include" logic.

## Severity

Medium. Real users hit this any time a proof fn library has one helper used by another helper. The chapter-3 (Fibonacci addition formula) attempt was the first place I hit it — `fib_step_mono` couldn't be a separate helper, had to inline into `fib_monotone`. Chapter 4 had the same — `fact_recurrence` had to be inlined into `fact_pos` and `fact_monotone` rather than shared.

Workaround: inline every helper. Each lemma is then self-contained but uses ~5–10 extra lines of duplication. Manageable for a tutorial; less ideal for a real proof library.

## Discovered while

Tutorial UX retest after the suite of fixes that landed during chapter writing. Specifically the proof-fn → proof-fn call test:

```rust
proof fn helper(n: nat) ...
proof fn caller(n: nat) ... by { have h := helper n; ... }
```

`caller.lean` verifies (correct order — dep walker places `helper` first). `helper.lean` doesn't (over-includes `caller`, places it first). Same shape in real tutorial code where one helper builds on another.
