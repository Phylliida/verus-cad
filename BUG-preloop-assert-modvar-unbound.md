# BUG: pre-loop assert mentioning a loop-modified var → unbound `i` in loop obligations (debug/release divergence)

**Severity:** correctness + soundness-adjacent. The generated Lean for the
loop maintain/use obligations references an **unbound** variable; the
debug-only sanity check rejects it, while **release** (= production
cargo-verus) silently accepts it via Lean's autoImplicit. This is the root of
the tutorial's "green in release, broken in debug" fragility — ch2 `fib_iter`,
ch4 `factorial`, ch7 `fast_fib`.

**Status:** ✅ RESOLVED 2026-06-08 (tactus `9439365`, approach 1). Found while
adding the tutorial-pin tests (TACTUS-TESTS-TO-PIN-TUTORIAL.md): T1/T2 passed
standalone (release) but failed in the test harness (debug).

## Symptom

A pre-loop `assert(P)` whose `P` mentions a loop-**modified** variable:

```rust
let mut result: u64 = 1;
let mut i: u64 = 0;
assert(result as nat == fact(i as nat)) by { ... };   // mentions i (modified by the loop)
while i < n invariant result >= 1, i <= n, decreases n - i { i = i + 1; }
```

- **Debug:** `Tactus codegen produced unresolved references: unresolved i`
  (in the loop-invariant *maintain* theorems and the postcondition).
- **Release:** `3 verified, 0 errors`. Same deterministic codegen — but
  release skips the sanity check, and Lean's autoImplicit silently rebinds the
  free `i`.

## Root cause

`walk_loop` builds the maintain context as `obl.clone()` (the **outer**
OblCtx, which contains the pre-loop assert's result as a `Hyp` mentioning `i`)
and then `push_mod_var_frames` appends the `∀ i` binder *after* it. Wrapped
outermost-first, the emitted theorem is:

```lean
let result := 1;
Int.toNat result = fact (Int.toNat i) →     -- ← i UNBOUND: the ∀ i is below
Int.toNat result = fact (Int.toNat i) →
(∀ (i : Int), 0 ≤ i ∧ … → result ≥ 1 → i ≤ n → i < n → … )   -- the real i, bound here
```

`push_mod_var_frames` already dropped prior `Let` frames *binding* a modified
var (so `let i := 0` is absent — BUG-loop-local-names-alpha-renamed.md), but it
did **not** drop `Hyp` frames that *mention* one. So the pre-loop assert hyp
dangled.

**Why the masking is soundness-adjacent.** Release verifies a maintain
obligation carrying an *extra, spurious* hypothesis (`result = fact(autobound_i)`).
Harmless in this shape (the goal doesn't use it), but an extra hypothesis on a
maintain obligation is exactly what can let a *non-preserved* invariant
"verify". The pre-loop fact is also semantically wrong for the loop (it's about
the entry state of a variable the loop mutates).

## Fix (approach 1)

`push_mod_var_frames` now also drops prior `Hyp` frames that mention any
modified-var name (via `lean_ast::mentions_free_var`), at the maintain / use /
closure-body sites uniformly. Sound by Hoare logic: the loop maintain assumes
only the invariant + cond; a pre-loop fact about a variable the loop mutates is
not preserved and must not flow in. The **init** obligation is unaffected — it
uses the outer ctx where `let i := 0` is still in scope, so its `i` resolves.

Rejected alternative (approach 2 — substitute the pre-loop value `i → 0`): it's
**unsound** when the hyp also mentions a modified var that gets ∀-quantified
(e.g. `result` in `fib_iter`), pinning that ∀-var to its entry value → a
contradictory hypothesis.

## Pinned by

`test_preloop_assert_names_init_lets` (T1, explicit `intro result i`),
`test_preloop_assert_via_show` (T2, `show` defeq), and
`test_preloop_assert_plain_intros_inaccessible` (T1-neg, `intros` → inaccessible
names → `Unknown identifier`). All three now pass identically in **debug and
release**. Full suite **501/0**, lean_verify **269/0**, vstd **1530/0**.

## Follow-up: close the masking generally (approach 4 — ✅ LANDED 81f9fe3)

The deeper sharp edge was that the sanity check is **debug-only**, so release
could ship broken Lean that autoImplicit masks. `generate.rs` now emits
`set_option autoImplicit false` after the namespace open in every generated
file, so **Lean itself** rejects any unbound reference in every build profile,
independent of the debug checker. Scoped after the namespace so the hand-written
prelude/addendums are unaffected.

**Probe result: zero false positives.** Validated across the full e2e suite
(501/0) and every tutorial chapter (0 errors) — and it surfaced **no other**
latent unbound-ref bugs, confirming this fix was complete for the tested surface
(as expected: well-formed generated code never relies on autobound). The
debug-only sanity check stays as a faster, more specific first line; autoImplicit
false is the profile-independent backstop. See DESIGN § "autoImplicit guardrail".
