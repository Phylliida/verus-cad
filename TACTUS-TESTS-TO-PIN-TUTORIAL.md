# Tactus regression tests to keep the tutorial from breaking under-foot

During the ch6/ch7 work, several Tactus lowering/closer behaviors that the
tutorial chapters depend on shifted between builds and silently broke chapters
that had been green. This doc lists those load-bearing behaviors, notes which
already have regression tests, and proposes tests (in
`source/rust_verify_test/tests/tactus.rs` style) for the gaps.

All tests target the Lean backend, so they go in `tactus.rs` (which shadows
`verify_one_file` to add `--lean-backend`).

## TL;DR — strongest single safeguard

Add the **eight tutorial chapter `.rs` files** (`tactus-tutorial/chapters/*/*.rs`,
chapters 0–7) to CI as an integration smoke test, run with `--lean-backend`, and
assert each ends in `0 errors`. The unit tests below are more diagnostic, but the
chapters are the real contract — they exercise combinations the units don't, and
they're what actually regressed. (They need Mathlib + the `TactusTutorialHelpers`
lib on the lean path; see `tactus-tutorial/HANDOFF.md`.)

## Already pinned (good — keep these)

These behaviors broke at some point this arc but now have tests:

- `test_spec_fn_mod_decreases`, `test_spec_fn_sub_decreases` — spec-fn
  `decreases` with a `%`/`-` measure (gcd). ✅
- `test_proof_fn_recursive_mod_decreases` — proof-fn version. ✅
- `test_plain_exec_fn_file_gets_file_level_import` — the aggregate file carries
  the source `import Mathlib.*` (the `nlinarith` "unknown tactic" bug). ✅
- `test_exec_tuple_destructure_assert_omega` (+ `_both_elements`,
  `_default_closer`, `_simp_all`, `_wrong_bound`, `_user_intros_fails`,
  `test_exec_tuple_construction_postcondition`, `test_exec_triple_destructure_assert`,
  `test_exec_tuple_destructure_and_loop`) — `let (a,b) = call()` then
  `assert(...) by { omega }`; notably `_user_intros_fails` pins that a user
  `intros` does *not* work there. ✅
- `test_exec_loop_invariant_u64_as_nat` — a `u64` loop var cast `as nat` in an
  invariant. ✅
- `test_exec_call_recursive_*` (many) — recursive exec fns with `decreases`
  (covers fast_fib's recursion shape). ✅
- `test_proof_heartbeats_attribute`, `test_exec_heartbeats_attribute`,
  `test_exec_heartbeats_multi_theorem` — `#[verifier::heartbeats(N)]` (ch7 needs
  a raised budget). ✅

## Gap: pre-loop / before-call asserts over synthetic goal-position lets

`test_loop_local_name_in_assert_by_probe` / `test_multi_var_loop_assert_by_probe`
cover asserts **inside the loop body**. They do **not** cover an assert placed
**before the `while`** (or **before a recursive call**) that references a fn's
init/temp values — and that is exactly the shape that broke ch2 `fib_iter`, ch4
`factorial`, and ch7 `fast_fib` when the loop-local-names lowering landed.

The init/temp values lower into **goal position** as `let result := 0; let i := 0;
…` / `let k := n/2;`, which are **not** auto-intro'd. A plain `intros` then
introduces them with **inaccessible** names, so referencing `i` / `k` by name in
the proof fails with "Unknown identifier". The tutorial works around this two
ways, both of which should be pinned.

### T1 — pre-loop assert names init lets via explicit `intro` (Ok) — VALIDATED

This compiles to `4 verified, 0 errors` today (validated standalone). It pins the
fib_iter idiom.

```rust
test_verify_one_file! {
    #[test] test_preloop_assert_names_init_lets verus_code! {
        import Mathlib.Tactic.Linarith

        spec fn cnt(n: nat) -> nat
            decreases n
        { if n == 0 { 0 } else { cnt((n - 1) as nat) + 1 } }

        #[verifier::tactus_auto]
        #[verifier::tactus_tactic("first | tactus_auto | (intros; omega)")]
        fn g(n: u64) -> (r: u64)
            requires n <= 100
            ensures r <= 100
        {
            let mut result: u64 = 0;
            let mut i: u64 = 0;
            // result, i are goal-position init lets; name them with explicit
            // `intro` (plain `intros` leaves them inaccessible — see T1-neg).
            assert(result as nat == cnt(i as nat)) by {
                intro result i
                have h : i.toNat = 0 := by omega
                rw [h]; unfold cnt; simp
            };
            while i < n
                invariant result == i, i <= n,
                decreases n - i
            {
                i = i + 1;
                result = result + 1;
            }
            result
        }
    } => Ok(())
}
```

### T1-neg — plain `intros` fails (Err) — VALIDATED

Same body but `intros` instead of `intro result i` → `Unknown identifier
i.toNat` (validated: `2 verified, 1 errors`). Pins the convention so a future
change that *re-enables* plain `intros` is noticed (and the tutorial / T1 can be
simplified) rather than silently diverging.

```rust
test_verify_one_file! {
    #[test] test_preloop_assert_plain_intros_inaccessible verus_code! {
        import Mathlib.Tactic.Linarith
        spec fn cnt(n: nat) -> nat decreases n { if n == 0 { 0 } else { cnt((n - 1) as nat) + 1 } }
        #[verifier::tactus_auto]
        #[verifier::tactus_tactic("first | tactus_auto | (intros; omega)")]
        fn g(n: u64) -> (r: u64) requires n <= 100 ensures r <= 100 {
            let mut result: u64 = 0;
            let mut i: u64 = 0;
            assert(result as nat == cnt(i as nat)) by {
                intros                       // ← inaccessible lets
                have h : i.toNat = 0 := by omega
                rw [h]; unfold cnt; simp
            };
            while i < n invariant result == i, i <= n, decreases n - i { i = i + 1; result = result + 1; }
            result
        }
    } => Err(err) => {
        let msg = format!("{:?}", err);
        assert!(msg.contains("Unknown identifier"), "expected inaccessible-let error, got: {}", msg);
    }
}
```

### T2 — pre-loop assert via `show` (Ok)

The factorial idiom: when the assert goal is a concrete equality, `show` strips
the lets by defeq (no naming needed). Derived from the verifying ch4
`factorial.rs` entry assert:

```rust
test_verify_one_file! {
    #[test] test_preloop_assert_via_show verus_code! {
        import Mathlib.Tactic.Linarith
        spec fn fact(n: nat) -> nat decreases n { if n == 0 { 1 } else { n * fact((n - 1) as nat) } }
        #[verifier::tactus_auto]
        fn g(n: u64) -> (r: u64) requires n <= 1 ensures r >= 1 {
            let mut result: u64 = 1;
            let mut i: u64 = 0;
            assert(result as nat == fact(i as nat)) by {
                show Int.toNat 1 = fact (Int.toNat 0)
                unfold fact
                simp
            };
            while i < n invariant result >= 1, i <= n, decreases n - i { i = i + 1; }
            result
        }
    } => Ok(())
}
```

### T3 — before-recursive-call assert names a `let k := n/2`

ch7 `fast_fib`'s recursive-call bound assert references `let k := n/2` (a trailing
goal-position let) and needs `intro _ _ _ _ k`. A *minimal* standalone is awkward
to pin — the `n/2` emits its own `2 ≠ 0` obligation and the exact `intro` arity
depends on how many guards precede `k`, which is **itself a fragility worth
removing** (see "Suggested ergonomic follow-up"). The faithful pin is the chapter:
`tactus-tutorial/chapters/07-fast-doubling/fib_fast.rs` (the
`assert(fib((k + 1) as nat) <= 0x8000_0000)` block). Recommend pinning it via the
integration smoke test (TL;DR) rather than a brittle minimized unit.

## Suggested ergonomic follow-up (would shrink these tests)

The root friction is that synthetic goal-position lets aren't auto-intro'd with
**accessible** names, forcing either `intro <exact-names-and-arity>` (fragile —
breaks when the guard set changes) or `show <concrete>` (verbose). If Tactus
auto-intro'd them with their **source names accessible** (the way loop-*body*
locals now are, per `test_loop_local_name_in_assert_by_probe`), the tutorial's
pre-loop / before-call asserts could use plain `intros` like everything else, and
T1/T2/T3 would collapse to one positive test. If that lands, update T1-neg
(it currently pins the *opposite*).

## Note for whoever adds these

Inside `by { … }` blocks the text is raw Lean: comments are `--` (not `//`), and
`rec`/`show`/etc. are keywords (don't name a hypothesis `rec`). These bit me
repeatedly; a quick lint in the test harness ("`//` inside a tactic block")
would have saved real time.
