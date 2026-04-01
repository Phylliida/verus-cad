# Summary of .md Files

`spec_fn` applications in `forall`/`exists` quantifiers cause "Could not automatically infer triggers" — Z3 can't match opaque function applications.
**Solution:** Use recursive spec fns (e.g., `no_pred_below`) to replace quantifiers entirely. For well-ordering proofs, use a scan pattern that recurses through the domain.

Quantified postconditions about fields of returned enum variants fail even when loop invariants establish the IDENTICAL quantifier on the local variable.
**Solution:** Wrap quantifiers in a named `open spec fn` — Z3 can match `f(x)` regardless of which variable name it uses.

compose_single case 2 (straddle) silently truncated output when `b_shape % (m/b_stride) != 0`.
**Fix:** Added divisibility check `&& b_shape % (m / b_stride) == 0`. Non-divisible inputs now fall to case 4 (rank-1 fallback). After fix, `lemma_crs_size` and `lemma_compose_size` no longer need admissibility.

Three patterns for proving `choose` results:
1. **Two-step choose** (avoids rlimit from nested forall): first choose the nat length, then choose the word at that length
2. **Proving choose == 0 for nat:** `lemma_no_pred_below_forces_zero` — if pred(0) and no_pred_below(pred, l), then l must be 0
3. **Proving choose returns ε:** show it picks a word of length 0, then any word of length 0 is ε

Comprehensive list of techniques that work in Verus/Z3:
- **Split match arms** into separate proof fns to reduce Z3 complexity
- **`return` per branch** isolates postcondition checking — prevents cross-branch context pollution
- **Recursive spec fn predicates** need explicit branch assertions to guide Z3 (can't auto-unfold reliably)
- **`by (compute_only)`** for concrete values (e.g., `pow2(63)`) — 98% rlimit reduction
- **Opaque large spec fns** — mark with `#[verifier::opaque]` to prevent Z3 from diving into tree structure
- **Eval rewriting lemmas** — one-step unfolding lemmas instead of relying on Z3 to auto-unfold 14-arm match
- **Module isolation** — put eval-chain proof fns in separate module to reduce trigger pollution
- **Struct literals in `requires`/`assert`** can hit parsing errors — use tiny spec constructors instead
- **delinearize_concat** is the go-to for offset proofs across concatenated shapes
- **flatten is NOT idempotent** — use `full_flatten = coalesce(flatten(L))` for canonical form
- **logical_divide with rank-1 B** only correct for rank-1 or column-major A — use `logical_divide_mode` for general multi-rank

Strict rule: never use `assume(...)` or `admit()` in proofs. Always prove fully or restructure.

Preference: direct edits (Read/Edit/Write) for code changes. Agents (delegate_task) are for research/exploration only. User rejected agent-based rewriting of widgets_deep_equal_exec.

Verification is fully deterministic. When a function hits rlimit after code changes, it's because adding new call sites increases Z3 work for existing lemmas. Fix: always split the affected function into smaller helpers, never just bump rlimit.

Never use `raw=true` on verus check — raw compiler output is enormous and wastes context. "0 verified, 0 errors" is normal for modules with only spec functions (specs don't appear in the verification count).

Z3 response time is superlinear in proof size. Functions with >50 assertions consistently fail even with high rlimit.
- Split into focused helpers of ≤30 lines each
- Use `assert(F) by { lemma_X(); }` scoping to prevent fact pollution
- Put preconditions (e.g., `axiom_eqv_reflexive`) BEFORE the call that needs them
- For proof-by-contradiction: use `if P { ... }` in main context, NOT inside `assert by`

act_word must process RIGHT-TO-LEFT for textbook LEFT action (φ(g₁·g₂) = φ(g₁) ∘ φ(g₂)). LEFT-to-RIGHT + LEFT multiplication gives the reversed group element — which breaks relator triviality since the reverse of a relator word is NOT always ε.
- Use `w.last()/w.drop_last()` (not `w.first()/w.drop_first()`)
- `inverse_pair_word` is `[inv(s), s]` (not `[s, inv(s)]`)
- lemma_insert_trivial_at_state uses SUFFIX state (not prefix)
