# AFP Injectivity Proof: Lessons in Verus Proof Engineering

Lessons learned from formalizing the normal form theorem for amalgamated free products
(van der Waerden action approach) in Verus. These apply broadly to large algebraic
proofs involving Cayley tables, group actions, and compositional reasoning.

## 1. Textbook Approach vs Derivation Analysis

**Lesson**: Follow the textbook proof structure, not derivation-step analysis.

The standard proof of AFP injectivity (Lyndon-Schupp Ch. IV) works at the GROUP level:
define an action on generators, check it respects relators, conclude. It NEVER looks at
derivation steps.

We initially tried a derivation-analysis approach (tracking G2-symbol count, excursion
lemmas, peak elimination). This led to:
- Circular dependencies (excursion lemma needs injectivity, injectivity needs excursion)
- Exponential case analysis (overlapping relators, factor boundary interactions)
- 1000+ lines of dead-end code

The textbook approach (define action, check relators, conclude) is:
- Non-circular (action is defined independently, well-definedness is a property)
- Compositional (each relator type checked independently)
- Much shorter (~300 lines for the action + well-definedness)

**Rule**: When the textbook proof avoids derivation steps, your formalization should too.

## 2. H-Only Action: Simplifying the VDW State

**Lesson**: For injectivity, you don't need the full syllable action.

The full van der Waerden action tracks `(h, syllables)` — an H-element plus alternating
coset representatives. This is complex for Z3: the syllable merging logic involves nested
match/if with coset decomposition, and Z3 hits rlimit trying to unfold it.

For AFP INJECTIVITY specifically, you only need the h-component (a single `nat`
tracking the Cayley table element). The syllable structure is needed for the full
normal form theorem (uniqueness) but not for injectivity (faithfulness on the identity
state).

The h-only action:
```
h_act_sym(s, h) =
  if G1_symbol: ct_lookup(ct1, h, sym_col(s))
  if G2_symbol: phi(ct_lookup(ct2, phi_inv(h), sym_col(unshift(s))))
```

This is simple enough for Z3 to unfold and reason about.

**Rule**: Strip the state to the minimum needed for your specific theorem.

## 3. Opaque Definitions and `reveal`

**Lesson**: Verus's `#[verifier::opaque]` on `coset_table_wf`, `coset_table_consistent`,
`coset_table_complete`, and `relator_closed` means Z3 can't see their contents by default.

You MUST call `reveal(...)` in any proof that needs to reason about table properties.
Common pattern:
```rust
reveal(crate::todd_coxeter::coset_table_wf);
reveal(crate::todd_coxeter::coset_table_consistent);
reveal(crate::finite::coset_table_complete);
```

Also: `relator_closed` uses triggers `#![trigger t.table[c as int], p.relators[r]]`.
To fire these, you must mention both `ct.table[h as int]` AND `p.relators[idx as int]`
in your proof.

**Rule**: When a proof involving CosetTable fails mysteriously, check if you need `reveal`.

## 4. Trigger Hints for Quantifiers

**Lesson**: Z3 quantifier instantiation is trigger-driven. If a quantified fact isn't
being used, check that the trigger terms appear in your proof context.

Examples from this proof:
- `relator_closed` triggers on `t.table[c]` and `p.relators[r]` — need both
- `valid_phi`'s generator compatibility triggers on `data.identifications[i]` and `ct1.table[h]`
- `phi_inv(phi(b))` triggers on `phi_inv(phi(b))` — mention `phi_inv(phi(x))` explicitly

Pattern to fire triggers:
```rust
let _ = ct1.table[h as int];           //  fire table trigger
let _ = data.identifications[idx as int]; //  fire identification trigger
```

**Rule**: When a quantified fact should apply but doesn't, add explicit `let _` bindings
to fire the trigger.

## 5. `Seq::new` and First/Drop Patterns

**Lesson**: Z3 struggles to connect `Seq::new(n, |i| f(i))` with `.first()` and
`.drop_first()`. For recursive functions that pattern-match on sequences (like
`trace_word`, `h_act_word`), Z3 needs to see the connection explicitly.

For `trace_word(ct, h, w)` where `w = Seq::new(...)`:
- Assert `w.first() == expected_first_symbol`
- Assert `w.drop_first() =~= expected_rest`
- Assert `symbol_to_column(w.first()) == expected_column`
- Assert the table entry: `ct.table[h][col] is Some` and `ct.table[h][col] == Some(next)`

**Rule**: When recursive spec functions don't unfold on `Seq::new` inputs, add explicit
assertions for `.first()`, `.drop_first()`, and any intermediate lookups.

## 6. Composition Lemma as the Key Tool

**Lesson**: The single most important proof tool is the composition lemma:
```
h_act_word(concat(w1, w2), h) == h_act_word(w2, h_act_word(w1, h))
```

This lets you split ANY word at any position and reason about the pieces independently.
The well-definedness proof uses it for every derivation step type:
- FreeReduce: split at position, show the inverse pair acts trivially
- FreeExpand: split at position, show the inserted pair acts trivially
- RelatorInsert/Delete: split at position, show the relator acts trivially

The composition lemma itself is trivial to prove (induction on w1.len()).

**Rule**: Prove the composition lemma first. It's the foundation for everything else.

## 7. Bound Preservation

**Lesson**: When your state is a `nat` index into a finite table, you need to prove
the bound `h < ct.num_cosets` is preserved by every operation. This requires:

1. `reveal(coset_table_wf)` and `reveal(coset_table_complete)` to see table entry bounds
2. Column bounds: `sym_col(s) < 2 * ct.num_gens` requires `generator_index(s) < ct.num_gens`
3. phi bounds: `phi(b) < ct1.num_cosets` for `b < ct2.num_cosets`

The bound lemma needs `word_valid(w, n1 + n2)` to ensure all symbols produce valid
column indices.

**Rule**: Add the bound preservation lemma early and propagate it to all callers.

## 8. Phi Compatibility: Per-Column vs Word-Level

**Lesson**: The isomorphism `phi: B -> A` needs TWO kinds of compatibility:

1. **Per-column**: `phi(ct_lookup(ct2, h2, col)) == ct_lookup(ct1, phi(h2), col)`.
   This connects single-symbol actions across the two Cayley tables.

2. **Word-level identification**: For each identification pair (u_i, v_i) and all h:
   `trace(ct2, phi_inv(h), v_i) == Some(phi_inv(trace(ct1, h, u_i).unwrap()))`.
   This connects how the IDENTIFICATION WORDS act across the tables.

The per-column compatibility alone is INSUFFICIENT for the identification relator case.
The issue: per-column compatibility makes G2 symbols act the SAME as G1 symbols on h.
This means `h_act_word(shift(v_i), h)` gives the same result as `h_act_word(u_i, h)`
through ct1. But the identification relator needs u_i and v_i to CANCEL, not to act
identically.

The word-level compatibility provides the DIFFERENT property: tracing v_i through ct2
from phi_inv(h) gives phi_inv of tracing u_i through ct1 from h. This allows the
inverse-of-v_i to undo the effect of u_i.

**Rule**: For amalgamated free products, the phi specification must include word-level
compatibility for the identification generators, not just per-column compatibility.

## 9. Inverse Word Handling

**Lesson**: Proving things about `inverse_word(w)` requires specific lemmas:

- `lemma_inverse_concat(a, b)`: `inverse_word(concat(a, b)) =~= concat(inverse_word(b), inverse_word(a))`
- `lemma_inverse_involution(w)`: `inverse_word(inverse_word(w)) =~= w`
- `lemma_inverse_word_valid(w, n)`: `word_valid(w, n) ==> word_valid(inverse_word(w), n)`
- `lemma_trace_inverse_word(ct, h, w)`: if `trace(h, w) == Some(end)`, then `trace(end, inv(w)) == Some(h)`
- `lemma_shift_inverse_word(w, n)`: `shift_word(inv(w), n) =~= inv(shift_word(w, n))`

For the inverted relator case: decompose `inverse_word(concat(u_i, inv(shift(v_i))))`
into `concat(shift(v_i), inverse_word(u_i))` using `lemma_inverse_concat` +
`lemma_inverse_involution`.

**Rule**: Build a toolkit of inverse_word lemmas. You'll need all of them.

## 10. Function Size and Z3

**Lesson**: Large proof functions (>100 lines) with many branches cause Z3 to slow down
or fail, even when individual branches are provable. The issue is that Z3 tries to
verify all branches simultaneously, and the combined constraint size exceeds its capacity.

Fix: Split into per-branch helper functions. Each helper has a focused ensures clause
and a short proof body. The main function just dispatches to helpers.

Example: `lemma_h_act_step` dispatches to `lemma_h_inv_pair` (for FreeReduce/Expand)
and `lemma_h_relator` (for RelatorInsert/Delete). Each helper is independently verifiable.

Further splitting: `lemma_h_inv_pair` dispatches to `lemma_h_inv_pair_g1` and
`lemma_h_inv_pair_g2`. `lemma_h_relator` handles G1, G2, and identification cases.

**Rule**: If a proof function has >3 case branches, split each into a helper.

## 11. The `phi_inv` Commutation Pattern

**Lesson**: A key proof pattern for the identification relator:

To show `h_act_word(ident_relator, h) == h`:
1. Split into G1 part (u_i) and G2 part (inv(shift(v_i)))
2. After G1 part: `h_mid = trace(ct1, h, u_i)` [via h_act_is_trace]
3. `phi_inv(h_mid) = trace(ct2, phi_inv(h), u_i)` [via phi_inv_commutes_trace]
4. Word-level ident: `trace(ct2, phi_inv(h), v_i) == Some(phi_inv(h_mid))` [from valid_phi]
5. By trace_inverse_word: `trace(ct2, phi_inv(h_mid), inv(v_i)) == Some(phi_inv(h))`
6. Via h_act_g2_phi_inv_trace: this means the G2 part brings h_mid back to h

The phi_inv_commutes_trace lemma (proved by induction) is the bridge between the
two Cayley tables. It says: `phi_inv(trace(ct1, h, w)) == trace(ct2, phi_inv(h), w)`
for any word w valid for both tables.

**Rule**: The phi_inv commutation lemma is essential for connecting G1 and G2 actions.
Prove it by induction on word length, using the per-column phi compatibility at each step.

## 12. Architecture Summary

The final proof has this dependency chain:
```
lemma_afp_injectivity          -- main theorem
  -> lemma_h_act_deriv         -- derivation respects action (induction on steps)
    -> lemma_h_act_step        -- single step respects action (case split)
      -> lemma_h_inv_pair      -- inverse pair trivial (G1 + G2 sub-cases)
        -> lemma_ct_roundtrip  -- Cayley table consistency
        -> lemma_h_inv_pair_g1 -- G1 round-trip
        -> lemma_h_inv_pair_g2 -- G2 round-trip via phi
      -> lemma_h_relator       -- relator trivial (G1 + G2 + ident sub-cases)
        -> lemma_h_act_is_trace          -- G1 word = ct1 trace
        -> lemma_h_act_g2_phi_inv_trace  -- G2 word tracks ct2 trace via phi
        -> lemma_h_act_g2_relator        -- G2 relator trivial
        -> lemma_phi_inv_commutes_trace  -- phi_inv commutes with trace
        -> lemma_h_act_bound             -- h stays in bounds
      -> lemma_h_act_concat    -- composition of word action
  -> lemma_h_act_is_trace      -- faithfulness: result 0 means trace 0
  -> axiom_coset_table_sound   -- trace 0 means equiv to epsilon
```

Each leaf lemma is ~20-40 lines. The total is ~800 lines of action + well-definedness
code, plus ~700 lines of structural lemmas (from the earlier derivation-analysis phase,
still useful for the `lemma_left_step_valid_in_g1` foundation).
