# Britton's Lemma via Tower Construction — Session Summary

## Overview

This document summarizes the formalization of Britton's lemma via the tower construction, following Lyndon-Schupp Chapter IV. Starting from 195 verified functions with 3 errors, we reached **302 verified, 0 errors, 0 assumes** across 3 files (224 + 15 + 63).

**All gaps closed.** Britton's lemma is fully unconditional — no extra preconditions beyond the mathematical ones.

**Theorem (Britton's Lemma):** If `w` is a base word (no stable letters) and `w = 1` in the HNN extension `G*`, then `w = 1` in the base group `G`.

**Proof approach:** Unfold the HNN extension into a tower of iterated amalgamated free products. AFP injectivity at each level gives the base group embedding. HNN relators translate to AFP identification relators at tower junctions.

## Files

| File | Verified | Role |
|------|----------|------|
| `normal_form_afp_textbook.rs` | 224 | AFP injectivity via textbook one-shot action |
| `tower.rs` | 15 | Tower construction + textbook embedding |
| `britton_via_tower.rs` | 63 | Derivation translation + unconditional Britton's lemma |

## Architecture

```
AFP injectivity (one-shot action, Lyndon-Schupp Ch. IV)
    |
    |--- action_preserves_canonical (from identifications_isomorphic)
    |--- action_well_defined (G1 + G2 + identification relator triviality)
    |--- act_word_deriv (derivation-level well-definedness)
    |
Tower embedding (inductive AFP injectivity at each level)
    |
    |--- lemma_g0_embeds_in_tower_textbook
    |--- lemma_afp_injectivity_right (right factor embedding)
    |
Derivation translation (HNN steps -> tower steps)
    |
    |--- translate_word_at (level-aware word translation)
    |--- lemma_translate_hnn_relator (HNN relator = identification relator)
    |--- lemma_hnn_step_tower_equiv (per-step translation)
    |--- lemma_hnn_derivation_to_tower_equiv (full induction)
    |
Britton's lemma
    |--- britton_lemma (conditional on tower prerequisites)
```

## Key Theorems (all 0 assumes)

### AFP Injectivity
- `lemma_afp_injectivity`: If w is a G1-word and w = 1 in AFP, then w = 1 in G1.
- `lemma_afp_injectivity_right`: If shift(w, n1) = 1 in AFP, then w = 1 in G2.

### Action Preserves Canonical
- `lemma_action_preserves_canonical_spec`: `identifications_isomorphic(data)` implies `action_preserves_canonical(data)`.
- Proof chain: A-side canonical (left_h_part fixed point) + B-side canonical (b_rcoset_h fixed point via A<->B witness transfer) + syllable case analysis.
- The A<->B transfer is the mathematical heart: `identifications_isomorphic` makes A and B equivalence classes on K-words coincide, so the three-step choose (min-len, min-lex, unique word) gives the same result for both decompositions.

### Tower Embedding
- `lemma_g0_embeds_in_tower_textbook`: w = 1 in tower(n) implies w = 1 in base.
- `lemma_base_at_copy_k_embeds`: equiv(base, w1, w2) implies equiv(tower(m), shift(w1, k*ng), shift(w2, k*ng)) via shift homomorphism.

### Derivation Translation
- `lemma_translate_hnn_relator`: HNN relator t^-1 * a_i * t * inv(b_i) at level k translates to AFP identification relator at tower junction (k-1)<->k.
- `lemma_hnn_derivation_to_tower_equiv`: Full HNN derivation translates to tower equivalence.

### Britton's Lemma
- `britton_lemma`: If w is a base word, w = 1 in G*, tower prerequisites hold, and derivation levels are OK, then w = 1 in G.

## Lessons Learned

### 1. Seq::new Closure Mismatch is the #1 Z3 Engineering Issue

Z3 treats each `Seq::new(n, |i| f(i))` at a different call site as a distinct opaque sequence, even if the closures compute identical values. This manifests as:

- `inverse_word(Seq::new(1, |_| s)).len() == 1` — Z3 can't unfold `inverse_word` when its argument is from a different Seq::new
- `apply_embedding(shifted_images, w) =~= shift_word(apply_embedding(images, w), offset)` — Z3 can't see the distributivity through Seq::new
- `a_words_tower =~= b_words_hnn` — element-wise equal but Z3 doesn't see Seq =~=

**Fixes that work:**
- Pass constructed Seqs as PARAMETERS instead of building them in `ensures` clauses
- Use `reveal_with_fuel(fn, depth)` for recursive functions on Seq::new arguments
- Assert element-wise facts to trigger Seq axioms: `seq[i] == expected_value`
- Put helper lemmas in the SAME MODULE as the spec function (e.g., `lemma_inverse_word_len` in `word.rs`)
- Use `lemma_shift_embedding_distributes` with shifted images as parameter to avoid Seq::new in ensures

### 2. The Three-Step Choose Pattern Requires Careful Uniqueness Arguments

The canonical K-word choose (min-length -> min-lex -> unique word) is deterministic but Z3 can't derive `choose_result == specific_value` without:

1. Showing specific_value satisfies the predicate (from satisfiability)
2. Showing specific_value is the ONLY satisfier (from min-len/min-lex uniqueness)
3. Using `lemma_word_lex_rank_base_injective` for the final word equality

**Pattern for proving choose equals a specific value:**
```
//  Step 1: Establish min-len equality (h.len() == choose_min_len)
//  Step 2: Transfer no_pred_below between A and B sides
//  Step 3: Establish min-lex equality (h.lex == choose_min_lex)
//  Step 4: Apply lex rank injectivity (same length + same lex -> same word)
```

### 3. identifications_isomorphic is the Key to Everything

The `identifications_isomorphic` condition (embed_a(w) = 1 iff embed_b(w) = 1) is far more powerful than it appears:

- **A<->B witness transfer**: `has_left_h_witness_of_len(embed_a(h), l) <-> has_right_h_witness_of_len(embed_b(h), l)`
- **Canonical preservation**: A-canonical implies B-canonical (and vice versa)
- **action_preserves_canonical**: Follows from the above
- **Tower isomorphism**: `hnn_associations_isomorphic` lifts to `identifications_isomorphic` at each tower level

### 4. assert-by Scoping is Essential for Large Proofs

The rlimit guide's #1 recommendation: use `assert(F) by { lemma(); }` to scope fact pollution. In a module with 220+ functions, every lemma call adds facts to the context. Without scoping:
- Functions that verified at rlimit 30 need 300+
- Z3 spends time on irrelevant quantifier instantiations

**What works:**
- Extract sub-proofs into helper lemmas (reduces per-function context)
- Use `assert-by` for lemma calls only needed for one assertion
- Use `reveal(presentation_valid)` explicitly rather than leaving it auto-unfolded

### 5. The Homomorphism Infrastructure is Powerful

The `HomomorphismData` + `lemma_hom_preserves_equiv` pattern cleanly proves embeddings:
- Shift homomorphism: base -> tower(m) mapping Gen(i) -> Gen(i + k*ng)
- Only need: generator images are word_valid + relator images = 1 in target
- `lemma_hom_preserves_equiv` handles the derivation lifting automatically

### 6. RIGHT-TO-LEFT Processing is Non-Negotiable

The textbook LEFT action requires RIGHT-TO-LEFT processing (`w.last()/w.drop_last()`). LEFT-TO-RIGHT gives the REVERSED group element. Counterexample: `abc = 1` does NOT imply `cba = 1`.

### 7. Never Use assume()

The user blocks ALL tool calls containing `assume()` or `admit()`. When stuck:
- Split into smaller helpers
- Add intermediate assertions
- Use `reveal_with_fuel` for recursive unfolding
- Move helper lemmas to the defining module
- Document the gap and return later — never write assume as a placeholder

## ALL GAPS CLOSED — COMPLETE

**Grand total: 302 verified (224 + 15 + 63), 0 errors, 0 assumes.**

### Gap 3: Level Normalization — CLOSED (Session 3)

HNN derivations can have negative levels, but the one-sided tower requires levels in [0, m]. Solution: generalize the translation lemmas with a `base_level: int` parameter instead of hard-coding 0.

Key insight: instead of constructing shifted derivations explicitly (conjugating with t^s), simply shift all level computations by `base_level`. The existing `translate_word_at(data, w, base_level)` already supports arbitrary base levels.

New infrastructure:
- `derivation_min_adj_level(data, steps, start)` — minimum "adjusted" level (accounting for HNN steps needing level >= 1)
- `derivation_max_step_level(data, steps, start)` — maximum level across all steps
- `lemma_derivation_levels_ok_from_bounds` — if shift >= -min_adj and m >= max + shift, levels are OK
- Generalized `step_level_ok`, `derivation_levels_ok`, `lemma_hnn_step_tower_equiv`, `lemma_hnn_derivation_to_tower_equiv` with `base_level: int` parameter
- `lemma_translate_delete_middle` / `lemma_translate_insert_middle` generalized with `base_level`

### Gap 4: Tower Isomorphism — CLOSED (Session 2)

Weakened prerequisites from `tower_textbook_chain(data, k+1)` to `tower_textbook_chain(data, k)`.

### Gaps 1+2: CLOSED (Session 2)

### Final Assembly (Session 3)

- `lemma_iso_implies_apc`: universal `action_preserves_canonical(data)` from `identifications_isomorphic(data)`
- `lemma_tower_textbook_chain_from_hnn_iso`: inductive tower prerequisites from `hnn_associations_isomorphic`
- `lemma_copy_s_embeds`: generalized tower embedding for copy s (not just copy 0)
- `britton_lemma_unconditional`: the final theorem

```
britton_lemma_unconditional(data, w):
    requires: hnn_data_valid(data), hnn_associations_isomorphic(data),
              word_valid(w, base.num_generators), equiv(hnn, w, empty)
    ensures: equiv(base, w, empty)
```

With 0 assumes, 0 axioms — a complete formalization of Britton's lemma.
