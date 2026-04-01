//  ================================================================
//  FILE: lib.rs
//  ================================================================

//  Britton's Lemma — Fully verified formalization (0 errors, 0 assumes)
//  Following Lyndon-Schupp Chapter IV: tower construction + AFP injectivity

//  Foundation
#[cfg(verus_keep_ghost)]
pub mod symbol;
#[cfg(verus_keep_ghost)]
pub mod word;
#[cfg(verus_keep_ghost)]
pub mod reduction;

//  Group presentations and equivalence
#[cfg(verus_keep_ghost)]
pub mod presentation;
#[cfg(verus_keep_ghost)]
pub mod presentation_lemmas;

//  Algebraic structures
#[cfg(verus_keep_ghost)]
pub mod quotient;
#[cfg(verus_keep_ghost)]
pub mod free_product;
#[cfg(verus_keep_ghost)]
pub mod amalgamated_free_product;
#[cfg(verus_keep_ghost)]
pub mod hnn;
#[cfg(verus_keep_ghost)]
pub mod homomorphism;
#[cfg(verus_keep_ghost)]
pub mod benign;

//  Supporting infrastructure
#[cfg(verus_keep_ghost)]
pub mod shortlex;
#[cfg(verus_keep_ghost)]
pub mod todd_coxeter;

//  Normal form theorems
#[cfg(verus_keep_ghost)]
pub mod normal_form_free_product;
#[cfg(verus_keep_ghost)]
pub mod normal_form_amalgamated;
#[cfg(verus_keep_ghost)]
pub mod normal_form_afp_textbook;

//  Tower construction and Britton's lemma
#[cfg(verus_keep_ghost)]
pub mod tower;
#[cfg(verus_keep_ghost)]
pub mod britton_via_tower;


//  ================================================================
//  FILE: symbol.rs
//  ================================================================

use vstd::prelude::*;

verus! {

///  A symbol in a group word: either a generator or its formal inverse.
///
///  Generators are identified by natural numbers. A group with `n` generators
///  uses symbols `Gen(0)` through `Gen(n-1)` and their inverses.
#[derive(PartialEq, Eq)]
pub enum Symbol {
    Gen(nat),
    Inv(nat),
}

///  Returns the formal inverse of a symbol.
///  Gen(i) ↔ Inv(i).
pub open spec fn inverse_symbol(s: Symbol) -> Symbol {
    match s {
        Symbol::Gen(i) => Symbol::Inv(i),
        Symbol::Inv(i) => Symbol::Gen(i),
    }
}

///  Two symbols form an inverse pair (cancel each other).
pub open spec fn is_inverse_pair(s1: Symbol, s2: Symbol) -> bool {
    s2 == inverse_symbol(s1)
}

///  The generator index of a symbol.
pub open spec fn generator_index(s: Symbol) -> nat {
    match s {
        Symbol::Gen(i) => i,
        Symbol::Inv(i) => i,
    }
}

///  A symbol is valid for a group with `num_generators` generators.
pub open spec fn symbol_valid(s: Symbol, num_generators: nat) -> bool {
    generator_index(s) < num_generators
}

//  --- Lemmas ---

///  Inverse is an involution: inv(inv(s)) == s.
pub proof fn lemma_inverse_involution(s: Symbol)
    ensures
        inverse_symbol(inverse_symbol(s)) == s,
{
}

///  Inverse pair is symmetric.
pub proof fn lemma_inverse_pair_symmetric(s1: Symbol, s2: Symbol)
    ensures
        is_inverse_pair(s1, s2) == is_inverse_pair(s2, s1),
{
    lemma_inverse_involution(s1);
}

///  A symbol is never its own inverse (Gen(i) != Inv(i)).
pub proof fn lemma_not_self_inverse(s: Symbol)
    ensures
        !is_inverse_pair(s, s),
{
}

///  Inverse preserves the generator index.
pub proof fn lemma_inverse_preserves_index(s: Symbol)
    ensures
        generator_index(inverse_symbol(s)) == generator_index(s),
{
}

///  Inverse preserves validity.
pub proof fn lemma_inverse_preserves_valid(s: Symbol, n: nat)
    ensures
        symbol_valid(s, n) == symbol_valid(inverse_symbol(s), n),
{
}

} //  verus!


//  ================================================================
//  FILE: word.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;

verus! {

///  A word is a finite sequence of symbols.
///  The empty word represents the group identity.
pub type Word = Seq<Symbol>;

///  The empty word (identity element).
pub open spec fn empty_word() -> Word {
    Seq::empty()
}

///  Concatenation of two words.
pub open spec fn concat(w1: Word, w2: Word) -> Word {
    w1 + w2
}

///  The formal inverse of a word: reverse and invert each symbol.
///  (s₁ s₂ ... sₙ)⁻¹ = sₙ⁻¹ ... s₂⁻¹ s₁⁻¹
pub open spec fn inverse_word(w: Word) -> Word
    decreases w.len(),
{
    if w.len() == 0 {
        empty_word()
    } else {
        inverse_word(w.drop_first()) + Seq::new(1, |_i: int| inverse_symbol(w.first()))
    }
}

///  Length of the inverse word equals the original.
pub proof fn lemma_inverse_word_len(w: Word)
    ensures
        inverse_word(w).len() == w.len(),
    decreases w.len(),
{
    if w.len() > 0 {
        lemma_inverse_word_len(w.drop_first());
    }
}

///  All symbols in a word are valid for a group with `n` generators.
pub open spec fn word_valid(w: Word, n: nat) -> bool {
    forall|i: int| 0 <= i < w.len() ==> symbol_valid(#[trigger] w[i], n)
}

///  The inverse of the empty word is empty.
pub proof fn lemma_inverse_empty()
    ensures
        inverse_word(empty_word()) == empty_word(),
{
}

///  Inverse of a single-symbol word.
pub proof fn lemma_inverse_singleton(s: Symbol)
    ensures
        inverse_word(Seq::new(1, |_i: int| s)) =~= Seq::new(1, |_i: int| inverse_symbol(s)),
{
    let w = Seq::new(1, |_i: int| s);
    assert(w.len() == 1);
    assert(w.first() == s);
    assert(w.drop_first() =~= empty_word());
    assert(inverse_word(w) =~= inverse_word(empty_word()) + Seq::new(1, |_i: int| inverse_symbol(s)));
    assert(inverse_word(empty_word()) =~= empty_word());
}

///  Inverse distributes over concatenation (reversed).
///  (w1 · w2)⁻¹ = w2⁻¹ · w1⁻¹
pub proof fn lemma_inverse_concat(w1: Word, w2: Word)
    ensures
        inverse_word(concat(w1, w2)) =~= concat(inverse_word(w2), inverse_word(w1)),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
        assert(inverse_word(w1) =~= empty_word());
        assert(concat(inverse_word(w2), empty_word()) =~= inverse_word(w2));
    } else {
        //  w1 = first · rest
        let first = w1.first();
        let rest = w1.drop_first();
        //  concat(w1, w2) = first · concat(rest, w2)
        assert(concat(w1, w2).drop_first() =~= concat(rest, w2));
        assert(concat(w1, w2).first() == first);

        //  IH: inverse(concat(rest, w2)) =~= concat(inverse(w2), inverse(rest))
        lemma_inverse_concat(rest, w2);

        //  inverse(w1) = inverse(rest) · inv(first)
        //  inverse(concat(w1, w2)) = inverse(concat(rest, w2)) · inv(first)
        //                          = concat(inverse(w2), inverse(rest)) · inv(first)
        //                          = concat(inverse(w2), inverse(rest) · inv(first))
        //                          = concat(inverse(w2), inverse(w1))
        let inv_first = Seq::new(1, |_i: int| inverse_symbol(first));
        assert(inverse_word(w1) =~= inverse_word(rest) + inv_first);
        assert(inverse_word(concat(w1, w2)) =~= (inverse_word(w2) + inverse_word(rest)) + inv_first);
        assert(concat(inverse_word(w2), inverse_word(w1)) =~= inverse_word(w2) + (inverse_word(rest) + inv_first));
        //  Seq concat is associative
        assert(((inverse_word(w2) + inverse_word(rest)) + inv_first) =~= (inverse_word(w2) + (inverse_word(rest) + inv_first)));
    }
}

///  Inverse is an involution: (w⁻¹)⁻¹ = w.
pub proof fn lemma_inverse_involution(w: Word)
    ensures
        inverse_word(inverse_word(w)) =~= w,
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let first = w.first();
        let rest = w.drop_first();
        let inv_first = Seq::new(1, |_i: int| inverse_symbol(first));

        //  inverse(w) = inverse(rest) · inv(first)
        lemma_inverse_involution(rest);

        //  inverse(inverse(w)) = inverse(inverse(rest) · inv(first))
        //                      = inverse(inv(first)) · inverse(inverse(rest))    by lemma_inverse_concat
        //                      = first · rest = w                                 by IH
        lemma_inverse_concat(inverse_word(rest), inv_first);

        //  inverse(inv(first)) = [first]
        lemma_inverse_singleton(inverse_symbol(first));
        crate::symbol::lemma_inverse_involution(first);
        assert(inverse_word(inv_first) =~= Seq::new(1, |_i: int| first));

        assert(w =~= Seq::new(1, |_i: int| first) + rest);
    }
}

///  Concatenation with the empty word (right identity).
pub proof fn lemma_concat_empty_right(w: Word)
    ensures
        concat(w, empty_word()) =~= w,
{
}

///  Concatenation with the empty word (left identity).
pub proof fn lemma_concat_empty_left(w: Word)
    ensures
        concat(empty_word(), w) =~= w,
{
}

///  Concatenation is associative.
pub proof fn lemma_concat_assoc(w1: Word, w2: Word, w3: Word)
    ensures
        concat(concat(w1, w2), w3) =~= concat(w1, concat(w2, w3)),
{
}

///  Length of concatenation is sum of lengths.
pub proof fn lemma_concat_len(w1: Word, w2: Word)
    ensures
        concat(w1, w2).len() == w1.len() + w2.len(),
{
}

///  inverse_word preserves word_valid.
pub proof fn lemma_inverse_word_valid(w: Word, n: nat)
    requires word_valid(w, n),
    ensures word_valid(inverse_word(w), n),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(inverse_word(w) =~= empty_word());
    } else {
        let rest = w.drop_first();
        assert(word_valid(rest, n)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies symbol_valid(rest[i], n) by { assert(rest[i] == w[i + 1]); }
        }
        lemma_inverse_word_valid(rest, n);
        let inv_rest = inverse_word(rest);
        let inv_first = inverse_symbol(w.first());
        assert(inverse_word(w) =~= inv_rest + seq![inv_first]);
        lemma_inverse_preserves_valid(w.first(), n);
        assert forall|i: int| 0 <= i < inverse_word(w).len()
            implies symbol_valid(inverse_word(w)[i], n)
        by {
            if i < inv_rest.len() {
                assert(inverse_word(w)[i] == inv_rest[i]);
            } else {
                assert(inverse_word(w)[i] == inv_first);
            }
        }
    }
}

///  Concatenation preserves word_valid.
pub proof fn lemma_concat_word_valid(w1: Word, w2: Word, n: nat)
    requires word_valid(w1, n), word_valid(w2, n),
    ensures word_valid(concat(w1, w2), n),
{
    assert forall|k: int| 0 <= k < concat(w1, w2).len()
        implies symbol_valid(concat(w1, w2)[k], n)
    by {
        if k < w1.len() {
            assert(concat(w1, w2)[k] == w1[k]);
        } else {
            assert(concat(w1, w2)[k] == w2[k - w1.len()]);
        }
    }
}

} //  verus!


//  ================================================================
//  FILE: reduction.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;

verus! {

///  A word has a cancellation at position i: symbols at i and i+1 are inverse pairs.
pub open spec fn has_cancellation_at(w: Word, i: int) -> bool {
    0 <= i < w.len() - 1 && is_inverse_pair(w[i], w[i + 1])
}

///  A word has at least one cancellation somewhere.
pub open spec fn has_cancellation(w: Word) -> bool {
    exists|i: int| has_cancellation_at(w, i)
}

///  A word is freely reduced: no adjacent inverse pairs.
pub open spec fn is_reduced(w: Word) -> bool {
    !has_cancellation(w)
}

///  Remove the inverse pair at position i, producing a shorter word.
///  w[0..i] ++ w[i+2..]
pub open spec fn reduce_at(w: Word, i: int) -> Word
    recommends
        has_cancellation_at(w, i),
{
    w.subrange(0, i) + w.subrange(i + 2, w.len() as int)
}

///  reduce_at decreases length by 2.
pub proof fn lemma_reduce_at_len(w: Word, i: int)
    requires
        has_cancellation_at(w, i),
    ensures
        reduce_at(w, i).len() == w.len() - 2,
{
}

///  reduce_at preserves elements outside the cancelled pair.
pub proof fn lemma_reduce_at_elements(w: Word, i: int)
    requires
        has_cancellation_at(w, i),
    ensures
        forall|k: int| 0 <= k < i ==> #[trigger] reduce_at(w, i)[k] == w[k],
        forall|k: int| i <= k < reduce_at(w, i).len() ==> #[trigger] reduce_at(w, i)[k] == w[k + 2],
{
}

///  Single-step free reduction: w1 reduces to w2 by removing one inverse pair.
pub open spec fn reduces_one_step(w1: Word, w2: Word) -> bool {
    exists|i: int| has_cancellation_at(w1, i) && w2 == reduce_at(w1, i)
}

///  Multi-step free reduction: transitive-reflexive closure.
///  w1 reduces to w2 in at most `n` steps.
pub open spec fn reduces_in_steps(w1: Word, w2: Word, n: nat) -> bool
    decreases n,
{
    if n == 0 {
        w1 == w2
    } else {
        w1 == w2 || exists|w_mid: Word|
            reduces_one_step(w1, w_mid) && reduces_in_steps(w_mid, w2, (n - 1) as nat)
    }
}

///  w1 freely reduces to w2 (in some number of steps).
pub open spec fn reduces_to(w1: Word, w2: Word) -> bool {
    exists|n: nat| reduces_in_steps(w1, w2, n)
}

///  Two words are freely equivalent (connected by reductions and expansions).
pub open spec fn freely_equivalent(w1: Word, w2: Word) -> bool {
    exists|w: Word| reduces_to(w1, w) && reduces_to(w2, w)
}

//  --- Basic reduction lemmas ---

///  Every word reduces to itself (0 steps).
pub proof fn lemma_reduces_to_refl(w: Word)
    ensures
        reduces_to(w, w),
{
    assert(reduces_in_steps(w, w, 0));
}

///  If w1 reduces to w2 in n steps, it also reduces in n+1 steps.
pub proof fn lemma_reduces_in_steps_monotone(w1: Word, w2: Word, n: nat)
    requires
        reduces_in_steps(w1, w2, n),
    ensures
        reduces_in_steps(w1, w2, (n + 1) as nat),
    decreases n,
{
    if n == 0 {
    } else {
        if w1 == w2 {
        } else {
            let w_mid = choose|w_mid: Word|
                reduces_one_step(w1, w_mid) && reduces_in_steps(w_mid, w2, (n - 1) as nat);
            lemma_reduces_in_steps_monotone(w_mid, w2, (n - 1) as nat);
            assert(reduces_in_steps(w_mid, w2, n as nat));
        }
    }
}

///  Transitivity: if w1 →* w2 and w2 →* w3, then w1 →* w3.
pub proof fn lemma_reduces_to_transitive(w1: Word, w2: Word, w3: Word)
    requires
        reduces_to(w1, w2),
        reduces_to(w2, w3),
    ensures
        reduces_to(w1, w3),
{
    let n1 = choose|n: nat| reduces_in_steps(w1, w2, n);
    let n2 = choose|n: nat| reduces_in_steps(w2, w3, n);
    lemma_reduces_chain(w1, w2, w3, n1, n2);
}

///  Helper: chaining reductions with explicit step counts.
proof fn lemma_reduces_chain(w1: Word, w2: Word, w3: Word, n1: nat, n2: nat)
    requires
        reduces_in_steps(w1, w2, n1),
        reduces_in_steps(w2, w3, n2),
    ensures
        reduces_to(w1, w3),
    decreases n1,
{
    if n1 == 0 {
        assert(reduces_in_steps(w1, w3, n2));
    } else {
        if w1 == w2 {
            assert(reduces_in_steps(w1, w3, n2));
        } else {
            let w_mid = choose|w_mid: Word|
                reduces_one_step(w1, w_mid) && reduces_in_steps(w_mid, w2, (n1 - 1) as nat);
            lemma_reduces_chain(w_mid, w2, w3, (n1 - 1) as nat, n2);
            let n3 = choose|n: nat| reduces_in_steps(w_mid, w3, n);
            assert(reduces_in_steps(w1, w3, (n3 + 1) as nat));
        }
    }
}

///  A reduced word has no cancellations, so it doesn't reduce further.
pub proof fn lemma_reduced_no_step(w: Word)
    requires
        is_reduced(w),
    ensures
        !exists|w2: Word| reduces_one_step(w, w2),
{
}

///  The empty word is reduced.
pub proof fn lemma_empty_is_reduced()
    ensures
        is_reduced(empty_word()),
{
    assert forall|i: int| !has_cancellation_at(empty_word(), i) by {
    }
}

///  A single symbol is reduced.
pub proof fn lemma_singleton_is_reduced(s: Symbol)
    ensures
        is_reduced(Seq::new(1, |_i: int| s)),
{
    let w = Seq::new(1, |_i: int| s);
    assert forall|i: int| !has_cancellation_at(w, i) by {
    }
}

///  Free equivalence is reflexive.
pub proof fn lemma_freely_equivalent_refl(w: Word)
    ensures
        freely_equivalent(w, w),
{
    lemma_reduces_to_refl(w);
}

///  Free equivalence is symmetric.
pub proof fn lemma_freely_equivalent_sym(w1: Word, w2: Word)
    requires
        freely_equivalent(w1, w2),
    ensures
        freely_equivalent(w2, w1),
{
    let w = choose|w: Word| reduces_to(w1, w) && reduces_to(w2, w);
    assert(reduces_to(w2, w) && reduces_to(w1, w));
}

///  Free equivalence is transitive.
pub proof fn lemma_freely_equivalent_trans(w1: Word, w2: Word, w3: Word)
    requires
        freely_equivalent(w1, w2),
        freely_equivalent(w2, w3),
    ensures
        freely_equivalent(w1, w3),
{
    //  w1 →* u ←* w2 →* v ←* w3
    let u = choose|w: Word| reduces_to(w1, w) && reduces_to(w2, w);
    let v = choose|w: Word| reduces_to(w2, w) && reduces_to(w3, w);
    //  By confluence on w2 →* u and w2 →* v: ∃ t. u →* t ∧ v →* t
    lemma_confluence(w2, u, v);
    let t = choose|t: Word| reduces_to(u, t) && reduces_to(v, t);
    //  w1 →* u →* t and w3 →* v →* t
    lemma_reduces_to_transitive(w1, u, t);
    lemma_reduces_to_transitive(w3, v, t);
}

//  ============================================================
//  Church-Rosser (Confluence) via Newman's Lemma
//  ============================================================

///  One step of reduction decreases word length by exactly 2.
pub proof fn lemma_one_step_decreases_len(w1: Word, w2: Word)
    requires
        reduces_one_step(w1, w2),
    ensures
        w2.len() == w1.len() - 2,
{
    let i = choose|i: int| has_cancellation_at(w1, i) && w2 == reduce_at(w1, i);
    lemma_reduce_at_len(w1, i);
}

///  Multi-step reduction never increases word length.
pub proof fn lemma_reduces_to_len(w1: Word, w2: Word, n: nat)
    requires
        reduces_in_steps(w1, w2, n),
    ensures
        w2.len() <= w1.len(),
    decreases n,
{
    if n == 0 {
    } else if w1 == w2 {
    } else {
        let w_mid = choose|w_mid: Word|
            reduces_one_step(w1, w_mid) && reduces_in_steps(w_mid, w2, (n - 1) as nat);
        lemma_one_step_decreases_len(w1, w_mid);
        lemma_reduces_to_len(w_mid, w2, (n - 1) as nat);
    }
}

///  Confluence: if w →* w1 and w →* w2, then ∃ w3. w1 →* w3 ∧ w2 →* w3.
///
///  Proof by induction on |w| (word length). Uses:
///  - Termination: each reduction step decreases length by 2
///  - Local confluence: if w →¹ w1 and w →¹ w2, then ∃ w3. w1 →* w3 ∧ w2 →* w3
///  - Newman's lemma: termination + local confluence → confluence
pub proof fn lemma_confluence(w: Word, w1: Word, w2: Word)
    requires
        reduces_to(w, w1),
        reduces_to(w, w2),
    ensures
        exists|w3: Word| reduces_to(w1, w3) && reduces_to(w2, w3),
    decreases w.len(),
{
    let n1 = choose|n: nat| reduces_in_steps(w, w1, n);
    let n2 = choose|n: nat| reduces_in_steps(w, w2, n);

    if n1 == 0 || w == w1 {
        //  w == w1
        lemma_reduces_to_refl(w2);
        assert(reduces_in_steps(w, w2, n2));
    } else if n2 == 0 || w == w2 {
        //  w == w2
        lemma_reduces_to_refl(w1);
        assert(reduces_in_steps(w, w1, n1));
    } else {
        //  w →¹ wa →* w1 and w →¹ wb →* w2
        let wa = choose|wa: Word|
            reduces_one_step(w, wa) && reduces_in_steps(wa, w1, (n1 - 1) as nat);
        let wb = choose|wb: Word|
            reduces_one_step(w, wb) && reduces_in_steps(wb, w2, (n2 - 1) as nat);

        //  wa, wb have length w.len() - 2
        lemma_one_step_decreases_len(w, wa);
        lemma_one_step_decreases_len(w, wb);

        //  By local confluence: ∃ wc. wa →* wc ∧ wb →* wc
        lemma_local_confluence(w, wa, wb);
        let wc = choose|wc: Word| reduces_to(wa, wc) && reduces_to(wb, wc);

        //  wc.len() <= wa.len() = w.len() - 2 < w.len()
        let nc_a = choose|n: nat| reduces_in_steps(wa, wc, n);
        lemma_reduces_to_len(wa, wc, nc_a);

        //  IH on wa: confluence of (wa →* w1, wa →* wc)
        lemma_confluence(wa, w1, wc);
        let d = choose|d: Word| reduces_to(w1, d) && reduces_to(wc, d);

        //  IH on wb: confluence of (wb →* w2, wb →* wc)
        lemma_confluence(wb, w2, wc);
        let e = choose|e: Word| reduces_to(w2, e) && reduces_to(wc, e);

        //  IH on wc: confluence of (wc →* d, wc →* e)
        lemma_confluence(wc, d, e);
        let w3 = choose|w3: Word| reduces_to(d, w3) && reduces_to(e, w3);

        //  Chain: w1 →* d →* w3 and w2 →* e →* w3
        lemma_reduces_to_transitive(w1, d, w3);
        lemma_reduces_to_transitive(w2, e, w3);
    }
}

//  ============================================================
//  Church-Rosser / Confluence
//  ============================================================

///  Find the first cancellation position, searching from index `start`.
///  Returns the first i >= start with a cancellation, or w.len() if none.
pub open spec fn find_cancellation_from(w: Word, start: nat) -> nat
    decreases w.len() - start,
{
    if start >= w.len() - 1 {
        w.len()
    } else if is_inverse_pair(w[start as int], w[start as int + 1]) {
        start
    } else {
        find_cancellation_from(w, start + 1)
    }
}

///  find_cancellation_from returns a valid cancellation or w.len().
pub proof fn lemma_find_cancellation_from_valid(w: Word, start: nat)
    ensures
        find_cancellation_from(w, start) < w.len() ==>
            has_cancellation_at(w, find_cancellation_from(w, start) as int),
    decreases w.len() - start,
{
    if start >= w.len() - 1 {
    } else if is_inverse_pair(w[start as int], w[start as int + 1]) {
    } else {
        lemma_find_cancellation_from_valid(w, start + 1);
    }
}

///  If find_cancellation_from returns w.len(), there is no cancellation at any position >= start.
pub proof fn lemma_find_cancellation_from_none(w: Word, start: nat, j: int)
    requires
        find_cancellation_from(w, start) >= w.len(),
        start as int <= j,
        j < w.len() - 1,
    ensures
        !is_inverse_pair(w[j], w[j + 1]),
    decreases w.len() - start,
{
    if start >= w.len() - 1 {
        //  j < w.len() - 1 and start >= w.len() - 1 and start <= j — contradiction
    } else if is_inverse_pair(w[start as int], w[start as int + 1]) {
        //  find_cancellation_from returns start < w.len() — contradicts requires
    } else {
        if j == start as int {
            //  !is_inverse_pair(w[start], w[start+1]) is the branch condition
        } else {
            lemma_find_cancellation_from_none(w, start + 1, j);
        }
    }
}

///  Iterated reduction with explicit fuel (half the word length suffices).
///  Each step removes 2 symbols, so w.len()/2 steps is enough.
pub open spec fn reduce_n_steps(w: Word, fuel: nat) -> Word
    decreases fuel,
{
    if fuel == 0 {
        w
    } else {
        let pos = find_cancellation_from(w, 0);
        if pos >= w.len() {
            w
        } else {
            reduce_n_steps(reduce_at(w, pos as int), (fuel - 1) as nat)
        }
    }
}

///  Normal form: reduce with enough fuel.
pub open spec fn normal_form(w: Word) -> Word {
    reduce_n_steps(w, w.len())
}

///  Helper: if find_cancellation_from finds a position, it's a valid cancellation.
proof fn lemma_find_gives_cancellation(w: Word)
    requires
        find_cancellation_from(w, 0) < w.len(),
    ensures
        has_cancellation_at(w, find_cancellation_from(w, 0) as int),
{
    lemma_find_cancellation_from_valid(w, 0);
}

///  reduce_n_steps with 0 fuel returns the input.
pub proof fn lemma_reduce_n_steps_zero(w: Word)
    ensures
        reduce_n_steps(w, 0) == w,
{
}

///  If w has no cancellation, reduce_n_steps returns w regardless of fuel.
pub proof fn lemma_reduce_n_steps_reduced(w: Word, fuel: nat)
    requires
        is_reduced(w),
    ensures
        reduce_n_steps(w, fuel) == w,
    decreases fuel,
{
    if fuel == 0 {
    } else {
        let pos = find_cancellation_from(w, 0);
        lemma_find_cancellation_from_valid(w, 0);
        assert(pos >= w.len()) by {
            if pos < w.len() {
                assert(has_cancellation(w));
            }
        };
    }
}

///  The normal form is reduced.
pub proof fn lemma_normal_form_is_reduced(w: Word)
    ensures
        is_reduced(normal_form(w)),
{
    lemma_reduce_n_steps_is_reduced(w, w.len());
}

///  reduce_n_steps always produces a reduced word when given enough fuel.
///  fuel >= w.len() is always sufficient since each step removes 2 chars.
proof fn lemma_reduce_n_steps_is_reduced(w: Word, fuel: nat)
    requires
        fuel >= w.len(),
    ensures
        is_reduced(reduce_n_steps(w, fuel)),
    decreases fuel,
{
    if fuel == 0 {
        //  fuel >= w.len() and fuel == 0 means w.len() == 0, so w is empty
        assert(w =~= empty_word());
        lemma_empty_is_reduced();
    } else {
        let pos = find_cancellation_from(w, 0);
        lemma_find_cancellation_from_valid(w, 0);
        if pos >= w.len() {
            assert forall|i: int| !has_cancellation_at(w, i) by {
                if 0 <= i < (w.len() - 1) as int {
                    lemma_find_cancellation_from_none(w, 0, i);
                }
            }
        } else {
            lemma_reduce_at_len(w, pos as int);
            //  reduce_at(w, pos).len() == w.len() - 2, and fuel - 1 >= w.len() - 1 >= w.len() - 2
            lemma_reduce_n_steps_is_reduced(reduce_at(w, pos as int), (fuel - 1) as nat);
        }
    }
}

///  The original word reduces to its normal form.
pub proof fn lemma_reduces_to_normal_form(w: Word)
    ensures
        reduces_to(w, normal_form(w)),
{
    lemma_reduce_n_steps_reduces(w, w.len());
}

///  reduce_n_steps produces a word reachable by reduction.
proof fn lemma_reduce_n_steps_reduces(w: Word, fuel: nat)
    ensures
        reduces_to(w, reduce_n_steps(w, fuel)),
    decreases fuel,
{
    if fuel == 0 {
        lemma_reduces_to_refl(w);
    } else {
        let pos = find_cancellation_from(w, 0);
        lemma_find_cancellation_from_valid(w, 0);
        if pos >= w.len() {
            lemma_reduces_to_refl(w);
        } else {
            let w2 = reduce_at(w, pos as int);
            lemma_reduce_n_steps_reduces(w2, (fuel - 1) as nat);
            //  w →¹ w2 →* reduce_n_steps(w2, fuel-1)
            assert(reduces_one_step(w, w2));
            let n = choose|n: nat| reduces_in_steps(w2, reduce_n_steps(w, fuel), n);
            assert(reduces_in_steps(w, reduce_n_steps(w, fuel), (n + 1) as nat));
        }
    }
}

//  --- Local Confluence ---

///  Local confluence: if w →¹ w1 and w →¹ w2, then ∃ w3. w1 →* w3 ∧ w2 →* w3.
///
///  Cases:
///  - Same position: w1 == w2 (trivial)
///  - Disjoint positions (|i-j| >= 2): both reductions commute, w3 = reduce both
///  - Overlapping (|i-j| == 1): e.g. i=k, j=k+1 means w[k]w[k+1]w[k+2] where
///    w[k]w[k+1] cancel AND w[k+1]w[k+2] cancel. This means w[k] = inv(w[k+1])
///    and w[k+1] = inv(w[k+2]), so w[k] = inv(inv(w[k+2])) = w[k+2].
///    After either reduction, the remaining pair also cancels → same result.
pub proof fn lemma_local_confluence(w: Word, w1: Word, w2: Word)
    requires
        reduces_one_step(w, w1),
        reduces_one_step(w, w2),
    ensures
        exists|w3: Word| reduces_to(w1, w3) && reduces_to(w2, w3),
{
    let i = choose|i: int| has_cancellation_at(w, i) && w1 == reduce_at(w, i);
    let j = choose|j: int| has_cancellation_at(w, j) && w2 == reduce_at(w, j);

    if i == j {
        //  Case 1: Same position → same result
        assert(w1 == w2);
        lemma_reduces_to_refl(w1);
    } else if i < j {
        if j == i + 1 {
            //  Case 2: Overlapping — positions i and i+1
            //  w[i]=A, w[i+1]=B, w[i+2]=C
            //  AB cancel: A = inv(B), BC cancel: B = inv(C)
            //  So A = inv(B) = inv(inv(C)) = C
            lemma_overlapping_confluence(w, w1, w2, i);
        } else {
            //  Case 3: Disjoint — |i-j| >= 2
            lemma_disjoint_confluence(w, w1, w2, i, j);
        }
    } else {
        //  j < i, symmetric
        if i == j + 1 {
            lemma_overlapping_confluence(w, w2, w1, j);
            let w3 = choose|w3: Word| reduces_to(w2, w3) && reduces_to(w1, w3);
            assert(reduces_to(w1, w3) && reduces_to(w2, w3));
        } else {
            lemma_disjoint_confluence(w, w2, w1, j, i);
            let w3 = choose|w3: Word| reduces_to(w2, w3) && reduces_to(w1, w3);
            assert(reduces_to(w1, w3) && reduces_to(w2, w3));
        }
    }
}

///  Overlapping case: cancellations at adjacent positions i and i+1.
///  w[i]=A, w[i+1]=B, w[i+2]=C with AB and BC both inverse pairs.
///  Then A=C, so both reductions give the same result.
proof fn lemma_overlapping_confluence(w: Word, w1: Word, w2: Word, i: int)
    requires
        has_cancellation_at(w, i),
        has_cancellation_at(w, i + 1),
        w1 == reduce_at(w, i),
        w2 == reduce_at(w, i + 1),
    ensures
        exists|w3: Word| reduces_to(w1, w3) && reduces_to(w2, w3),
{
    //  A = w[i], B = w[i+1], C = w[i+2]
    //  is_inverse_pair(A, B) and is_inverse_pair(B, C)
    //  means B = inverse_symbol(A) and C = inverse_symbol(B) = inverse_symbol(inverse_symbol(A)) = A
    let a = w[i];
    let b = w[i + 1];
    let c = w[i + 2];
    assert(is_inverse_pair(a, b));
    assert(is_inverse_pair(b, c));
    //  b == inverse_symbol(a), c == inverse_symbol(b)
    assert(b == inverse_symbol(a));
    assert(c == inverse_symbol(b));
    crate::symbol::lemma_inverse_involution(a);
    assert(c == a);

    //  w1 = w[0..i] ++ w[i+2..] — removed positions i,i+1 (A,B)
    //  w2 = w[0..i+1] ++ w[i+3..] — removed positions i+1,i+2 (B,C)
    //  w1 = w[0..i] ++ [C] ++ w[i+3..]
    //  w2 = w[0..i] ++ [A] ++ w[i+3..]
    //  Since A == C, w1 =~= w2
    assert(w1 =~= w2) by {
        lemma_reduce_at_len(w, i);
        lemma_reduce_at_len(w, i + 1);
        assert(w1.len() == w2.len());
        assert forall|k: int| 0 <= k < w1.len() implies #[trigger] w1[k] == w2[k] by {
            lemma_reduce_at_elements(w, i);
            lemma_reduce_at_elements(w, i + 1);
            if k < i {
                assert(w1[k] == w[k]);
                assert(w2[k] == w[k]);
            } else if k == i {
                assert(w1[k] == w[k + 2]); //  C
                assert(w2[k] == w[k]); //  A
                assert(w[k] == a);
                assert(w[k + 2] == c);
            } else {
                //  k > i: w1[k] == w[k+2], w2[k] == w[k+2]
                assert(w1[k] == w[k + 2]);
                assert(w2[k] == w[k + 2]);
            }
        };
    };
    lemma_reduces_to_refl(w1);
}

///  Disjoint case: cancellations at positions i and j with i + 2 <= j.
///  Both reductions commute to a common reduct.
proof fn lemma_disjoint_confluence(w: Word, w1: Word, w2: Word, i: int, j: int)
    requires
        has_cancellation_at(w, i),
        has_cancellation_at(w, j),
        i + 2 <= j,
        w1 == reduce_at(w, i),
        w2 == reduce_at(w, j),
    ensures
        exists|w3: Word| reduces_to(w1, w3) && reduces_to(w2, w3),
{
    //  w1 still has cancellation at j-2, w2 still has cancellation at i
    //  Use reduce_at(w1, j-2) as the common reduct
    lemma_reduce_at_len(w, i);
    lemma_reduce_at_elements(w, i);
    assert(has_cancellation_at(w1, j - 2)) by {
        assert(w1[j - 2] == w[j]);
        assert(w1[j - 2 + 1] == w[j + 1]);
    };
    let w3 = reduce_at(w1, j - 2);

    //  w1 →¹ w3: witness the existentials explicitly
    assert(has_cancellation_at(w1, j - 2) && w3 == reduce_at(w1, j - 2));
    //  reduces_in_steps(w1, w3, 1) needs witness w_mid = w3
    assert(reduces_in_steps(w3, w3, 0));
    assert(reduces_one_step(w1, w3) && reduces_in_steps(w3, w3, 0));

    //  Show w2 has cancellation at i and reduce_at(w2, i) == w3
    lemma_reduce_at_len(w, j);
    lemma_reduce_at_elements(w, j);
    assert(has_cancellation_at(w2, i)) by {
        assert(w2[i] == w[i]);
        assert(w2[i + 1] == w[i + 1]);
    };
    let w2_reduced = reduce_at(w2, i);
    assert(w2_reduced =~= w3) by {
        lemma_reduce_at_len(w1, j - 2);
        lemma_reduce_at_elements(w1, j - 2);
        lemma_reduce_at_len(w2, i);
        lemma_reduce_at_elements(w2, i);
        assert(w3.len() == w2_reduced.len());
        assert forall|k: int| 0 <= k < w3.len() implies #[trigger] w3[k] == w2_reduced[k] by {
            if k < i {
                //  w3[k] = w1[k] = w[k], w2_reduced[k] = w2[k] = w[k]
                assert(w3[k] == w1[k]);
                assert(w1[k] == w[k]);
                assert(w2_reduced[k] == w2[k]);
                assert(w2[k] == w[k]);
            } else if k < j - 2 {
                //  w3[k] = w1[k] = w[k+2], w2_reduced[k] = w2[k+2] = w[k+2]
                assert(w3[k] == w1[k]);
                assert(w1[k] == w[k + 2]);
                assert(w2_reduced[k] == w2[k + 2]);
                assert(w2[k + 2] == w[k + 2]);
            } else {
                //  w3[k] = w1[k+2] = w[k+4], w2_reduced[k] = w2[k+2] = w[k+4]
                assert(w3[k] == w1[k + 2]);
                assert(w1[k + 2] == w[k + 4]);
                assert(w2_reduced[k] == w2[k + 2]);
                assert(w2[k + 2] == w[k + 4]);
            }
        };
    };
    //  w2 →¹ w2_reduced =~= w3, so w2 →¹ w3
    assert(has_cancellation_at(w2, i) && w3 == reduce_at(w2, i)) by {
        assert(w2_reduced == w3); //  from =~= for Seq
    };
    assert(reduces_in_steps(w3, w3, 0));
    assert(reduces_one_step(w2, w3) && reduces_in_steps(w3, w3, 0));

    //  Witness reduces_to
    assert(reduces_in_steps(w1, w3, 1nat));
    assert(reduces_in_steps(w2, w3, 1nat));
    assert(reduces_to(w1, w3));
    assert(reduces_to(w2, w3));
}

//  ============================================================
//  Reduction Respects Concatenation
//  ============================================================

///  If w1 reduces in one step to wa, then concat(w1, w2) reduces in one step to concat(wa, w2).
///  Proof: cancellation at position i in w1 is also at position i in concat(w1, w2),
///  and reduce_at(concat(w1, w2), i) =~= concat(reduce_at(w1, i), w2).
pub proof fn lemma_one_step_concat_left(w1: Word, wa: Word, w2: Word)
    requires
        reduces_one_step(w1, wa),
    ensures
        reduces_one_step(concat(w1, w2), concat(wa, w2)),
{
    let i = choose|i: int| has_cancellation_at(w1, i) && wa == reduce_at(w1, i);
    let cw = concat(w1, w2);
    //  cancellation at i in w1 means i < w1.len() - 1, so i < cw.len() - 1
    assert(cw[i] == w1[i]);
    assert(cw[i + 1] == w1[i + 1]);
    assert(has_cancellation_at(cw, i));
    //  Show reduce_at(cw, i) =~= concat(wa, w2)
    assert(reduce_at(cw, i) =~= concat(reduce_at(w1, i), w2)) by {
        lemma_reduce_at_len(cw, i);
        lemma_reduce_at_len(w1, i);
        lemma_reduce_at_elements(cw, i);
        lemma_reduce_at_elements(w1, i);
        let result = reduce_at(cw, i);
        let expected = concat(reduce_at(w1, i), w2);
        assert(result.len() == expected.len());
        assert forall|k: int| 0 <= k < result.len() implies #[trigger] result[k] == expected[k] by {
            if k < i {
                assert(result[k] == cw[k]);
                assert(cw[k] == w1[k]);
                assert(expected[k] == reduce_at(w1, i)[k]);
                assert(reduce_at(w1, i)[k] == w1[k]);
            } else if k < (w1.len() - 2) as int {
                assert(result[k] == cw[k + 2]);
                assert(cw[k + 2] == w1[k + 2]);
                assert(expected[k] == reduce_at(w1, i)[k]);
                assert(reduce_at(w1, i)[k] == w1[k + 2]);
            } else {
                //  k >= w1.len() - 2, in the w2 part
                assert(result[k] == cw[k + 2]);
                let w2_idx = k - (w1.len() - 2) as int;
                assert(cw[k + 2] == w2[w2_idx]);
                assert(expected[k] == w2[w2_idx]);
            }
        };
    };
    assert(has_cancellation_at(cw, i) && concat(wa, w2) == reduce_at(cw, i));
}

///  If w1 reduces to w1' (multi-step), then concat(w1, w2) reduces to concat(w1', w2).
pub proof fn lemma_reduces_to_concat_left(w1: Word, w1_prime: Word, w2: Word)
    requires
        reduces_to(w1, w1_prime),
    ensures
        reduces_to(concat(w1, w2), concat(w1_prime, w2)),
{
    let n = choose|n: nat| reduces_in_steps(w1, w1_prime, n);
    lemma_reduces_to_concat_left_aux(w1, w1_prime, w2, n);
}

proof fn lemma_reduces_to_concat_left_aux(w1: Word, w1_prime: Word, w2: Word, n: nat)
    requires
        reduces_in_steps(w1, w1_prime, n),
    ensures
        reduces_to(concat(w1, w2), concat(w1_prime, w2)),
    decreases n,
{
    if n == 0 {
        lemma_reduces_to_refl(concat(w1, w2));
    } else if w1 == w1_prime {
        lemma_reduces_to_refl(concat(w1, w2));
    } else {
        let w_mid = choose|w_mid: Word|
            reduces_one_step(w1, w_mid) && reduces_in_steps(w_mid, w1_prime, (n - 1) as nat);
        lemma_one_step_concat_left(w1, w_mid, w2);
        //  concat(w1, w2) →¹ concat(w_mid, w2)
        let cw1 = concat(w1, w2);
        let cwm = concat(w_mid, w2);
        assert(reduces_in_steps(cw1, cwm, 1nat)) by {
            assert(reduces_in_steps(cwm, cwm, 0));
            assert(reduces_one_step(cw1, cwm) && reduces_in_steps(cwm, cwm, 0));
        };
        //  IH: concat(w_mid, w2) →* concat(w1_prime, w2)
        lemma_reduces_to_concat_left_aux(w_mid, w1_prime, w2, (n - 1) as nat);
        //  chain
        lemma_reduces_to_transitive(cw1, cwm, concat(w1_prime, w2));
    }
}

///  If w2 reduces in one step to wb, then concat(w1, w2) reduces in one step to concat(w1, wb).
///  Cancellation at position j in w2 maps to position j + w1.len() in concat(w1, w2).
pub proof fn lemma_one_step_concat_right(w1: Word, w2: Word, wb: Word)
    requires
        reduces_one_step(w2, wb),
    ensures
        reduces_one_step(concat(w1, w2), concat(w1, wb)),
{
    let j = choose|j: int| has_cancellation_at(w2, j) && wb == reduce_at(w2, j);
    let cw = concat(w1, w2);
    let offset = w1.len() as int;
    //  cancellation at j+offset in concat
    assert(cw[j + offset] == w2[j]);
    assert(cw[j + offset + 1] == w2[j + 1]);
    assert(has_cancellation_at(cw, j + offset));
    //  Show reduce_at(cw, j+offset) =~= concat(w1, wb)
    assert(reduce_at(cw, j + offset) =~= concat(w1, reduce_at(w2, j))) by {
        lemma_reduce_at_len(cw, j + offset);
        lemma_reduce_at_len(w2, j);
        lemma_reduce_at_elements(cw, j + offset);
        lemma_reduce_at_elements(w2, j);
        let result = reduce_at(cw, j + offset);
        let expected = concat(w1, reduce_at(w2, j));
        assert(result.len() == expected.len());
        assert forall|k: int| 0 <= k < result.len() implies #[trigger] result[k] == expected[k] by {
            if k < offset {
                assert(result[k] == cw[k]);
                assert(cw[k] == w1[k]);
                assert(expected[k] == w1[k]);
            } else if k < j + offset {
                assert(result[k] == cw[k]);
                assert(cw[k] == w2[k - offset]);
                assert(expected[k] == reduce_at(w2, j)[k - offset]);
                assert(reduce_at(w2, j)[k - offset] == w2[k - offset]);
            } else {
                //  k >= j + offset
                assert(result[k] == cw[k + 2]);
                assert(cw[k + 2] == w2[k + 2 - offset]);
                assert(expected[k] == reduce_at(w2, j)[k - offset]);
                assert(reduce_at(w2, j)[k - offset] == w2[k - offset + 2]);
            }
        };
    };
    assert(has_cancellation_at(cw, j + offset) && concat(w1, wb) == reduce_at(cw, j + offset));
}

///  If w2 reduces to w2' (multi-step), then concat(w1, w2) reduces to concat(w1, w2').
pub proof fn lemma_reduces_to_concat_right(w1: Word, w2: Word, w2_prime: Word)
    requires
        reduces_to(w2, w2_prime),
    ensures
        reduces_to(concat(w1, w2), concat(w1, w2_prime)),
{
    let n = choose|n: nat| reduces_in_steps(w2, w2_prime, n);
    lemma_reduces_to_concat_right_aux(w1, w2, w2_prime, n);
}

proof fn lemma_reduces_to_concat_right_aux(w1: Word, w2: Word, w2_prime: Word, n: nat)
    requires
        reduces_in_steps(w2, w2_prime, n),
    ensures
        reduces_to(concat(w1, w2), concat(w1, w2_prime)),
    decreases n,
{
    if n == 0 {
        lemma_reduces_to_refl(concat(w1, w2));
    } else if w2 == w2_prime {
        lemma_reduces_to_refl(concat(w1, w2));
    } else {
        let w_mid = choose|w_mid: Word|
            reduces_one_step(w2, w_mid) && reduces_in_steps(w_mid, w2_prime, (n - 1) as nat);
        lemma_one_step_concat_right(w1, w2, w_mid);
        let cw2 = concat(w1, w2);
        let cwm = concat(w1, w_mid);
        assert(reduces_in_steps(cw2, cwm, 1nat)) by {
            assert(reduces_in_steps(cwm, cwm, 0));
            assert(reduces_one_step(cw2, cwm) && reduces_in_steps(cwm, cwm, 0));
        };
        lemma_reduces_to_concat_right_aux(w1, w_mid, w2_prime, (n - 1) as nat);
        lemma_reduces_to_transitive(cw2, cwm, concat(w1, w2_prime));
    }
}

///  Reduction respects concatenation: if w1 →* w1' and w2 →* w2',
///  then concat(w1, w2) →* concat(w1', w2').
pub proof fn lemma_reduces_to_concat(w1: Word, w1_prime: Word, w2: Word, w2_prime: Word)
    requires
        reduces_to(w1, w1_prime),
        reduces_to(w2, w2_prime),
    ensures
        reduces_to(concat(w1, w2), concat(w1_prime, w2_prime)),
{
    lemma_reduces_to_concat_left(w1, w1_prime, w2);
    lemma_reduces_to_concat_right(w1_prime, w2, w2_prime);
    lemma_reduces_to_transitive(concat(w1, w2), concat(w1_prime, w2), concat(w1_prime, w2_prime));
}

//  ============================================================
//  Normal Form Uniqueness
//  ============================================================

///  A reduced word is its own normal form.
pub proof fn lemma_reduced_is_own_normal_form(w: Word)
    requires
        is_reduced(w),
    ensures
        normal_form(w) == w,
{
    lemma_reduce_n_steps_reduced(w, w.len());
}

///  If w reduces to r and r is reduced, then r is the normal form of w.
pub proof fn lemma_reduces_to_reduced_unique(w: Word, r: Word)
    requires
        reduces_to(w, r),
        is_reduced(r),
    ensures
        r == normal_form(w),
{
    //  w →* r and w →* nf(w). By confluence, ∃ s with r →* s ←* nf(w).
    lemma_reduces_to_normal_form(w);
    lemma_confluence(w, r, normal_form(w));
    let s = choose|s: Word| reduces_to(r, s) && reduces_to(normal_form(w), s);
    //  r is reduced, so r →* s means r == s
    lemma_reduced_no_step(r);
    lemma_reduced_reduces_to_self(r, s);
    //  nf(w) is reduced, so nf(w) →* s means nf(w) == s
    lemma_normal_form_is_reduced(w);
    lemma_reduced_no_step(normal_form(w));
    lemma_reduced_reduces_to_self(normal_form(w), s);
    //  r == s == nf(w)
}

///  A reduced word can only reduce to itself.
proof fn lemma_reduced_reduces_to_self(w: Word, w2: Word)
    requires
        is_reduced(w),
        reduces_to(w, w2),
    ensures
        w == w2,
{
    let n = choose|n: nat| reduces_in_steps(w, w2, n);
    lemma_reduced_reduces_to_self_aux(w, w2, n);
}

proof fn lemma_reduced_reduces_to_self_aux(w: Word, w2: Word, n: nat)
    requires
        is_reduced(w),
        reduces_in_steps(w, w2, n),
    ensures
        w == w2,
    decreases n,
{
    if n == 0 {
    } else {
        if w == w2 {
        } else {
            //  w →¹ w_mid → contradiction since w is reduced
            let w_mid = choose|w_mid: Word|
                reduces_one_step(w, w_mid) && reduces_in_steps(w_mid, w2, (n - 1) as nat);
            lemma_reduced_no_step(w);
            //  contradiction: reduces_one_step(w, w_mid) is impossible
            assert(false);
        }
    }
}

///  Forward direction: freely_equivalent(w1, w2) → normal_form(w1) == normal_form(w2).
pub proof fn lemma_normal_form_equiv_forward(w1: Word, w2: Word)
    requires
        freely_equivalent(w1, w2),
    ensures
        normal_form(w1) == normal_form(w2),
{
    //  ∃ w with w1 →* w ←* w2
    let w = choose|w: Word| reduces_to(w1, w) && reduces_to(w2, w);
    //  w1 →* nf(w1) and w1 →* w. By confluence, ∃ t1 with nf(w1) →* t1 ←* w.
    lemma_reduces_to_normal_form(w1);
    lemma_confluence(w1, normal_form(w1), w);
    let t1 = choose|t1: Word| reduces_to(normal_form(w1), t1) && reduces_to(w, t1);
    //  nf(w1) is reduced, so nf(w1) == t1
    lemma_normal_form_is_reduced(w1);
    lemma_reduced_reduces_to_self(normal_form(w1), t1);
    //  So w →* nf(w1)

    //  w2 →* w →* nf(w1). By transitivity: w2 →* nf(w1).
    lemma_reduces_to_transitive(w2, w, normal_form(w1));
    //  nf(w1) is reduced, so it's the normal form of w2
    lemma_reduces_to_reduced_unique(w2, normal_form(w1));
}

///  Backward direction: normal_form(w1) == normal_form(w2) → freely_equivalent(w1, w2).
pub proof fn lemma_normal_form_equiv_backward(w1: Word, w2: Word)
    requires
        normal_form(w1) == normal_form(w2),
    ensures
        freely_equivalent(w1, w2),
{
    //  Both w1 and w2 reduce to normal_form(w1) == normal_form(w2)
    lemma_reduces_to_normal_form(w1);
    lemma_reduces_to_normal_form(w2);
    let nf = normal_form(w1);
    assert(reduces_to(w1, nf) && reduces_to(w2, nf));
}

} //  verus!


//  ================================================================
//  FILE: presentation.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;

verus! {

///  A group presentation ⟨S | R⟩.
///
///  - `num_generators`: the generators are Gen(0), ..., Gen(num_generators - 1)
///  - `relators`: words that are set equal to the identity
///
///  The presented group is the quotient of the free group on S by the normal
///  closure of R.
pub struct Presentation {
    pub num_generators: nat,
    pub relators: Seq<Word>,
}

///  All symbols in a relator use valid generators.
#[verifier::opaque]
pub open spec fn presentation_valid(p: Presentation) -> bool {
    forall|i: int| #![trigger p.relators[i]]
        0 <= i < p.relators.len() ==> word_valid(p.relators[i], p.num_generators)
}

///  An elementary derivation step in a presented group.
pub enum DerivationStep {
    ///  Free reduction: remove an inverse pair at position i.
    FreeReduce { position: int },
    ///  Free expansion: insert an inverse pair at position i.
    FreeExpand { position: int, symbol: Symbol },
    ///  Relator insertion: insert relator r (or its inverse) at position i,
    ///  possibly conjugated by prefix of the word.
    RelatorInsert { position: int, relator_index: nat, inverted: bool },
    ///  Relator deletion: delete a copy of relator r at position i.
    RelatorDelete { position: int, relator_index: nat, inverted: bool },
}

///  Get the relator word, possibly inverted.
pub open spec fn get_relator(p: Presentation, idx: nat, inverted: bool) -> Word {
    if inverted {
        inverse_word(p.relators[idx as int])
    } else {
        p.relators[idx as int]
    }
}

///  Apply a derivation step to a word, producing the result.
///  Returns None if the step is invalid.
pub open spec fn apply_step(p: Presentation, w: Word, step: DerivationStep) -> Option<Word> {
    match step {
        DerivationStep::FreeReduce { position } => {
            if has_cancellation_at(w, position) {
                Some(reduce_at(w, position))
            } else {
                None
            }
        },
        DerivationStep::FreeExpand { position, symbol } => {
            if 0 <= position <= w.len() && symbol_valid(symbol, p.num_generators) {
                let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
                Some(w.subrange(0, position) + pair + w.subrange(position, w.len() as int))
            } else {
                None
            }
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            if 0 <= position <= w.len() && 0 <= relator_index < p.relators.len() {
                let r = get_relator(p, relator_index, inverted);
                Some(w.subrange(0, position) + r + w.subrange(position, w.len() as int))
            } else {
                None
            }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            if 0 <= relator_index < p.relators.len() {
                let r = get_relator(p, relator_index, inverted);
                let rlen = r.len();
                if 0 <= position && position + rlen <= w.len()
                    && w.subrange(position, position + rlen as int) == r
                {
                    Some(w.subrange(0, position) + w.subrange(position + rlen as int, w.len() as int))
                } else {
                    None
                }
            } else {
                None
            }
        },
    }
}

///  A derivation is a sequence of steps transforming w1 into w2.
pub struct Derivation {
    pub steps: Seq<DerivationStep>,
}

///  Check that a derivation is valid: each step successfully produces the next word.
pub open spec fn derivation_valid(p: Presentation, d: Derivation, start: Word, end: Word) -> bool {
    derivation_produces(p, d.steps, start) == Some(end)
}

///  Apply a sequence of steps starting from a word.
pub open spec fn derivation_produces(p: Presentation, steps: Seq<DerivationStep>, start: Word) -> Option<Word>
    decreases steps.len(),
{
    if steps.len() == 0 {
        Some(start)
    } else {
        match apply_step(p, start, steps.first()) {
            Some(next) => derivation_produces(p, steps.drop_first(), next),
            None => None,
        }
    }
}

///  Two words are equivalent in the presented group: there exists a valid derivation.
pub open spec fn equiv_in_presentation(p: Presentation, w1: Word, w2: Word) -> bool {
    exists|d: Derivation| derivation_valid(p, d, w1, w2)
}

///  The empty derivation witnesses reflexivity.
pub proof fn lemma_equiv_refl(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, w, w),
{
    let d = Derivation { steps: Seq::empty() };
    assert(derivation_produces(p, d.steps, w) == Some(w));
    assert(derivation_valid(p, d, w, w));
}

///  Concatenating derivations witnesses transitivity.
pub proof fn lemma_derivation_concat(
    p: Presentation,
    steps1: Seq<DerivationStep>,
    steps2: Seq<DerivationStep>,
    w1: Word,
    w2: Word,
    w3: Word,
)
    requires
        derivation_produces(p, steps1, w1) == Some(w2),
        derivation_produces(p, steps2, w2) == Some(w3),
    ensures
        derivation_produces(p, steps1 + steps2, w1) == Some(w3),
    decreases steps1.len(),
{
    if steps1.len() == 0 {
        assert(steps1 + steps2 =~= steps2);
    } else {
        let next = apply_step(p, w1, steps1.first()).unwrap();
        lemma_derivation_concat(p, steps1.drop_first(), steps2, next, w2, w3);
        assert((steps1 + steps2).first() == steps1.first());
        assert((steps1 + steps2).drop_first() =~= steps1.drop_first() + steps2);
    }
}

///  Transitivity of equivalence.
pub proof fn lemma_equiv_transitive(p: Presentation, w1: Word, w2: Word, w3: Word)
    requires
        equiv_in_presentation(p, w1, w2),
        equiv_in_presentation(p, w2, w3),
    ensures
        equiv_in_presentation(p, w1, w3),
{
    let d1 = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    let d2 = choose|d: Derivation| derivation_valid(p, d, w2, w3);
    lemma_derivation_concat(p, d1.steps, d2.steps, w1, w2, w3);
    let d3 = Derivation { steps: d1.steps + d2.steps };
    assert(derivation_valid(p, d3, w1, w3));
}

///  Invert a single derivation step given the source word.
///  FreeReduce needs the symbol from the source word to construct FreeExpand.
pub open spec fn invert_step_with_context(step: DerivationStep, w: Word) -> DerivationStep {
    match step {
        DerivationStep::FreeReduce { position } =>
            DerivationStep::FreeExpand { position, symbol: w[position] },
        DerivationStep::FreeExpand { position, symbol } =>
            DerivationStep::FreeReduce { position },
        DerivationStep::RelatorInsert { position, relator_index, inverted } =>
            DerivationStep::RelatorDelete { position, relator_index, inverted },
        DerivationStep::RelatorDelete { position, relator_index, inverted } =>
            DerivationStep::RelatorInsert { position, relator_index, inverted },
    }
}

///  A single step can be reversed: if apply_step(p, w, step) = Some(w'),
///  then apply_step(p, w', invert_step_with_context(step, w)) = Some(w).
pub proof fn lemma_single_step_reversible(p: Presentation, w: Word, step: DerivationStep, w_prime: Word)
    requires
        apply_step(p, w, step) == Some(w_prime),
        word_valid(w, p.num_generators),
        presentation_valid(p),
    ensures
        apply_step(p, w_prime, invert_step_with_context(step, w)) == Some(w),
{
    match step {
        DerivationStep::FreeReduce { position } => {
            //  w has inverse pair at position, w' = reduce_at(w, position)
            //  Inverse: FreeExpand at position with symbol w[position]
            //  w' expanded at position gives w back
            let s = w[position];
            let inv_s = w[position + 1];
            assert(is_inverse_pair(s, inv_s));
            assert(inv_s == inverse_symbol(s));
            //  s is valid because w is word_valid
            assert(symbol_valid(s, p.num_generators));
            let pair = Seq::new(1, |_i: int| s) + Seq::new(1, |_i: int| inverse_symbol(s));
            //  w' = w[0..position] ++ w[position+2..]
            //  Expanding at position: w'[0..position] ++ pair ++ w'[position..]
            //  = w[0..position] ++ [s, inv_s] ++ w[position+2..] = w
            assert(w_prime.subrange(0, position) =~= w.subrange(0, position));
            assert(w_prime.subrange(position, w_prime.len() as int) =~= w.subrange(position + 2, w.len() as int));
            assert(w_prime.subrange(0, position) + pair + w_prime.subrange(position, w_prime.len() as int) =~= w);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            //  w' = w[0..position] ++ [symbol, inv(symbol)] ++ w[position..]
            //  Inverse: FreeReduce at position
            //  w'[position] = symbol, w'[position+1] = inv(symbol) → inverse pair
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            assert(w_prime =~= w.subrange(0, position) + pair + w.subrange(position, w.len() as int));
            assert(w_prime[position] == symbol);
            assert(w_prime[position + 1] == inverse_symbol(symbol));
            assert(has_cancellation_at(w_prime, position));
            assert(reduce_at(w_prime, position) =~= w);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            //  w' = w[0..position] ++ relator ++ w[position..]
            //  Inverse: RelatorDelete at position
            let r = get_relator(p, relator_index, inverted);
            assert(w_prime =~= w.subrange(0, position) + r + w.subrange(position, w.len() as int));
            assert(w_prime.subrange(position, position + r.len() as int) =~= r);
            assert(w_prime.subrange(0, position) + w_prime.subrange(position + r.len() as int, w_prime.len() as int) =~= w);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            //  w' = w[0..position] ++ w[position+|r|..]
            //  Inverse: RelatorInsert at position
            let r = get_relator(p, relator_index, inverted);
            assert(w.subrange(position, position + r.len() as int) == r);
            assert(w_prime =~= w.subrange(0, position) + w.subrange(position + r.len() as int, w.len() as int));
            assert(w_prime.subrange(0, position) =~= w.subrange(0, position));
            assert(w_prime.subrange(position, w_prime.len() as int) =~= w.subrange(position + r.len() as int, w.len() as int));
            assert(w_prime.subrange(0, position) + r + w_prime.subrange(position, w_prime.len() as int) =~= w);
        },
    }
}

///  Symmetry: if w1 ≡ w2 then w2 ≡ w1.
///  Proof by induction on derivation length, reversing each step.
///  Requires word_valid(w1) + presentation_valid(p) because reversing
///  a FreeReduce produces a FreeExpand that needs symbol_valid.
pub proof fn lemma_equiv_symmetric(p: Presentation, w1: Word, w2: Word)
    requires
        equiv_in_presentation(p, w1, w2),
        word_valid(w1, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, w2, w1),
{
    let d = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    lemma_derivation_reversible(p, d.steps, w1, w2);
}

///  A single derivation step preserves word_valid when presentation_valid.
///  Used in lemma_derivation_reversible to maintain word_valid through induction.
pub proof fn lemma_step_preserves_word_valid_pres(
    p: Presentation, w: Word, step: DerivationStep, w_next: Word,
)
    requires
        apply_step(p, w, step) == Some(w_next),
        presentation_valid(p),
        word_valid(w, p.num_generators),
    ensures
        word_valid(w_next, p.num_generators),
{
    reveal(presentation_valid);
    let n = p.num_generators;
    match step {
        DerivationStep::FreeReduce { position } => {
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else { assert(w_next[k] == w[k + 2]); }
            }
        },
        DerivationStep::FreeExpand { position, symbol } => {
            //  apply_step guard ensures symbol_valid(symbol, n)
            crate::symbol::lemma_inverse_preserves_valid(symbol, n);
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            let pfx = w.subrange(0, position);
            let sfx = w.subrange(position, w.len() as int);
            assert(w_next =~= pfx + pair + sfx);
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else if k == position as int { }
                else if k == position + 1 { assert(w_next[k] == inverse_symbol(symbol)); }
                else { assert(w_next[k] == w[k - 2]); }
            }
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            if inverted { crate::word::lemma_inverse_word_valid(p.relators[relator_index as int], n); }
            assert(word_valid(r, n));
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else if k < position + r.len() { assert(w_next[k] == r[k - position]); }
                else { assert(w_next[k] == w[k - r.len() as int]); }
            }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            assert forall|k: int| 0 <= k < w_next.len()
                implies symbol_valid(w_next[k], n)
            by {
                if k < position { assert(w_next[k] == w[k]); }
                else { assert(w_next[k] == w[k + r.len() as int]); }
            }
        },
    }
}

///  A valid derivation can be reversed.
proof fn lemma_derivation_reversible(p: Presentation, steps: Seq<DerivationStep>, start: Word, end: Word)
    requires
        derivation_produces(p, steps, start) == Some(end),
        word_valid(start, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, end, start),
    decreases steps.len(),
{
    if steps.len() == 0 {
        //  start == end
        lemma_equiv_refl(p, start);
    } else {
        let step = steps.first();
        let next = apply_step(p, start, step).unwrap();
        let rest = steps.drop_first();

        //  Maintain word_valid through the derivation
        lemma_step_preserves_word_valid_pres(p, start, step, next);

        //  rest takes next to end
        lemma_derivation_reversible(p, rest, next, end);
        //  We now know: end ≡ next

        //  We need: next → start (single reverse step)
        lemma_single_step_reversible(p, start, step, next);
        let rev_step = invert_step_with_context(step, start);
        assert(apply_step(p, next, rev_step) == Some(start));
        //  derivation_produces on a single-step sequence:
        //  first apply rev_step to next → Some(start)
        //  then derivation_produces on empty from start → Some(start)
        let rev_steps = Seq::new(1, |_i: int| rev_step);
        assert(rev_steps.first() == rev_step);
        assert(rev_steps.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(p, rev_steps.drop_first(), start) == Some(start));
        let rev_d = Derivation { steps: rev_steps };
        assert(derivation_valid(p, rev_d, next, start));
        //  next ≡ start
        //  end ≡ next ≡ start
        lemma_equiv_transitive(p, end, next, start);
    }
}

} //  verus!


//  ================================================================
//  FILE: presentation_lemmas.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::presentation::*;

verus! {

//  ============================================================
//  Equivalence respects group operations
//  ============================================================

///  A single derivation step on the left part of a concatenation.
///  If apply_step(p, w1, step) = Some(w1'), then applying the same step
///  to concat(w1, w2) gives concat(w1', w2).
proof fn lemma_single_step_concat_left(p: Presentation, w1: Word, w2: Word, step: DerivationStep, w1_prime: Word)
    requires
        apply_step(p, w1, step) == Some(w1_prime),
    ensures
        apply_step(p, concat(w1, w2), step) == Some(concat(w1_prime, w2)),
{
    let cw = concat(w1, w2);
    match step {
        DerivationStep::FreeReduce { position } => {
            //  position is within w1 (has_cancellation_at(w1, position) requires position < w1.len()-1)
            assert(has_cancellation_at(w1, position));
            //  cw[position] == w1[position], cw[position+1] == w1[position+1]
            assert(cw[position] == w1[position]);
            assert(cw[position + 1] == w1[position + 1]);
            assert(has_cancellation_at(cw, position));
            //  reduce_at(cw, position) == reduce_at(w1, position) ++ w2
            assert(reduce_at(cw, position) =~= concat(reduce_at(w1, position), w2));
        },
        DerivationStep::FreeExpand { position, symbol } => {
            //  0 <= position <= w1.len(), so position <= cw.len()
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            assert(cw.subrange(0, position) =~= w1.subrange(0, position));
            assert(cw.subrange(position, cw.len() as int) =~= w1.subrange(position, w1.len() as int) + w2);
            assert(cw.subrange(0, position) + pair + cw.subrange(position, cw.len() as int) =~=
                concat(w1.subrange(0, position) + pair + w1.subrange(position, w1.len() as int), w2));
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            assert(cw.subrange(0, position) =~= w1.subrange(0, position));
            assert(cw.subrange(position, cw.len() as int) =~= w1.subrange(position, w1.len() as int) + w2);
            assert(cw.subrange(0, position) + r + cw.subrange(position, cw.len() as int) =~=
                concat(w1.subrange(0, position) + r + w1.subrange(position, w1.len() as int), w2));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            let rlen = r.len();
            //  The relator is entirely within w1
            assert(w1.subrange(position, position + rlen as int) == r);
            assert(cw.subrange(position, position + rlen as int) =~= r);
            assert(cw.subrange(0, position) + cw.subrange(position + rlen as int, cw.len() as int) =~=
                concat(w1.subrange(0, position) + w1.subrange(position + rlen as int, w1.len() as int), w2));
        },
    }
}

///  If w1 ≡ w1' then w1·w2 ≡ w1'·w2.
pub proof fn lemma_equiv_concat_left(p: Presentation, w1: Word, w1_prime: Word, w2: Word)
    requires
        equiv_in_presentation(p, w1, w1_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1_prime, w2)),
{
    let d = choose|d: Derivation| derivation_valid(p, d, w1, w1_prime);
    lemma_derivation_lift_left(p, d.steps, w1, w1_prime, w2);
}

///  Lift an entire derivation to the left of a concatenation.
proof fn lemma_derivation_lift_left(
    p: Presentation, steps: Seq<DerivationStep>,
    w1: Word, w1_prime: Word, w2: Word,
)
    requires
        derivation_produces(p, steps, w1) == Some(w1_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1_prime, w2)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(w1 == w1_prime);
        lemma_equiv_refl(p, concat(w1, w2));
    } else {
        let step = steps.first();
        let next = apply_step(p, w1, step).unwrap();
        let rest = steps.drop_first();

        //  Lift this single step
        lemma_single_step_concat_left(p, w1, w2, step, next);
        let lifted_step = step;
        assert(apply_step(p, concat(w1, w2), lifted_step) == Some(concat(next, w2)));
        let lifted_d = Derivation { steps: Seq::new(1, |_i: int| lifted_step) };
        assert(lifted_d.steps.first() == lifted_step);
        assert(lifted_d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(p, lifted_d.steps.drop_first(), concat(next, w2)) == Some(concat(next, w2)));
        assert(derivation_valid(p, lifted_d, concat(w1, w2), concat(next, w2)));

        //  Recurse on rest
        lemma_derivation_lift_left(p, rest, next, w1_prime, w2);

        //  Chain: concat(w1, w2) ≡ concat(next, w2) ≡ concat(w1_prime, w2)
        lemma_equiv_transitive(p, concat(w1, w2), concat(next, w2), concat(w1_prime, w2));
    }
}

///  Shift a derivation step's position by an offset (for right-concat lifting).
pub open spec fn shift_step(step: DerivationStep, offset: int) -> DerivationStep {
    match step {
        DerivationStep::FreeReduce { position } =>
            DerivationStep::FreeReduce { position: position + offset },
        DerivationStep::FreeExpand { position, symbol } =>
            DerivationStep::FreeExpand { position: position + offset, symbol },
        DerivationStep::RelatorInsert { position, relator_index, inverted } =>
            DerivationStep::RelatorInsert { position: position + offset, relator_index, inverted },
        DerivationStep::RelatorDelete { position, relator_index, inverted } =>
            DerivationStep::RelatorDelete { position: position + offset, relator_index, inverted },
    }
}

///  A single derivation step on the right part of a concatenation.
proof fn lemma_single_step_concat_right(p: Presentation, w1: Word, w2: Word, step: DerivationStep, w2_prime: Word)
    requires
        apply_step(p, w2, step) == Some(w2_prime),
    ensures
        apply_step(p, concat(w1, w2), shift_step(step, w1.len() as int)) == Some(concat(w1, w2_prime)),
{
    let cw = concat(w1, w2);
    let offset = w1.len() as int;
    match step {
        DerivationStep::FreeReduce { position } => {
            assert(has_cancellation_at(w2, position));
            assert(cw[position + offset] == w2[position]);
            assert(cw[position + offset + 1] == w2[position + 1]);
            assert(has_cancellation_at(cw, position + offset));
            assert(reduce_at(cw, position + offset) =~= concat(w1, reduce_at(w2, position)));
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let pair = Seq::new(1, |_i: int| symbol) + Seq::new(1, |_i: int| inverse_symbol(symbol));
            assert(cw.subrange(0, position + offset) =~= w1 + w2.subrange(0, position));
            assert(cw.subrange(position + offset, cw.len() as int) =~= w2.subrange(position, w2.len() as int));
            assert(cw.subrange(0, position + offset) + pair + cw.subrange(position + offset, cw.len() as int) =~=
                concat(w1, w2.subrange(0, position) + pair + w2.subrange(position, w2.len() as int)));
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            assert(cw.subrange(0, position + offset) =~= w1 + w2.subrange(0, position));
            assert(cw.subrange(position + offset, cw.len() as int) =~= w2.subrange(position, w2.len() as int));
            assert(cw.subrange(0, position + offset) + r + cw.subrange(position + offset, cw.len() as int) =~=
                concat(w1, w2.subrange(0, position) + r + w2.subrange(position, w2.len() as int)));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(p, relator_index, inverted);
            let rlen = r.len();
            assert(w2.subrange(position, position + rlen as int) == r);
            assert(cw.subrange(position + offset, position + offset + rlen as int) =~= r);
            assert(cw.subrange(0, position + offset) + cw.subrange(position + offset + rlen as int, cw.len() as int) =~=
                concat(w1, w2.subrange(0, position) + w2.subrange(position + rlen as int, w2.len() as int)));
        },
    }
}

///  If w2 ≡ w2' then w1·w2 ≡ w1·w2'.
pub proof fn lemma_equiv_concat_right(p: Presentation, w1: Word, w2: Word, w2_prime: Word)
    requires
        equiv_in_presentation(p, w2, w2_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1, w2_prime)),
{
    let d = choose|d: Derivation| derivation_valid(p, d, w2, w2_prime);
    lemma_derivation_lift_right(p, d.steps, w1, w2, w2_prime);
}

///  Lift an entire derivation to the right of a concatenation.
proof fn lemma_derivation_lift_right(
    p: Presentation, steps: Seq<DerivationStep>,
    w1: Word, w2: Word, w2_prime: Word,
)
    requires
        derivation_produces(p, steps, w2) == Some(w2_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1, w2_prime)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(w2 == w2_prime);
        lemma_equiv_refl(p, concat(w1, w2));
    } else {
        let step = steps.first();
        let next = apply_step(p, w2, step).unwrap();
        let rest = steps.drop_first();

        let shifted = shift_step(step, w1.len() as int);
        lemma_single_step_concat_right(p, w1, w2, step, next);
        assert(apply_step(p, concat(w1, w2), shifted) == Some(concat(w1, next)));
        let lifted_d = Derivation { steps: Seq::new(1, |_i: int| shifted) };
        assert(lifted_d.steps.first() == shifted);
        assert(lifted_d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(p, lifted_d.steps.drop_first(), concat(w1, next)) == Some(concat(w1, next)));
        assert(derivation_valid(p, lifted_d, concat(w1, w2), concat(w1, next)));

        lemma_derivation_lift_right(p, rest, w1, next, w2_prime);
        lemma_equiv_transitive(p, concat(w1, w2), concat(w1, next), concat(w1, w2_prime));
    }
}

///  Equivalence respects concatenation on both sides.
pub proof fn lemma_equiv_concat(
    p: Presentation, w1: Word, w1_prime: Word, w2: Word, w2_prime: Word,
)
    requires
        equiv_in_presentation(p, w1, w1_prime),
        equiv_in_presentation(p, w2, w2_prime),
    ensures
        equiv_in_presentation(p, concat(w1, w2), concat(w1_prime, w2_prime)),
{
    lemma_equiv_concat_left(p, w1, w1_prime, w2);
    lemma_equiv_concat_right(p, w1_prime, w2, w2_prime);
    lemma_equiv_transitive(p, concat(w1, w2), concat(w1_prime, w2), concat(w1_prime, w2_prime));
}

//  ============================================================
//  Identity and inverses
//  ============================================================

///  The empty word is the identity: w·ε ≡ w.
pub proof fn lemma_concat_identity_right(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, concat(w, empty_word()), w),
{
    assert(concat(w, empty_word()) =~= w);
    lemma_equiv_refl(p, w);
}

///  ε·w ≡ w.
pub proof fn lemma_concat_identity_left(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, concat(empty_word(), w), w),
{
    assert(concat(empty_word(), w) =~= w);
    lemma_equiv_refl(p, w);
}

///  A single FreeReduce step as a derivation.
proof fn lemma_free_reduce_step(p: Presentation, w: Word, pos: int)
    requires
        has_cancellation_at(w, pos),
    ensures
        equiv_in_presentation(p, w, reduce_at(w, pos)),
{
    let step = DerivationStep::FreeReduce { position: pos };
    let w2 = reduce_at(w, pos);
    let d = Derivation { steps: Seq::new(1, |_i: int| step) };
    assert(d.steps.first() == step);
    assert(d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
    assert(apply_step(p, w, step) == Some(w2));
    assert(derivation_produces(p, d.steps.drop_first(), w2) == Some(w2));
    assert(derivation_valid(p, d, w, w2));
}

///  w · w⁻¹ ≡ ε (right inverse).
///
///  Base: ε · ε⁻¹ = ε ≡ ε
///  Step: w = s · rest, so w⁻¹ = rest⁻¹ · s⁻¹
///    w · w⁻¹ = s · rest · rest⁻¹ · s⁻¹
///    Step 1: rest · rest⁻¹ ≡ ε (IH)
///    Step 2: s · (rest · rest⁻¹) · s⁻¹ ≡ s · ε · s⁻¹ = s · s⁻¹ (by concat lifting)
///    Step 3: s · s⁻¹ ≡ ε (free reduction)
pub proof fn lemma_word_inverse_right(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, concat(w, inverse_word(w)), empty_word()),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(w =~= empty_word());
        lemma_inverse_empty();
        assert(concat(w, inverse_word(w)) =~= empty_word());
        lemma_equiv_refl(p, empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        let s_seq = Seq::new(1, |_i: int| s);
        let s_inv = Seq::new(1, |_i: int| inverse_symbol(s));

        //  Establish key equalities
        assert(w =~= s_seq + rest);
        assert(inverse_word(w) =~= inverse_word(rest) + s_inv);

        //  Name the intermediate words
        let rest_rest_inv = concat(rest, inverse_word(rest));  //  rest · rest⁻¹
        let middle = concat(s_seq, concat(rest_rest_inv, s_inv)); //  s · (rest·rest⁻¹) · s⁻¹
        let s_sinv = concat(s_seq, s_inv); //  s · s⁻¹

        //  ww_inv =~= middle (just reassociation)
        let ww_inv = concat(w, inverse_word(w));
        assert(ww_inv =~= middle);

        //  Step 1: rest · rest⁻¹ ≡ ε (IH)
        lemma_word_inverse_right(p, rest);

        //  Step 2: concat(rest_rest_inv, s_inv) ≡ concat(empty, s_inv)
        lemma_equiv_concat_left(p, rest_rest_inv, empty_word(), s_inv);
        //  → concat(s_seq, concat(rest_rest_inv, s_inv)) ≡ concat(s_seq, concat(empty, s_inv))
        lemma_equiv_concat_right(p, s_seq,
            concat(rest_rest_inv, s_inv),
            concat(empty_word(), s_inv),
        );
        //  middle ≡ concat(s_seq, concat(empty, s_inv))
        //  concat(s_seq, concat(empty, s_inv)) =~= s_sinv
        assert(concat(s_seq, concat(empty_word(), s_inv)) =~= s_sinv);

        //  Step 3: s · s⁻¹ has a cancellation at 0
        assert(has_cancellation_at(s_sinv, 0));
        assert(reduce_at(s_sinv, 0) =~= empty_word());
        lemma_free_reduce_step(p, s_sinv, 0);

        //  Chain: ww_inv ≡ middle ≡ s_sinv ≡ ε
        lemma_equiv_transitive(p, middle, s_sinv, empty_word());
    }
}

///  w⁻¹ · w ≡ ε (left inverse).
pub proof fn lemma_word_inverse_left(p: Presentation, w: Word)
    ensures
        equiv_in_presentation(p, concat(inverse_word(w), w), empty_word()),
    decreases w.len(),
{
    //  inverse_word(w) · w ≡ ε
    //  Use: inverse_word(inverse_word(w)) =~= w
    //  So this is: inverse_word(w) · inverse_word(inverse_word(w)) ≡ ε
    //  Which is the right inverse for inverse_word(w)
    crate::word::lemma_inverse_involution(w);
    lemma_inverse_word_len(w);
    lemma_word_inverse_right(p, inverse_word(w));
    //  inverse_word(w) · inverse_word(inverse_word(w)) ≡ ε
    //  but inverse_word(inverse_word(w)) =~= w
    assert(concat(inverse_word(w), inverse_word(inverse_word(w))) =~= concat(inverse_word(w), w));
}

//  ============================================================
//  Relators
//  ============================================================

///  Each relator is equivalent to the identity.
pub proof fn lemma_relator_is_identity(p: Presentation, i: int)
    requires
        0 <= i < p.relators.len(),
    ensures
        equiv_in_presentation(p, p.relators[i], empty_word()),
{
    let r = p.relators[i];
    let step = DerivationStep::RelatorDelete {
        position: 0,
        relator_index: i as nat,
        inverted: false,
    };
    let rel = get_relator(p, i as nat, false);
    assert(rel == r);
    let rlen = rel.len();

    //  The key check in apply_step: w.subrange(position, position + rlen) == rel
    //  Here w = r, position = 0, so r.subrange(0, rlen) == r
    assert(r.subrange(0, 0 + rlen as int) =~= r);
    //  Result: r.subrange(0, 0) + r.subrange(0 + rlen, r.len()) = empty
    let result = r.subrange(0, 0int) + r.subrange(0 + rlen as int, r.len() as int);
    assert(result =~= empty_word());

    assert(apply_step(p, r, step) == Some(result));

    let d = Derivation { steps: Seq::new(1, |_j: int| step) };
    let steps = d.steps;
    assert(steps.len() == 1);
    assert(steps.first() == step);
    assert(steps.drop_first().len() == 0);
    assert(steps.drop_first() =~= Seq::<DerivationStep>::empty());
    //  Unfold: derivation_produces(p, steps, r)
    //    = match apply_step(p, r, step) { Some(next) => derivation_produces(p, rest, next) }
    //    = match Some(result) { Some(result) => derivation_produces(p, empty, result) }
    //    = Some(result)
    assert(derivation_produces(p, steps.drop_first(), result) == Some(result));
    //  result =~= empty_word(), so result == empty_word() for Seq
    assert(result == empty_word());
    assert(derivation_valid(p, d, r, empty_word()));
}

///  Conjugation: if r is a relator, then w·r·w⁻¹ ≡ ε.
pub proof fn lemma_conjugate_relator_is_identity(p: Presentation, w: Word, i: int)
    requires
        0 <= i < p.relators.len(),
    ensures
        equiv_in_presentation(
            p,
            concat(concat(w, p.relators[i]), inverse_word(w)),
            empty_word(),
        ),
{
    let r = p.relators[i];
    let w_inv = inverse_word(w);
    let wrw_inv = concat(concat(w, r), w_inv);

    //  Step 1: r ≡ ε
    lemma_relator_is_identity(p, i);

    //  Step 2: concat(r, w_inv) ≡ concat(ε, w_inv)
    lemma_equiv_concat_left(p, r, empty_word(), w_inv);

    //  Step 3: w · concat(r, w_inv) ≡ w · concat(ε, w_inv)
    lemma_equiv_concat_right(p, w, concat(r, w_inv), concat(empty_word(), w_inv));

    //  Reassociate: wrw_inv = concat(concat(w, r), w_inv) =~= concat(w, concat(r, w_inv))
    assert(wrw_inv =~= concat(w, concat(r, w_inv)));
    //  and concat(w, concat(ε, w_inv)) =~= concat(w, w_inv)
    assert(concat(w, concat(empty_word(), w_inv)) =~= concat(w, w_inv));

    //  Step 4: w · w⁻¹ ≡ ε
    lemma_word_inverse_right(p, w);

    //  Chain: wrw_inv ≡ concat(w, w_inv) ≡ ε
    lemma_equiv_transitive(p, wrw_inv, concat(w, w_inv), empty_word());
}

//  ============================================================
//  The presented group is indeed a group
//  ============================================================

///  Summary: the quotient Free(S)/⟨⟨R⟩⟩ satisfies the group axioms:
///  - Associativity: (w1·w2)·w3 ≡ w1·(w2·w3)      (follows from Seq concat assoc)
///  - Identity: ε·w ≡ w ≡ w·ε                        (above)
///  - Inverses: w·w⁻¹ ≡ ε ≡ w⁻¹·w                   (above)
///  - Closure: concat and inverse_word are total      (by construction)
///  - Well-defined: equiv respects concat             (above)

///  Associativity is definitional (Seq concatenation is associative).
pub proof fn lemma_group_associative(p: Presentation, w1: Word, w2: Word, w3: Word)
    ensures
        equiv_in_presentation(
            p,
            concat(concat(w1, w2), w3),
            concat(w1, concat(w2, w3)),
        ),
{
    lemma_concat_assoc(w1, w2, w3);
    //  They're extensionally equal, so trivially equivalent
    assert(concat(concat(w1, w2), w3) =~= concat(w1, concat(w2, w3)));
    lemma_equiv_refl(p, concat(w1, concat(w2, w3)));
}

//  ============================================================
//  Quotient Presentations
//  ============================================================

///  A presentation p' extends p: same generators, relators are p's relators plus extras.
pub open spec fn extends_presentation(p: Presentation, p_prime: Presentation) -> bool {
    p_prime.num_generators == p.num_generators
    && p.relators.len() <= p_prime.relators.len()
    && p_prime.relators.subrange(0, p.relators.len() as int) == p.relators
}

///  A single derivation step valid in p is also valid in any extension p'.
pub proof fn lemma_step_valid_in_extension(
    p: Presentation, p_prime: Presentation,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        extends_presentation(p, p_prime),
        apply_step(p, w, step) == Some(w_prime),
    ensures
        apply_step(p_prime, w, step) == Some(w_prime),
{
    match step {
        DerivationStep::FreeReduce { position } => {
            //  FreeReduce doesn't depend on the presentation
        },
        DerivationStep::FreeExpand { position, symbol } => {
            //  FreeExpand doesn't depend on the presentation
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            //  relator_index < p.relators.len() <= p_prime.relators.len()
            //  p_prime.relators[relator_index] == p.relators[relator_index]
            assert(0 <= relator_index < p.relators.len());
            assert(p_prime.relators[relator_index as int] == p.relators[relator_index as int]);
            assert(get_relator(p_prime, relator_index, inverted) == get_relator(p, relator_index, inverted));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < p.relators.len());
            assert(p_prime.relators[relator_index as int] == p.relators[relator_index as int]);
            assert(get_relator(p_prime, relator_index, inverted) == get_relator(p, relator_index, inverted));
        },
    }
}

///  A derivation valid in p is also valid in any extension p'.
pub proof fn lemma_derivation_valid_in_extension(
    p: Presentation, p_prime: Presentation,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        extends_presentation(p, p_prime),
        derivation_produces(p, steps, w1) == Some(w2),
    ensures
        derivation_produces(p_prime, steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let step = steps.first();
        let next = apply_step(p, w1, step).unwrap();
        lemma_step_valid_in_extension(p, p_prime, w1, step, next);
        lemma_derivation_valid_in_extension(p, p_prime, steps.drop_first(), next, w2);
    }
}

///  Adding relators preserves equivalence: if w1 ≡ w2 in p, then w1 ≡ w2 in any extension p'.
pub proof fn lemma_quotient_preserves_equiv(
    p: Presentation, p_prime: Presentation,
    w1: Word, w2: Word,
)
    requires
        extends_presentation(p, p_prime),
        equiv_in_presentation(p, w1, w2),
    ensures
        equiv_in_presentation(p_prime, w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(p, d, w1, w2);
    lemma_derivation_valid_in_extension(p, p_prime, d.steps, w1, w2);
    let d_prime = Derivation { steps: d.steps };
    assert(derivation_valid(p_prime, d_prime, w1, w2));
}

//  ============================================================
//  Relator inclusion (generalization of extends_presentation)
//  ============================================================

///  Every relator of p1 appears somewhere in p2's relators.
pub open spec fn relators_included(p1: Presentation, p2: Presentation) -> bool {
    p1.num_generators == p2.num_generators &&
    forall|i: int| 0 <= i < p1.relators.len() ==>
        exists|j: int| 0 <= j < p2.relators.len() &&
            p2.relators[j] == #[trigger] p1.relators[i]
}

///  Re-index a derivation step from p1 to p2 using relator inclusion.
pub open spec fn reindex_step(p1: Presentation, p2: Presentation, step: DerivationStep) -> DerivationStep {
    match step {
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let j = choose|j: int| 0 <= j < p2.relators.len()
                && p2.relators[j] == p1.relators[relator_index as int];
            DerivationStep::RelatorInsert { position, relator_index: j as nat, inverted }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let j = choose|j: int| 0 <= j < p2.relators.len()
                && p2.relators[j] == p1.relators[relator_index as int];
            DerivationStep::RelatorDelete { position, relator_index: j as nat, inverted }
        },
        _ => step,
    }
}

///  A single derivation step valid in p1 can be replayed in p2
///  when relators are included.
pub proof fn lemma_step_valid_with_inclusion(
    p1: Presentation, p2: Presentation,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        relators_included(p1, p2),
        apply_step(p1, w, step) == Some(w_prime),
    ensures
        apply_step(p2, w, reindex_step(p1, p2, step)) == Some(w_prime),
{
    match step {
        DerivationStep::FreeReduce { position } => {},
        DerivationStep::FreeExpand { position, symbol } => {},
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(0 <= relator_index < p1.relators.len());
            let j = choose|j: int| 0 <= j < p2.relators.len()
                && p2.relators[j] == p1.relators[relator_index as int];
            assert(get_relator(p2, j as nat, inverted)
                == get_relator(p1, relator_index, inverted));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < p1.relators.len());
            let j = choose|j: int| 0 <= j < p2.relators.len()
                && p2.relators[j] == p1.relators[relator_index as int];
            assert(get_relator(p2, j as nat, inverted)
                == get_relator(p1, relator_index, inverted));
        },
    }
}

///  Re-index a sequence of derivation steps.
pub open spec fn reindex_steps(p1: Presentation, p2: Presentation, steps: Seq<DerivationStep>) -> Seq<DerivationStep> {
    Seq::new(steps.len(), |i: int| reindex_step(p1, p2, steps[i]))
}

///  A valid derivation in p1 can be replayed in p2 when relators are included.
pub proof fn lemma_derivation_valid_with_inclusion(
    p1: Presentation, p2: Presentation,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        relators_included(p1, p2),
        derivation_produces(p1, steps, w1) == Some(w2),
    ensures
        derivation_produces(p2, reindex_steps(p1, p2, steps), w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
        assert(reindex_steps(p1, p2, steps) =~= Seq::<DerivationStep>::empty());
    } else {
        let step = steps.first();
        let next = apply_step(p1, w1, step).unwrap();
        lemma_step_valid_with_inclusion(p1, p2, w1, step, next);

        let new_steps = reindex_steps(p1, p2, steps);
        assert(new_steps.first() == reindex_step(p1, p2, step));
        assert(apply_step(p2, w1, new_steps.first()) == Some(next));

        let tail = steps.drop_first();
        lemma_derivation_valid_with_inclusion(p1, p2, tail, next, w2);

        assert(new_steps.drop_first() =~= reindex_steps(p1, p2, tail));
    }
}

///  Equivalence transfers from p1 to p2 when relators are included.
pub proof fn lemma_relator_inclusion_preserves_equiv(
    p1: Presentation, p2: Presentation,
    w1: Word, w2: Word,
)
    requires
        relators_included(p1, p2),
        equiv_in_presentation(p1, w1, w2),
    ensures
        equiv_in_presentation(p2, w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(p1, d, w1, w2);
    lemma_derivation_valid_with_inclusion(p1, p2, d.steps, w1, w2);
    let d2 = Derivation { steps: reindex_steps(p1, p2, d.steps) };
    assert(derivation_valid(p2, d2, w1, w2));
}

//  ============================================================
//  Bridge: free reduction → presentation equivalence
//  ============================================================

///  A single free reduction step implies presentation equivalence.
///  reduce_at(w, i) IS apply_step(p, w, FreeReduce{position: i}).
proof fn lemma_reduces_one_step_equiv(p: Presentation, w1: Word, w2: Word)
    requires
        reduces_one_step(w1, w2),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let i = choose|i: int| has_cancellation_at(w1, i) && w2 == reduce_at(w1, i);
    lemma_free_reduce_step(p, w1, i);
}

///  Multi-step free reduction implies presentation equivalence (induction on n).
proof fn lemma_reduces_in_steps_equiv(p: Presentation, w1: Word, w2: Word, n: nat)
    requires
        reduces_in_steps(w1, w2, n),
    ensures
        equiv_in_presentation(p, w1, w2),
    decreases n,
{
    if n == 0 {
        assert(w1 == w2);
        lemma_equiv_refl(p, w1);
    } else {
        if w1 == w2 {
            lemma_equiv_refl(p, w1);
        } else {
            let w_mid = choose|w_mid: Word|
                reduces_one_step(w1, w_mid) && reduces_in_steps(w_mid, w2, (n - 1) as nat);
            lemma_reduces_one_step_equiv(p, w1, w_mid);
            lemma_reduces_in_steps_equiv(p, w_mid, w2, (n - 1) as nat);
            lemma_equiv_transitive(p, w1, w_mid, w2);
        }
    }
}

///  Free reduction implies presentation equivalence.
pub proof fn lemma_reduces_to_equiv(p: Presentation, w1: Word, w2: Word)
    requires
        reduces_to(w1, w2),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let n = choose|n: nat| reduces_in_steps(w1, w2, n);
    lemma_reduces_in_steps_equiv(p, w1, w2, n);
}

///  Free equivalence implies presentation equivalence.
///  freely_equivalent(w1, w2) means ∃ w. w1 →* w ←* w2.
///  Both directions give equiv_in_presentation, then symmetry + transitivity.
pub proof fn lemma_freely_equivalent_implies_equiv(p: Presentation, w1: Word, w2: Word)
    requires
        freely_equivalent(w1, w2),
        word_valid(w1, p.num_generators),
        word_valid(w2, p.num_generators),
        presentation_valid(p),
    ensures
        equiv_in_presentation(p, w1, w2),
{
    let w = choose|w: Word| reduces_to(w1, w) && reduces_to(w2, w);
    //  w1 →* w  ⟹  w1 ≡ w in presentation
    lemma_reduces_to_equiv(p, w1, w);
    //  w2 →* w  ⟹  w2 ≡ w in presentation
    lemma_reduces_to_equiv(p, w2, w);
    //  w ≡ w2 by symmetry (needs word_valid(w2) + presentation_valid)
    lemma_equiv_symmetric(p, w2, w);
    //  w1 ≡ w ≡ w2 by transitivity... wait, we have w1 ≡ w and w ≡ w2
    //  Hmm, we have equiv(w1, w) and equiv(w, w2) — but for symmetry we need word_valid(w2).
    //  Actually: we have equiv(w2, w). To get equiv(w, w2) we need symmetry on w2.
    //  lemma_equiv_symmetric requires word_valid(w2) which we have.
    lemma_equiv_transitive(p, w1, w, w2);
}

} //  verus!


//  ================================================================
//  FILE: quotient.rs
//  ================================================================

use vstd::prelude::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;

verus! {

///  Add a single relator to a presentation.
pub open spec fn add_relator(p: Presentation, r: Word) -> Presentation {
    Presentation {
        num_generators: p.num_generators,
        relators: p.relators.push(r),
    }
}

///  Add multiple relators to a presentation (recursive).
pub open spec fn add_relators(p: Presentation, rs: Seq<Word>) -> Presentation
    decreases rs.len(),
{
    if rs.len() == 0 {
        p
    } else {
        add_relators(add_relator(p, rs.first()), rs.drop_first())
    }
}

//  --- Lemmas ---

///  Adding a relator extends the presentation.
pub proof fn lemma_add_relator_extends(p: Presentation, r: Word)
    ensures
        extends_presentation(p, add_relator(p, r)),
{
    let p2 = add_relator(p, r);
    assert(p2.num_generators == p.num_generators);
    assert(p2.relators.len() == p.relators.len() + 1);
    assert(p2.relators.subrange(0, p.relators.len() as int) =~= p.relators);
}

///  Extension is transitive.
pub proof fn lemma_extends_transitive(p1: Presentation, p2: Presentation, p3: Presentation)
    requires
        extends_presentation(p1, p2),
        extends_presentation(p2, p3),
    ensures
        extends_presentation(p1, p3),
{
    assert(p3.num_generators == p1.num_generators);
    assert(p1.relators.len() <= p2.relators.len() <= p3.relators.len());
    //  p3.relators[0..p2.len] == p2.relators
    //  p2.relators[0..p1.len] == p1.relators
    //  So p3.relators[0..p1.len] == p1.relators
    assert(p3.relators.subrange(0, p1.relators.len() as int) =~= p1.relators);
}

///  Adding a relator preserves existing equivalences.
pub proof fn lemma_add_relator_preserves_equiv(
    p: Presentation, r: Word, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(p, w1, w2),
    ensures
        equiv_in_presentation(add_relator(p, r), w1, w2),
{
    lemma_add_relator_extends(p, r);
    lemma_quotient_preserves_equiv(p, add_relator(p, r), w1, w2);
}

///  The newly added relator is the identity in the extended presentation.
pub proof fn lemma_added_relator_is_identity(p: Presentation, r: Word)
    ensures
        equiv_in_presentation(add_relator(p, r), r, empty_word()),
{
    let p2 = add_relator(p, r);
    let idx = p.relators.len();
    assert(p2.relators[idx as int] == r);
    lemma_relator_is_identity(p2, idx as int);
}

///  Conjugates of the added relator are also identity.
pub proof fn lemma_normal_closure_contains_conjugates(
    p: Presentation, r: Word, w: Word,
)
    ensures
        equiv_in_presentation(
            add_relator(p, r),
            concat(concat(w, r), inverse_word(w)),
            empty_word(),
        ),
{
    let p2 = add_relator(p, r);
    let idx = p.relators.len();
    assert(p2.relators[idx as int] == r);
    lemma_conjugate_relator_is_identity(p2, w, idx as int);
}

///  Adding multiple relators extends the original presentation.
pub proof fn lemma_add_relators_extends(p: Presentation, rs: Seq<Word>)
    ensures
        extends_presentation(p, add_relators(p, rs)),
    decreases rs.len(),
{
    if rs.len() == 0 {
        assert(p.relators.subrange(0, p.relators.len() as int) =~= p.relators);
    } else {
        let p1 = add_relator(p, rs.first());
        lemma_add_relator_extends(p, rs.first());
        lemma_add_relators_extends(p1, rs.drop_first());
        lemma_extends_transitive(p, p1, add_relators(p1, rs.drop_first()));
    }
}

///  Adding multiple relators preserves existing equivalences.
pub proof fn lemma_add_relators_preserves_equiv(
    p: Presentation, rs: Seq<Word>, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(p, w1, w2),
    ensures
        equiv_in_presentation(add_relators(p, rs), w1, w2),
{
    lemma_add_relators_extends(p, rs);
    lemma_quotient_preserves_equiv(p, add_relators(p, rs), w1, w2);
}

///  Each added relator is the identity in the extended presentation.
pub proof fn lemma_each_added_relator_is_identity(
    p: Presentation, rs: Seq<Word>, i: int,
)
    requires
        0 <= i < rs.len(),
    ensures
        equiv_in_presentation(add_relators(p, rs), rs[i], empty_word()),
    decreases rs.len(),
{
    if rs.len() == 0 {
        //  impossible
    } else {
        let p1 = add_relator(p, rs.first());
        if i == 0 {
            //  rs[0] = rs.first() is the identity in p1
            lemma_added_relator_is_identity(p, rs.first());
            //  Lift to add_relators(p1, rs.drop_first())
            lemma_add_relators_extends(p1, rs.drop_first());
            lemma_quotient_preserves_equiv(
                p1,
                add_relators(p1, rs.drop_first()),
                rs.first(),
                empty_word(),
            );
            assert(rs[0] == rs.first());
        } else {
            //  rs[i] == rs.drop_first()[i-1]
            assert(rs[i] == rs.drop_first()[(i - 1) as int]);
            lemma_each_added_relator_is_identity(p1, rs.drop_first(), i - 1);
        }
    }
}

///  Adding relators preserves presentation_valid when all added words are word_valid.
pub proof fn lemma_add_relators_valid(p: Presentation, rs: Seq<Word>)
    requires
        presentation_valid(p),
        forall|i: int| 0 <= i < rs.len() ==> word_valid(rs[i], p.num_generators),
    ensures
        presentation_valid(add_relators(p, rs)),
    decreases rs.len(),
{
    reveal(presentation_valid);
    if rs.len() == 0 {
    } else {
        let p1 = add_relator(p, rs.first());
        assert(presentation_valid(p1)) by {
            assert forall|i: int| 0 <= i < p1.relators.len()
                implies word_valid(p1.relators[i], p1.num_generators)
            by {
                if i < p.relators.len() as int {
                    assert(p1.relators[i] == p.relators[i]);
                } else {
                    assert(p1.relators[i] == rs.first());
                    assert(rs[0] == rs.first());
                }
            }
        }
        assert forall|i: int| 0 <= i < rs.drop_first().len()
            implies word_valid(rs.drop_first()[i], p1.num_generators)
        by {
            assert(rs.drop_first()[i] == rs[i + 1]);
        }
        lemma_add_relators_valid(p1, rs.drop_first());
    }
}

} //  verus!


//  ================================================================
//  FILE: free_product.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::reduction::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;

verus! {

//  ============================================================
//  Free Products of Presented Groups
//  ============================================================

///  Shift a symbol's generator index by an offset.
///  Gen(i) → Gen(i + offset), Inv(i) → Inv(i + offset).
pub open spec fn shift_symbol(s: Symbol, offset: nat) -> Symbol {
    match s {
        Symbol::Gen(i) => Symbol::Gen(i + offset),
        Symbol::Inv(i) => Symbol::Inv(i + offset),
    }
}

///  Shift every symbol in a word by an offset.
pub open spec fn shift_word(w: Word, offset: nat) -> Word {
    Seq::new(w.len(), |i: int| shift_symbol(w[i], offset))
}

///  Shift every word in a sequence of relators.
pub open spec fn shift_relators(relators: Seq<Word>, offset: nat) -> Seq<Word> {
    Seq::new(relators.len(), |i: int| shift_word(relators[i], offset))
}

///  The free product of two presentations.
///  Generators: p1's generators (0..n1-1) and p2's generators (n1..n1+n2-1).
///  Relators: p1's relators followed by p2's relators (shifted).
pub open spec fn free_product(p1: Presentation, p2: Presentation) -> Presentation {
    Presentation {
        num_generators: p1.num_generators + p2.num_generators,
        relators: p1.relators + shift_relators(p2.relators, p1.num_generators),
    }
}

///  A word uses only generators from p1 (indices < p1.num_generators).
pub open spec fn word_in_left(w: Word, p1: Presentation) -> bool {
    forall|i: int| 0 <= i < w.len() ==> generator_index(#[trigger] w[i]) < p1.num_generators
}

///  A word uses only generators from p2 (indices >= p1.num_generators).
pub open spec fn word_in_right(w: Word, p1: Presentation, p2: Presentation) -> bool {
    forall|i: int| 0 <= i < w.len() ==>
        p1.num_generators <= generator_index(#[trigger] w[i])
        && generator_index(w[i]) < p1.num_generators + p2.num_generators
}

//  ============================================================
//  Shift lemmas
//  ============================================================

///  Shifting preserves inverse pair relationships.
pub proof fn lemma_shift_preserves_inverse_pair(s1: Symbol, s2: Symbol, offset: nat)
    ensures
        is_inverse_pair(s1, s2) == is_inverse_pair(shift_symbol(s1, offset), shift_symbol(s2, offset)),
{
}

///  Shifting a word preserves its length.
pub proof fn lemma_shift_word_len(w: Word, offset: nat)
    ensures
        shift_word(w, offset).len() == w.len(),
{
}

///  Shifting preserves cancellations.
pub proof fn lemma_shift_preserves_cancellation(w: Word, offset: nat, i: int)
    requires
        has_cancellation_at(w, i),
    ensures
        has_cancellation_at(shift_word(w, offset), i),
{
    let sw = shift_word(w, offset);
    assert(sw[i] == shift_symbol(w[i], offset));
    assert(sw[i + 1] == shift_symbol(w[i + 1], offset));
    lemma_shift_preserves_inverse_pair(w[i], w[i + 1], offset);
}

///  reduce_at commutes with shifting.
pub proof fn lemma_shift_reduce_at(w: Word, offset: nat, i: int)
    requires
        has_cancellation_at(w, i),
    ensures
        shift_word(reduce_at(w, i), offset) =~= reduce_at(shift_word(w, offset), i),
{
    lemma_shift_preserves_cancellation(w, offset, i);
    lemma_reduce_at_len(w, i);
    lemma_reduce_at_elements(w, i);
    let sw = shift_word(w, offset);
    lemma_reduce_at_len(sw, i);
    lemma_reduce_at_elements(sw, i);
    let lhs = shift_word(reduce_at(w, i), offset);
    let rhs = reduce_at(sw, i);
    assert(lhs.len() == rhs.len());
    assert forall|k: int| 0 <= k < lhs.len() implies #[trigger] lhs[k] == rhs[k] by {
        if k < i {
            assert(lhs[k] == shift_symbol(reduce_at(w, i)[k], offset));
            assert(reduce_at(w, i)[k] == w[k]);
            assert(rhs[k] == sw[k]);
            assert(sw[k] == shift_symbol(w[k], offset));
        } else {
            assert(lhs[k] == shift_symbol(reduce_at(w, i)[k], offset));
            assert(reduce_at(w, i)[k] == w[k + 2]);
            assert(rhs[k] == sw[k + 2]);
            assert(sw[k + 2] == shift_symbol(w[k + 2], offset));
        }
    };
}

///  Shifting distributes over concatenation.
pub proof fn lemma_shift_concat(w1: Word, w2: Word, offset: nat)
    ensures
        shift_word(concat(w1, w2), offset) =~= concat(shift_word(w1, offset), shift_word(w2, offset)),
{
    let lhs = shift_word(concat(w1, w2), offset);
    let rhs = concat(shift_word(w1, offset), shift_word(w2, offset));
    assert(lhs.len() == rhs.len());
    assert forall|k: int| 0 <= k < lhs.len() implies #[trigger] lhs[k] == rhs[k] by {
        if k < w1.len() {
            assert(lhs[k] == shift_symbol(concat(w1, w2)[k], offset));
            assert(concat(w1, w2)[k] == w1[k]);
            assert(rhs[k] == shift_word(w1, offset)[k]);
        } else {
            assert(lhs[k] == shift_symbol(concat(w1, w2)[k], offset));
            assert(concat(w1, w2)[k] == w2[k - w1.len()]);
            assert(rhs[k] == shift_word(w2, offset)[k - w1.len()]);
        }
    };
}

///  Shifting distributes over word inversion.
pub proof fn lemma_shift_inverse_word(w: Word, offset: nat)
    ensures
        shift_word(inverse_word(w), offset) =~= inverse_word(shift_word(w, offset)),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(shift_word(inverse_word(w), offset) =~= Seq::<Symbol>::empty());
        assert(inverse_word(shift_word(w, offset)) =~= Seq::<Symbol>::empty());
    } else {
        let first = w.first();
        let rest = w.drop_first();
        lemma_shift_inverse_word(rest, offset);

        let sw = shift_word(w, offset);
        assert(sw.first() == shift_symbol(first, offset));
        assert(sw.drop_first() =~= shift_word(rest, offset));
        assert(shift_symbol(inverse_symbol(first), offset) == inverse_symbol(shift_symbol(first, offset)));

        lemma_shift_concat(
            inverse_word(rest),
            Seq::new(1, |_i: int| inverse_symbol(first)),
            offset,
        );

        lemma_inverse_word_len(rest);
        assert(shift_word(Seq::new(1, |_i: int| inverse_symbol(first)), offset) =~=
            Seq::new(1, |_i: int| inverse_symbol(shift_symbol(first, offset))));
        assert(shift_word(inverse_word(rest), offset) =~= inverse_word(shift_word(rest, offset)));
    }
}

//  ============================================================
//  Left Embedding
//  ============================================================

///  A derivation step valid in p1 is also valid in free_product(p1, p2).
///  apply_step doesn't check num_generators, only relator indices.
///  p1's relators are at the same indices in fp.
proof fn lemma_step_valid_in_free_product_left(
    p1: Presentation, p2: Presentation,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        apply_step(p1, w, step) == Some(w_prime),
    ensures
        apply_step(free_product(p1, p2), w, step) == Some(w_prime),
{
    let fp = free_product(p1, p2);
    match step {
        DerivationStep::FreeReduce { position } => {
            //  Doesn't use relators
        },
        DerivationStep::FreeExpand { position, symbol } => {
            //  Doesn't use relators
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(0 <= relator_index < p1.relators.len());
            assert(fp.relators[relator_index as int] == p1.relators[relator_index as int]);
            assert(get_relator(fp, relator_index, inverted) == get_relator(p1, relator_index, inverted));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < p1.relators.len());
            assert(fp.relators[relator_index as int] == p1.relators[relator_index as int]);
            assert(get_relator(fp, relator_index, inverted) == get_relator(p1, relator_index, inverted));
        },
    }
}

///  A derivation valid in p1 is also valid in free_product(p1, p2).
proof fn lemma_derivation_valid_in_free_product_left(
    p1: Presentation, p2: Presentation,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        derivation_produces(p1, steps, w1) == Some(w2),
    ensures
        derivation_produces(free_product(p1, p2), steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let step = steps.first();
        let next = apply_step(p1, w1, step).unwrap();
        lemma_step_valid_in_free_product_left(p1, p2, w1, step, next);
        lemma_derivation_valid_in_free_product_left(p1, p2, steps.drop_first(), next, w2);
    }
}

///  Left embedding: equivalence in p1 implies equivalence in free_product(p1, p2).
pub proof fn lemma_left_embeds(p1: Presentation, p2: Presentation, w1: Word, w2: Word)
    requires
        equiv_in_presentation(p1, w1, w2),
    ensures
        equiv_in_presentation(free_product(p1, p2), w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(p1, d, w1, w2);
    lemma_derivation_valid_in_free_product_left(p1, p2, d.steps, w1, w2);
    let d_fp = Derivation { steps: d.steps };
    assert(derivation_valid(free_product(p1, p2), d_fp, w1, w2));
}

//  ============================================================
//  Right Embedding
//  ============================================================

///  Shift a derivation step: shift symbols by offset, shift relator indices by relator_offset.
pub open spec fn shift_derivation_step(step: DerivationStep, offset: nat, relator_offset: nat) -> DerivationStep {
    match step {
        DerivationStep::FreeReduce { position } =>
            DerivationStep::FreeReduce { position },
        DerivationStep::FreeExpand { position, symbol } =>
            DerivationStep::FreeExpand { position, symbol: shift_symbol(symbol, offset) },
        DerivationStep::RelatorInsert { position, relator_index, inverted } =>
            DerivationStep::RelatorInsert { position, relator_index: relator_index + relator_offset, inverted },
        DerivationStep::RelatorDelete { position, relator_index, inverted } =>
            DerivationStep::RelatorDelete { position, relator_index: relator_index + relator_offset, inverted },
    }
}

///  A shifted derivation step on a shifted word produces a shifted result in the free product.
proof fn lemma_shifted_step_valid(
    p1: Presentation, p2: Presentation,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        apply_step(p2, w, step) == Some(w_prime),
    ensures
        apply_step(
            free_product(p1, p2),
            shift_word(w, p1.num_generators),
            shift_derivation_step(step, p1.num_generators, p1.relators.len()),
        ) == Some(shift_word(w_prime, p1.num_generators)),
{
    let fp = free_product(p1, p2);
    let offset = p1.num_generators;
    let roff = p1.relators.len();
    let sw = shift_word(w, offset);
    match step {
        DerivationStep::FreeReduce { position } => {
            assert(has_cancellation_at(w, position));
            lemma_shift_preserves_cancellation(w, offset, position);
            lemma_shift_reduce_at(w, offset, position);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let ss = shift_symbol(symbol, offset);
            let pair_shifted = Seq::new(1, |_i: int| ss) + Seq::new(1, |_i: int| inverse_symbol(ss));
            assert(shift_symbol(inverse_symbol(symbol), offset) == inverse_symbol(shift_symbol(symbol, offset)));
            assert(sw.subrange(0, position) =~= shift_word(w.subrange(0, position), offset));
            assert(sw.subrange(position, sw.len() as int) =~= shift_word(w.subrange(position, w.len() as int), offset));
            assert(sw.subrange(0, position) + pair_shifted + sw.subrange(position, sw.len() as int) =~=
                shift_word(w_prime, offset));
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(p2, relator_index, inverted);
            let shifted_idx = relator_index + roff;
            //  fp.relators[shifted_idx] == shift_word(p2.relators[relator_index], offset)
            assert(fp.relators[shifted_idx as int] == shift_word(p2.relators[relator_index as int], offset));
            let r_fp = get_relator(fp, shifted_idx, inverted);
            if inverted {
                lemma_shift_inverse_word(p2.relators[relator_index as int], offset);
            }
            assert(r_fp =~= shift_word(r, offset));

            assert(sw.subrange(0, position) =~= shift_word(w.subrange(0, position), offset));
            assert(sw.subrange(position, sw.len() as int) =~= shift_word(w.subrange(position, w.len() as int), offset));
            assert(sw.subrange(0, position) + r_fp + sw.subrange(position, sw.len() as int) =~=
                shift_word(w_prime, offset));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(p2, relator_index, inverted);
            let rlen = r.len();
            let shifted_idx = relator_index + roff;
            assert(fp.relators[shifted_idx as int] == shift_word(p2.relators[relator_index as int], offset));
            let r_fp = get_relator(fp, shifted_idx, inverted);
            if inverted {
                lemma_shift_inverse_word(p2.relators[relator_index as int], offset);
            }
            assert(r_fp =~= shift_word(r, offset));

            lemma_shift_word_len(r, offset);
            assert(r_fp.len() == rlen);

            assert(sw.subrange(position, position + rlen as int) =~= shift_word(r, offset));
            assert(sw.subrange(position, position + r_fp.len() as int) == r_fp);
            assert(sw.subrange(0, position) + sw.subrange(position + r_fp.len() as int, sw.len() as int) =~=
                shift_word(w_prime, offset));
        },
    }
}

///  A shifted derivation valid in fp.
proof fn lemma_shifted_derivation_valid(
    p1: Presentation, p2: Presentation,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        derivation_produces(p2, steps, w1) == Some(w2),
    ensures
        equiv_in_presentation(
            free_product(p1, p2),
            shift_word(w1, p1.num_generators),
            shift_word(w2, p1.num_generators),
        ),
    decreases steps.len(),
{
    let fp = free_product(p1, p2);
    let offset = p1.num_generators;
    if steps.len() == 0 {
        assert(w1 == w2);
        lemma_equiv_refl(fp, shift_word(w1, offset));
    } else {
        let step = steps.first();
        let next = apply_step(p2, w1, step).unwrap();
        let rest = steps.drop_first();

        let shifted_step = shift_derivation_step(step, offset, p1.relators.len());
        lemma_shifted_step_valid(p1, p2, w1, step, next);

        //  Single-step derivation in fp
        let d = Derivation { steps: Seq::new(1, |_i: int| shifted_step) };
        assert(d.steps.first() == shifted_step);
        assert(d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
        assert(derivation_produces(fp, d.steps.drop_first(), shift_word(next, offset)) == Some(shift_word(next, offset)));
        assert(derivation_valid(fp, d, shift_word(w1, offset), shift_word(next, offset)));

        //  Recurse
        lemma_shifted_derivation_valid(p1, p2, rest, next, w2);

        //  Chain
        lemma_equiv_transitive(fp, shift_word(w1, offset), shift_word(next, offset), shift_word(w2, offset));
    }
}

///  Right embedding: equivalence in p2 implies equivalence of shifted words in free_product(p1, p2).
pub proof fn lemma_right_embeds(p1: Presentation, p2: Presentation, w1: Word, w2: Word)
    requires
        equiv_in_presentation(p2, w1, w2),
    ensures
        equiv_in_presentation(
            free_product(p1, p2),
            shift_word(w1, p1.num_generators),
            shift_word(w2, p1.num_generators),
        ),
{
    let d = choose|d: Derivation| derivation_valid(p2, d, w1, w2);
    lemma_shifted_derivation_valid(p1, p2, d.steps, w1, w2);
}

} //  verus!


//  ================================================================
//  FILE: amalgamated_free_product.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::free_product::*;
use crate::quotient::*;

verus! {

//  ============================================================
//  Amalgamated Free Products
//  ============================================================
//
//  Given two presentations G₁ = ⟨S₁ | R₁⟩ and G₂ = ⟨S₂ | R₂⟩,
//  and identification pairs (u_i, v_i) where u_i is a word in G₁
//  and v_i is a word in G₂, the amalgamated free product is:
//
//    G₁ *_A G₂ = ⟨S₁ ∪ S₂ | R₁ ∪ R₂ ∪ { u_i · shift(v_i)⁻¹ }⟩
//
//  This identifies the subgroup generated by the u_i in G₁ with
//  the subgroup generated by the v_i in G₂.

///  Data for an amalgamated free product.
///
///  - `p1`, `p2`: the two presentations being amalgamated
///  - `identifications`: pairs (u_i, v_i) where u_i is a word in G₁,
///    v_i is a word in G₂. These are identified in the amalgamation.
pub struct AmalgamatedData {
    pub p1: Presentation,
    pub p2: Presentation,
    pub identifications: Seq<(Word, Word)>,
}

///  The amalgamation data is valid:
///  - Both presentations are valid
///  - Each u_i is word_valid for p1
///  - Each v_i is word_valid for p2
pub open spec fn amalgamated_data_valid(data: AmalgamatedData) -> bool {
    presentation_valid(data.p1)
    && presentation_valid(data.p2)
    && forall|i: int| 0 <= i < data.identifications.len() ==>
        word_valid(data.identifications[i].0, data.p1.num_generators)
        && word_valid(data.identifications[i].1, data.p2.num_generators)
}

///  Build the i-th identification relator: u_i · shift(v_i)⁻¹.
///
///  In the free product, p2's generators are shifted by p1.num_generators.
///  So we form the word u_i · inverse(shift(v_i, p1.num_generators)).
pub open spec fn amalgamation_relator(data: AmalgamatedData, i: int) -> Word
    recommends
        0 <= i < data.identifications.len(),
{
    let (u_i, v_i) = data.identifications[i];
    let shifted_v = shift_word(v_i, data.p1.num_generators);
    concat(u_i, inverse_word(shifted_v))
}

///  Build all identification relators.
pub open spec fn amalgamation_relators(data: AmalgamatedData) -> Seq<Word> {
    Seq::new(data.identifications.len(), |i: int| amalgamation_relator(data, i))
}

///  The amalgamated free product: free_product(p1, p2) with identification relators added.
pub open spec fn amalgamated_free_product(data: AmalgamatedData) -> Presentation {
    add_relators(free_product(data.p1, data.p2), amalgamation_relators(data))
}

//  ============================================================
//  Helper: add_relators preserves num_generators
//  ============================================================

///  Adding relators preserves the number of generators.
pub proof fn lemma_add_relators_num_generators(p: Presentation, rs: Seq<Word>)
    ensures
        add_relators(p, rs).num_generators == p.num_generators,
    decreases rs.len(),
{
    if rs.len() == 0 {
    } else {
        let p1 = add_relator(p, rs.first());
        assert(p1.num_generators == p.num_generators);
        lemma_add_relators_num_generators(p1, rs.drop_first());
    }
}

//  ============================================================
//  Validity
//  ============================================================

///  Shifted word validity: if w is word_valid for p2, then shift_word(w, p1.num_generators)
///  is word_valid for free_product(p1, p2).
proof fn lemma_shift_word_valid(w: Word, p1: Presentation, p2: Presentation)
    requires
        word_valid(w, p2.num_generators),
    ensures
        word_valid(shift_word(w, p1.num_generators), p1.num_generators + p2.num_generators),
{
    let offset = p1.num_generators;
    let n = p1.num_generators + p2.num_generators;
    let sw = shift_word(w, offset);
    assert forall|k: int| 0 <= k < sw.len()
        implies symbol_valid(#[trigger] sw[k], n)
    by {
        assert(sw[k] == shift_symbol(w[k], offset));
        assert(symbol_valid(w[k], p2.num_generators));
        //  shift_symbol maps Gen(i) → Gen(i+offset), Inv(i) → Inv(i+offset)
        //  If i < p2.num_generators, then i+offset < p2.num_generators+offset = n
    }
}

///  Each amalgamation relator is word_valid for the free product.
proof fn lemma_amalgamation_relator_valid(data: AmalgamatedData, i: int)
    requires
        amalgamated_data_valid(data),
        0 <= i < data.identifications.len(),
    ensures
        word_valid(
            amalgamation_relator(data, i),
            free_product(data.p1, data.p2).num_generators,
        ),
{
    let (u_i, v_i) = data.identifications[i];
    let fp = free_product(data.p1, data.p2);
    let n = fp.num_generators;

    //  u_i is word_valid for p1.num_generators < n
    assert(word_valid(u_i, n)) by {
        assert forall|k: int| 0 <= k < u_i.len()
            implies symbol_valid(#[trigger] u_i[k], n)
        by {
            assert(symbol_valid(u_i[k], data.p1.num_generators));
        }
    }

    //  shift(v_i) is word_valid for n
    lemma_shift_word_valid(v_i, data.p1, data.p2);
    let shifted_v = shift_word(v_i, data.p1.num_generators);

    //  inverse(shift(v_i)) is word_valid for n
    lemma_inverse_word_valid(shifted_v, n);

    //  concat is word_valid
    lemma_concat_word_valid(u_i, inverse_word(shifted_v), n);
}

///  The amalgamated free product is a valid presentation.
pub proof fn lemma_amalgamated_valid(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        presentation_valid(amalgamated_free_product(data)),
{
    let fp = free_product(data.p1, data.p2);
    let rels = amalgamation_relators(data);

    //  fp is presentation_valid
    reveal(presentation_valid);
    assert(presentation_valid(fp)) by {
        assert forall|k: int| 0 <= k < fp.relators.len()
            implies word_valid(fp.relators[k], fp.num_generators)
        by {
            if k < data.p1.relators.len() as int {
                assert(fp.relators[k] == data.p1.relators[k]);
                assert(word_valid(data.p1.relators[k], data.p1.num_generators));
                assert forall|m: int| 0 <= m < fp.relators[k].len()
                    implies symbol_valid(fp.relators[k][m], fp.num_generators)
                by {
                    assert(symbol_valid(fp.relators[k][m], data.p1.num_generators));
                }
            } else {
                let j = k - data.p1.relators.len() as int;
                assert(fp.relators[k] == shift_word(data.p2.relators[j], data.p1.num_generators));
                let w = data.p2.relators[j];
                assert(word_valid(w, data.p2.num_generators));
                lemma_shift_word_valid(w, data.p1, data.p2);
            }
        }
    }

    //  Each amalgamation relator is word_valid for fp
    assert forall|k: int| 0 <= k < rels.len()
        implies word_valid(rels[k], fp.num_generators)
    by {
        assert(rels[k] == amalgamation_relator(data, k));
        lemma_amalgamation_relator_valid(data, k);
    }

    lemma_add_relators_valid(fp, rels);
}

//  ============================================================
//  Left Embedding
//  ============================================================

///  Left embedding: equivalence in p1 implies equivalence in the amalgamated product.
pub proof fn lemma_left_embeds_in_amalgamation(
    data: AmalgamatedData,
    w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(data.p1, w1, w2),
    ensures
        equiv_in_presentation(amalgamated_free_product(data), w1, w2),
{
    //  p1 words embed in free_product(p1, p2)
    lemma_left_embeds(data.p1, data.p2, w1, w2);
    //  free product embeds in amalgamation (adding relators preserves equiv)
    lemma_add_relators_preserves_equiv(
        free_product(data.p1, data.p2),
        amalgamation_relators(data),
        w1, w2,
    );
}

//  ============================================================
//  Right Embedding
//  ============================================================

///  Right embedding: equivalence in p2 implies equivalence of shifted words
///  in the amalgamated product.
pub proof fn lemma_right_embeds_in_amalgamation(
    data: AmalgamatedData,
    w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(data.p2, w1, w2),
    ensures
        equiv_in_presentation(
            amalgamated_free_product(data),
            shift_word(w1, data.p1.num_generators),
            shift_word(w2, data.p1.num_generators),
        ),
{
    //  p2 words embed in free product via shifting
    lemma_right_embeds(data.p1, data.p2, w1, w2);
    //  free product embeds in amalgamation
    lemma_add_relators_preserves_equiv(
        free_product(data.p1, data.p2),
        amalgamation_relators(data),
        shift_word(w1, data.p1.num_generators),
        shift_word(w2, data.p1.num_generators),
    );
}

//  ============================================================
//  Identification
//  ============================================================

///  The identified words are equivalent in the amalgamated product:
///  u_i ≡ shift(v_i) in the amalgamated free product.
///
///  Proof: u_i · inverse(shift(v_i)) is a relator, so it equals ε.
///  Then u_i ≡ u_i · ε ≡ u_i · (inverse(shift(v_i)) · shift(v_i))
///          ≡ (u_i · inverse(shift(v_i))) · shift(v_i) ≡ ε · shift(v_i) ≡ shift(v_i).
pub proof fn lemma_amalgamation_identifies(data: AmalgamatedData, i: int)
    requires
        amalgamated_data_valid(data),
        0 <= i < data.identifications.len(),
    ensures
        equiv_in_presentation(
            amalgamated_free_product(data),
            data.identifications[i].0,
            shift_word(data.identifications[i].1, data.p1.num_generators),
        ),
{
    let afp = amalgamated_free_product(data);
    let (u_i, v_i) = data.identifications[i];
    let shifted_v = shift_word(v_i, data.p1.num_generators);
    let rel = amalgamation_relator(data, i);
    let rels = amalgamation_relators(data);

    //  rel = concat(u_i, inverse_word(shifted_v))
    assert(rel == concat(u_i, inverse_word(shifted_v)));

    //  rel is the i-th amalgamation relator → it equals ε in afp
    assert(rels[i] == rel);
    lemma_each_added_relator_is_identity(
        free_product(data.p1, data.p2),
        rels,
        i,
    );
    //  rel ≡ ε in afp

    //  Now derive: u_i ≡ shifted_v
    //  Strategy: rel ≡ ε, and rel = u_i · inv(shifted_v)
    //  So u_i · inv(shifted_v) ≡ ε
    //  u_i · inv(shifted_v) · shifted_v ≡ ε · shifted_v ≡ shifted_v
    //  u_i · (inv(shifted_v) · shifted_v) ≡ shifted_v  (by assoc)
    //  u_i · ε ≡ shifted_v  (since inv(w) · w ≡ ε)
    //  u_i ≡ shifted_v

    //  Step 1: rel ≡ ε
    //  (already established above)

    //  Step 2: concat(rel, shifted_v) ≡ concat(ε, shifted_v) ≡ shifted_v
    lemma_equiv_concat_left(afp, rel, empty_word(), shifted_v);
    assert(concat(empty_word(), shifted_v) =~= shifted_v);
    lemma_equiv_refl(afp, shifted_v);
    lemma_equiv_transitive(afp, concat(rel, shifted_v), concat(empty_word(), shifted_v), shifted_v);

    //  Step 3: concat(rel, shifted_v) =~= concat(u_i, concat(inv(shifted_v), shifted_v))
    assert(concat(rel, shifted_v) =~= concat(u_i, concat(inverse_word(shifted_v), shifted_v)));

    //  Step 4: inv(shifted_v) · shifted_v ≡ ε
    lemma_word_inverse_left(afp, shifted_v);

    //  Step 5: u_i · (inv(shifted_v) · shifted_v) ≡ u_i · ε
    lemma_equiv_concat_right(afp, u_i, concat(inverse_word(shifted_v), shifted_v), empty_word());

    //  Step 6: u_i · ε =~= u_i
    assert(concat(u_i, empty_word()) =~= u_i);
    lemma_equiv_refl(afp, u_i);

    //  Step 7: Chain: u_i · (inv(shifted_v) · shifted_v) ≡ u_i · ε ≡ u_i
    lemma_equiv_transitive(
        afp,
        concat(u_i, concat(inverse_word(shifted_v), shifted_v)),
        concat(u_i, empty_word()),
        u_i,
    );

    //  Now we have:
    //    concat(rel, shifted_v) ≡ shifted_v  (from step 2)
    //    concat(u_i, concat(inv(shifted_v), shifted_v)) ≡ u_i  (from step 7)
    //  And these LHS are extensionally equal (step 3).

    //  So: u_i ≡ concat(rel, shifted_v) ≡ shifted_v
    //  Need: u_i ≡ shifted_v

    //  We need symmetry for the chain. Let's use word_valid + presentation_valid.
    lemma_amalgamated_valid(data);
    let fp = free_product(data.p1, data.p2);
    let n = afp.num_generators;

    //  afp.num_generators == fp.num_generators
    lemma_add_relators_num_generators(fp, rels);
    assert(n == fp.num_generators);

    //  word_valid(u_i, n)
    assert(word_valid(u_i, n)) by {
        assert forall|k: int| 0 <= k < u_i.len()
            implies symbol_valid(#[trigger] u_i[k], n)
        by {
            assert(symbol_valid(u_i[k], data.p1.num_generators));
        }
    }

    //  word_valid(shifted_v, n)
    lemma_shift_word_valid(v_i, data.p1, data.p2);
    assert(word_valid(shifted_v, n));

    //  word_valid(inv(shifted_v), n)
    lemma_inverse_word_valid(shifted_v, n);

    //  word_valid(concat(inv(sv), sv), n)
    lemma_concat_word_valid(inverse_word(shifted_v), shifted_v, n);

    //  word_valid(concat(u_i, concat(inv(sv), sv)), n)
    lemma_concat_word_valid(u_i, concat(inverse_word(shifted_v), shifted_v), n);

    //  u_i ≡ concat(u_i, concat(inv(sv), sv)) (symmetric)
    lemma_equiv_symmetric(
        afp,
        concat(u_i, concat(inverse_word(shifted_v), shifted_v)),
        u_i,
    );

    //  Chain: u_i ≡ concat(u_i, concat(inv(sv), sv)) = concat(rel, sv) ≡ shifted_v
    lemma_equiv_transitive(
        afp,
        u_i,
        concat(u_i, concat(inverse_word(shifted_v), shifted_v)),
        shifted_v,
    );
}

//  ============================================================
//  Free product embeds in amalgamation
//  ============================================================

///  The free product embeds in the amalgamated free product:
///  equivalence in free_product(p1, p2) implies equivalence in the amalgamation.
pub proof fn lemma_free_product_embeds_in_amalgamation(
    data: AmalgamatedData,
    w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(free_product(data.p1, data.p2), w1, w2),
    ensures
        equiv_in_presentation(amalgamated_free_product(data), w1, w2),
{
    lemma_add_relators_preserves_equiv(
        free_product(data.p1, data.p2),
        amalgamation_relators(data),
        w1, w2,
    );
}

} //  verus!


//  ================================================================
//  FILE: hnn.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::benign::*;

verus! {

//  ============================================================
//  HNN Extensions
//  ============================================================
//
//  Given a base group G = ⟨S | R⟩ and pairs of associated words (a_i, b_i),
//  the HNN extension is:
//    G*_φ = ⟨S, t | R, t⁻¹·a_i·t·b_i⁻¹ for each i⟩
//
//  The stable letter t is Gen(|S|), the new generator.

///  Data for an HNN extension: base presentation plus association pairs.
pub struct HNNData {
    pub base: Presentation,
    ///  Each pair (a_i, b_i) represents the relation t⁻¹·a_i·t = b_i.
    pub associations: Seq<(Word, Word)>,
}

///  The stable letter symbol: Gen(base.num_generators).
pub open spec fn stable_letter(data: HNNData) -> Symbol {
    Symbol::Gen(data.base.num_generators)
}

///  The inverse of the stable letter.
pub open spec fn stable_letter_inv(data: HNNData) -> Symbol {
    Symbol::Inv(data.base.num_generators)
}

///  Build the i-th HNN relator: t⁻¹ · a_i · t · b_i⁻¹.
pub open spec fn hnn_relator(data: HNNData, i: int) -> Word
    recommends
        0 <= i < data.associations.len(),
{
    let (a_i, b_i) = data.associations[i];
    let t = stable_letter(data);
    let t_inv = stable_letter_inv(data);
    //  t⁻¹ · a_i · t · b_i⁻¹
    Seq::new(1, |_j: int| t_inv) + a_i + Seq::new(1, |_j: int| t) + inverse_word(b_i)
}

///  Build the sequence of all HNN relators.
pub open spec fn hnn_relators(data: HNNData) -> Seq<Word> {
    Seq::new(data.associations.len(), |i: int| hnn_relator(data, i))
}

///  An HNN extension is valid when the base is valid and all association words are word_valid.
pub open spec fn hnn_data_valid(data: HNNData) -> bool {
    presentation_valid(data.base)
    && forall|i: int| 0 <= i < data.associations.len() ==>
        word_valid(data.associations[i].0, data.base.num_generators)
        && word_valid(data.associations[i].1, data.base.num_generators)
}

///  The HNN associations define a valid isomorphism between the subgroups
///  generated by the a_i's and b_i's.
///
///  Formally: for any word w over |associations| generators, substituting
///  a_i for generator i gives identity in G iff substituting b_i for
///  generator i gives identity in G. This ensures the map a_i ↦ b_i
///  extends to a well-defined isomorphism of the generated subgroups.
///
///  This condition is required for Britton's Lemma. Without it, the
///  inclusion G → G* may not be injective. Counterexample: G = ⟨a | ⟩
///  with association (ε, a) satisfies hnn_data_valid but the HNN relator
///  t⁻¹t·a⁻¹ forces a ≡ ε in G* while a ≢ ε in G.
pub open spec fn hnn_associations_isomorphic(data: HNNData) -> bool {
    let k = data.associations.len();
    let a_words = Seq::new(k, |i: int| data.associations[i].0);
    let b_words = Seq::new(k, |i: int| data.associations[i].1);
    forall|w: Word| word_valid(w, k as nat) ==> (
        equiv_in_presentation(data.base, apply_embedding(a_words, w), empty_word())
        <==>
        equiv_in_presentation(data.base, apply_embedding(b_words, w), empty_word())
    )
}

///  The HNN presentation: base generators + t, base relators + HNN relators.
pub open spec fn hnn_presentation(data: HNNData) -> Presentation {
    Presentation {
        num_generators: data.base.num_generators + 1,
        relators: data.base.relators + hnn_relators(data),
    }
}

///  The HNN presentation extends the base presentation
///  (base relators come first, same plus one generator but apply_step ignores num_generators).
proof fn lemma_hnn_extends_base(data: HNNData)
    ensures ({
        let hp = hnn_presentation(data);
        let bp = data.base;
        &&& bp.relators.len() <= hp.relators.len()
        &&& hp.relators.subrange(0, bp.relators.len() as int) == bp.relators
    }),
{
    let hp = hnn_presentation(data);
    let bp = data.base;
    assert(hp.relators.subrange(0, bp.relators.len() as int) =~= bp.relators);
}

///  A derivation step valid in the base is valid in the HNN presentation.
proof fn lemma_step_valid_in_hnn(
    data: HNNData,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        apply_step(data.base, w, step) == Some(w_prime),
    ensures
        apply_step(hnn_presentation(data), w, step) == Some(w_prime),
{
    let hp = hnn_presentation(data);
    let bp = data.base;
    match step {
        DerivationStep::FreeReduce { position } => {},
        DerivationStep::FreeExpand { position, symbol } => {},
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(0 <= relator_index < bp.relators.len());
            assert(hp.relators[relator_index as int] == bp.relators[relator_index as int]);
            assert(get_relator(hp, relator_index, inverted) == get_relator(bp, relator_index, inverted));
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(0 <= relator_index < bp.relators.len());
            assert(hp.relators[relator_index as int] == bp.relators[relator_index as int]);
            assert(get_relator(hp, relator_index, inverted) == get_relator(bp, relator_index, inverted));
        },
    }
}

///  A derivation valid in the base is valid in the HNN presentation.
pub proof fn lemma_derivation_valid_in_hnn(
    data: HNNData,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        derivation_produces(data.base, steps, w1) == Some(w2),
    ensures
        derivation_produces(hnn_presentation(data), steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let step = steps.first();
        let next = apply_step(data.base, w1, step).unwrap();
        lemma_step_valid_in_hnn(data, w1, step, next);
        lemma_derivation_valid_in_hnn(data, steps.drop_first(), next, w2);
    }
}

///  Base group embeds in HNN extension:
///  if w1 ≡ w2 in base, then w1 ≡ w2 in hnn_presentation.
pub proof fn lemma_base_embeds_in_hnn(data: HNNData, w1: Word, w2: Word)
    requires
        equiv_in_presentation(data.base, w1, w2),
    ensures
        equiv_in_presentation(hnn_presentation(data), w1, w2),
{
    let d = choose|d: Derivation| derivation_valid(data.base, d, w1, w2);
    lemma_derivation_valid_in_hnn(data, d.steps, w1, w2);
    let d_hnn = Derivation { steps: d.steps };
    assert(derivation_valid(hnn_presentation(data), d_hnn, w1, w2));
}

///  The HNN conjugation relation: t⁻¹·a_i·t ≡ b_i in the HNN presentation.
///  This is by construction: t⁻¹·a_i·t·b_i⁻¹ is a relator, so it equals ε,
///  hence t⁻¹·a_i·t ≡ b_i.
pub proof fn lemma_hnn_conjugation(data: HNNData, i: int)
    requires
        0 <= i < data.associations.len(),
        hnn_data_valid(data),
    ensures
        equiv_in_presentation(
            hnn_presentation(data),
            Seq::new(1, |_j: int| stable_letter_inv(data))
                + data.associations[i].0
                + Seq::new(1, |_j: int| stable_letter(data)),
            data.associations[i].1,
        ),
{
    reveal(presentation_valid);
    let hp = hnn_presentation(data);
    let bp = data.base;
    let (a_i, b_i) = data.associations[i];
    let t = stable_letter(data);
    let t_inv = stable_letter_inv(data);
    let lhs = Seq::new(1, |_j: int| t_inv) + a_i + Seq::new(1, |_j: int| t);

    let rel_idx = (bp.relators.len() + i) as nat;
    let relator = hnn_relator(data, i);
    assert(hp.relators[rel_idx as int] == relator);

    //  Step 1: relator ≡ ε (delete the relator)
    let step = DerivationStep::RelatorDelete {
        position: 0,
        relator_index: rel_idx,
        inverted: false,
    };
    assert(relator.subrange(0, 0int + relator.len() as int) =~= relator);
    let result = relator.subrange(0, 0int) + relator.subrange(0 + relator.len() as int, relator.len() as int);
    assert(result =~= empty_word());
    assert(apply_step(hp, relator, step) == Some(result));
    let d_del = Derivation { steps: Seq::new(1, |_j: int| step) };
    assert(d_del.steps.first() == step);
    assert(d_del.steps.drop_first() =~= Seq::<DerivationStep>::empty());
    assert(derivation_produces(hp, d_del.steps.drop_first(), result) == Some(result));
    assert(result == empty_word());
    assert(derivation_valid(hp, d_del, relator, empty_word()));
    //  relator ≡ ε

    assert(relator =~= concat(lhs, inverse_word(b_i)));

    //  concat(relator, b_i) ≡ b_i
    lemma_equiv_concat_left(hp, relator, empty_word(), b_i);
    assert(concat(empty_word(), b_i) =~= b_i);
    lemma_equiv_refl(hp, b_i);
    lemma_equiv_transitive(hp, concat(relator, b_i), concat(empty_word(), b_i), b_i);

    assert(concat(relator, b_i) =~= concat(lhs, concat(inverse_word(b_i), b_i)));

    //  inv(b_i) · b_i ≡ ε
    lemma_word_inverse_left(hp, b_i);

    //  lhs · (inv(b_i) · b_i) ≡ lhs · ε ≡ lhs
    lemma_equiv_concat_right(hp, lhs, concat(inverse_word(b_i), b_i), empty_word());
    assert(concat(lhs, empty_word()) =~= lhs);
    lemma_equiv_refl(hp, lhs);
    lemma_equiv_transitive(hp, concat(lhs, concat(inverse_word(b_i), b_i)), concat(lhs, empty_word()), lhs);

    //  Prove presentation_valid(hp) and word_valid for symmetric call
    let n = hp.num_generators;
    assert(n == bp.num_generators + 1);

    //  presentation_valid(hp)
    assert(presentation_valid(hp)) by {
        assert forall|k: int| 0 <= k < hp.relators.len()
            implies word_valid(hp.relators[k], hp.num_generators)
        by {
            if k < bp.relators.len() as int {
                //  base relator: word_valid for bp.num_generators < hp.num_generators
                assert(hp.relators[k] == bp.relators[k]);
                assert(word_valid(bp.relators[k], bp.num_generators));
                assert forall|m: int| 0 <= m < hp.relators[k].len()
                    implies symbol_valid(hp.relators[k][m], n) by {
                    assert(symbol_valid(hp.relators[k][m], bp.num_generators));
                }
            } else {
                //  HNN relator at index bp.relators.len() + j
                let j = k - bp.relators.len() as int;
                let hr = hnn_relator(data, j);
                assert(hp.relators[k] == hr);
                let (aj, bj) = data.associations[j];
                //  hr = t_inv ++ aj ++ t ++ inv(bj)
                //  All symbols valid for n = bp.num_generators + 1
                assert(word_valid(aj, bp.num_generators));
                crate::word::lemma_inverse_word_valid(bj, bp.num_generators);
                assert forall|m: int| 0 <= m < hr.len()
                    implies symbol_valid(hr[m], n) by {
                    //  manual: check each segment of the HNN relator
                    let t_inv_w = Seq::new(1, |_j2: int| t_inv);
                    let t_w = Seq::new(1, |_j2: int| t);
                    let inv_bj = inverse_word(bj);
                    //  hr = t_inv_w + aj + t_w + inv_bj
                    if m < 1 {
                        //  t_inv = Inv(bp.num_generators), valid for n
                        assert(hr[m] == t_inv);
                    } else if m < (1 + aj.len()) as int {
                        assert(hr[m] == aj[(m - 1) as int]);
                        assert(symbol_valid(aj[(m - 1) as int], bp.num_generators));
                    } else if m < (2 + aj.len()) as int {
                        assert(hr[m] == t);
                    } else {
                        let inv_idx = (m - 2 - aj.len()) as int;
                        assert(hr[m] == inv_bj[inv_idx]);
                        assert(symbol_valid(inv_bj[inv_idx], bp.num_generators));
                    }
                }
            }
        }
    }

    //  word_valid for concat(lhs, concat(inv(b_i), b_i))
    assert(word_valid(b_i, n)) by {
        assert(word_valid(b_i, bp.num_generators));
        assert forall|m: int| 0 <= m < b_i.len() implies symbol_valid(b_i[m], n) by {
            assert(symbol_valid(b_i[m], bp.num_generators));
        }
    }
    crate::word::lemma_inverse_word_valid(b_i, n);
    crate::word::lemma_concat_word_valid(inverse_word(b_i), b_i, n);

    assert(word_valid(a_i, n)) by {
        assert(word_valid(a_i, bp.num_generators));
        assert forall|m: int| 0 <= m < a_i.len() implies symbol_valid(a_i[m], n) by {
            assert(symbol_valid(a_i[m], bp.num_generators));
        }
    }
    assert(word_valid(lhs, n)) by {
        assert forall|m: int| 0 <= m < lhs.len() implies symbol_valid(lhs[m], n) by {
            let t_inv_w = Seq::new(1, |_j2: int| t_inv);
            let t_w = Seq::new(1, |_j2: int| t);
            if m < 1 {
                assert(lhs[m] == t_inv);
            } else if m < (1 + a_i.len()) as int {
                assert(lhs[m] == a_i[(m - 1) as int]);
            } else {
                assert(lhs[m] == t);
            }
        }
    }
    crate::word::lemma_concat_word_valid(lhs, concat(inverse_word(b_i), b_i), n);

    //  symmetric: lhs ≡ concat(lhs, concat(inv(b_i), b_i))
    lemma_equiv_symmetric(hp, concat(lhs, concat(inverse_word(b_i), b_i)), lhs);
    //  chain: lhs ≡ concat(relator, b_i) ≡ b_i
    lemma_equiv_transitive(hp, lhs, concat(lhs, concat(inverse_word(b_i), b_i)), b_i);
}

///  The i-th HNN relator has the expected structure: t⁻¹·a_i·t·b_i⁻¹.
pub proof fn lemma_hnn_relator_structure(data: HNNData, i: int)
    requires
        0 <= i < data.associations.len(),
    ensures ({
        let hp = hnn_presentation(data);
        let bp = data.base;
        let rel_idx = bp.relators.len() + i;
        let (a_i, b_i) = data.associations[i];
        let t = stable_letter(data);
        let t_inv = stable_letter_inv(data);
        hp.relators[rel_idx] == Seq::new(1, |_j: int| t_inv) + a_i + Seq::new(1, |_j: int| t) + inverse_word(b_i)
    }),
{
    let hp = hnn_presentation(data);
    let bp = data.base;
    let rel_idx = (bp.relators.len() + i) as int;
    assert(hp.relators[rel_idx] == hnn_relator(data, i));
}

} //  verus!


//  ================================================================
//  FILE: homomorphism.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::reduction::*;

verus! {

///  Data defining a group homomorphism via generator images.
pub struct HomomorphismData {
    pub source: Presentation,
    pub target: Presentation,
    pub generator_images: Seq<Word>,
}

///  Image of a single symbol under the homomorphism.
pub open spec fn apply_hom_symbol(h: HomomorphismData, s: Symbol) -> Word {
    match s {
        Symbol::Gen(i) => h.generator_images[i as int],
        Symbol::Inv(i) => inverse_word(h.generator_images[i as int]),
    }
}

///  Image of a word under the homomorphism.
pub open spec fn apply_hom(h: HomomorphismData, w: Word) -> Word
    decreases w.len(),
{
    if w.len() == 0 {
        empty_word()
    } else {
        concat(apply_hom_symbol(h, w.first()), apply_hom(h, w.drop_first()))
    }
}

///  A homomorphism is valid if images.len() == num_generators,
///  both presentations are valid, generator images are word_valid,
///  and each relator image ≡ ε.
pub open spec fn is_valid_homomorphism(h: HomomorphismData) -> bool {
    h.generator_images.len() == h.source.num_generators
    && presentation_valid(h.source)
    && presentation_valid(h.target)
    && (forall|i: int| 0 <= i < h.generator_images.len() ==>
        word_valid(h.generator_images[i], h.target.num_generators))
    && (forall|i: int| 0 <= i < h.source.relators.len() ==>
        equiv_in_presentation(h.target, apply_hom(h, h.source.relators[i]), empty_word()))
}

///  The identity homomorphism: Gen(i) → [Gen(i)].
pub open spec fn identity_hom(p: Presentation) -> HomomorphismData {
    HomomorphismData {
        source: p,
        target: p,
        generator_images: Seq::new(p.num_generators, |i: int| {
            Seq::new(1, |_j: int| Symbol::Gen(i as nat))
        }),
    }
}

///  Composition of homomorphisms.
pub open spec fn compose_hom(h1: HomomorphismData, h2: HomomorphismData) -> HomomorphismData {
    HomomorphismData {
        source: h1.source,
        target: h2.target,
        generator_images: Seq::new(h1.generator_images.len(), |i: int| {
            apply_hom(h2, h1.generator_images[i])
        }),
    }
}

//  --- Helpers ---

///  apply_hom of a singleton word.
pub proof fn lemma_hom_singleton(h: HomomorphismData, s: Symbol)
    ensures
        apply_hom(h, Seq::new(1, |_i: int| s)) =~= apply_hom_symbol(h, s),
{
    let w = Seq::new(1, |_i: int| s);
    assert(w.len() == 1);
    assert(w.first() == s);
    let tail = w.drop_first();
    assert(tail.len() == 0);
    //  apply_hom(h, w) = concat(apply_hom_symbol(h, s), apply_hom(h, tail))
    //  apply_hom(h, tail) = empty_word() because tail.len() == 0
    assert(apply_hom(h, tail) =~= empty_word());
    //  concat(x, empty) =~= x
    assert(concat(apply_hom_symbol(h, s), empty_word()) =~= apply_hom_symbol(h, s));
}

///  Image of a single symbol is word_valid for target.
proof fn lemma_apply_hom_symbol_word_valid(h: HomomorphismData, s: Symbol)
    requires
        is_valid_homomorphism(h),
        symbol_valid(s, h.source.num_generators),
    ensures
        word_valid(apply_hom_symbol(h, s), h.target.num_generators),
{
    match s {
        Symbol::Gen(i) => {},
        Symbol::Inv(i) => {
            crate::word::lemma_inverse_word_valid(
                h.generator_images[i as int], h.target.num_generators);
        },
    }
}

///  Image of a word under a valid homomorphism is word_valid for target.
pub proof fn lemma_apply_hom_word_valid(h: HomomorphismData, w: Word)
    requires
        is_valid_homomorphism(h),
        word_valid(w, h.source.num_generators),
    ensures
        word_valid(apply_hom(h, w), h.target.num_generators),
    decreases w.len(),
{
    if w.len() > 0 {
        let s = w.first();
        let rest = w.drop_first();
        assert(word_valid(rest, h.source.num_generators)) by {
            assert forall|i: int| 0 <= i < rest.len()
                implies symbol_valid(rest[i], h.source.num_generators)
            by { assert(rest[i] == w[i + 1]); }
        }
        lemma_apply_hom_symbol_word_valid(h, s);
        lemma_apply_hom_word_valid(h, rest);
        crate::word::lemma_concat_word_valid(
            apply_hom_symbol(h, s), apply_hom(h, rest), h.target.num_generators);
    }
}

///  concat(x, suffix) ≡ suffix when x ≡ ε.
pub proof fn lemma_identity_prefix_equiv(p: Presentation, x: Word, suffix: Word)
    requires
        equiv_in_presentation(p, x, empty_word()),
    ensures
        equiv_in_presentation(p, concat(x, suffix), suffix),
{
    lemma_equiv_concat_left(p, x, empty_word(), suffix);
    assert(concat(empty_word(), suffix) =~= suffix);
    lemma_equiv_refl(p, suffix);
    lemma_equiv_transitive(p, concat(x, suffix), concat(empty_word(), suffix), suffix);
}

///  hom(r) ≡ ε for an inverted relator.
proof fn lemma_inverted_relator_image_is_identity(h: HomomorphismData, relator_index: nat)
    requires
        is_valid_homomorphism(h),
        0 <= relator_index < h.source.relators.len(),
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, inverse_word(h.source.relators[relator_index as int])),
            empty_word(),
        ),
{
    reveal(presentation_valid);
    let orig_r = h.source.relators[relator_index as int];
    let hom_orig = apply_hom(h, orig_r);

    //  word_valid facts for lemma_equiv_symmetric calls
    assert(word_valid(orig_r, h.source.num_generators));
    lemma_apply_hom_word_valid(h, orig_r);
    let n = h.target.num_generators;
    crate::word::lemma_inverse_word_valid(hom_orig, n);
    crate::word::lemma_concat_word_valid(inverse_word(hom_orig), hom_orig, n);

    lemma_hom_respects_inverse(h, orig_r);

    lemma_word_inverse_left(h.target, hom_orig);
    lemma_equiv_symmetric(h.target, hom_orig, empty_word());
    lemma_equiv_concat_right(h.target, inverse_word(hom_orig), hom_orig, empty_word());
    assert(concat(inverse_word(hom_orig), empty_word()) =~= inverse_word(hom_orig));

    crate::word::lemma_concat_word_valid(inverse_word(hom_orig), empty_word(), n);
    lemma_equiv_symmetric(h.target,
        concat(inverse_word(hom_orig), hom_orig),
        concat(inverse_word(hom_orig), empty_word()),
    );
    lemma_equiv_transitive(h.target,
        inverse_word(hom_orig),
        concat(inverse_word(hom_orig), hom_orig),
        empty_word(),
    );

    assert(apply_hom(h, inverse_word(orig_r)) =~= inverse_word(hom_orig));
}

///  hom_r ≡ ε for either direct or inverted relator.
proof fn lemma_relator_image_is_identity(h: HomomorphismData, relator_index: nat, inverted: bool)
    requires
        is_valid_homomorphism(h),
        0 <= relator_index < h.source.relators.len(),
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, get_relator(h.source, relator_index, inverted)),
            empty_word(),
        ),
{
    if inverted {
        lemma_inverted_relator_image_is_identity(h, relator_index);
    }
}

//  --- Main Lemmas ---

///  Homomorphism of empty word is empty.
pub proof fn lemma_hom_empty(h: HomomorphismData)
    ensures
        apply_hom(h, empty_word()) =~= empty_word(),
{
}

///  Homomorphism respects concatenation.
pub proof fn lemma_hom_respects_concat(h: HomomorphismData, w1: Word, w2: Word)
    ensures
        apply_hom(h, concat(w1, w2)) =~= concat(apply_hom(h, w1), apply_hom(h, w2)),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
        assert(apply_hom(h, w1) =~= empty_word());
    } else {
        let s = w1.first();
        let rest = w1.drop_first();
        assert(concat(w1, w2).first() == s);
        assert(concat(w1, w2).drop_first() =~= concat(rest, w2));
        lemma_hom_respects_concat(h, rest, w2);
        lemma_concat_assoc(apply_hom_symbol(h, s), apply_hom(h, rest), apply_hom(h, w2));
    }
}

///  Homomorphism respects word inverse.
pub proof fn lemma_hom_respects_inverse(h: HomomorphismData, w: Word)
    ensures
        apply_hom(h, inverse_word(w)) =~= inverse_word(apply_hom(h, w)),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();

        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        assert(inverse_word(w) =~= concat(inverse_word(rest), inv_s_word));
        lemma_hom_respects_concat(h, inverse_word(rest), inv_s_word);
        lemma_hom_respects_inverse(h, rest);
        lemma_hom_singleton(h, inverse_symbol(s));

        match s {
            Symbol::Gen(_idx) => {},
            Symbol::Inv(idx) => {
                crate::word::lemma_inverse_involution(h.generator_images[idx as int]);
            },
        }

        lemma_inverse_concat(apply_hom_symbol(h, s), apply_hom(h, rest));
    }
}

///  Homomorphism preserves a single derivation step.
pub proof fn lemma_hom_preserves_single_step(
    h: HomomorphismData,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        is_valid_homomorphism(h),
        apply_step(h.source, w, step) == Some(w_prime),
    ensures
        equiv_in_presentation(h.target, apply_hom(h, w), apply_hom(h, w_prime)),
{
    match step {
        DerivationStep::FreeReduce { position } => {
            lemma_hom_preserves_free_reduce(h, w, position);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            lemma_hom_preserves_free_expand(h, w, position, symbol);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            lemma_hom_preserves_relator_insert(h, w, position, relator_index, inverted);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            lemma_hom_preserves_relator_delete(h, w, position, relator_index, inverted);
        },
    }
}

///  Helper: hom preserves FreeReduce step.
proof fn lemma_hom_preserves_free_reduce(
    h: HomomorphismData, w: Word, position: int,
)
    requires
        is_valid_homomorphism(h),
        has_cancellation_at(w, position),
    ensures
        equiv_in_presentation(h.target, apply_hom(h, w), apply_hom(h, reduce_at(w, position))),
{
    let s1 = w[position];
    let s2 = w[position + 1];

    let prefix = w.subrange(0, position);
    let s1_word = Seq::new(1, |_i: int| s1);
    let s2_word = Seq::new(1, |_i: int| s2);
    let pair = s1_word + s2_word;
    let suffix = w.subrange(position + 2, w.len() as int);
    assert(w =~= (prefix + pair) + suffix);

    let reduced = reduce_at(w, position);
    assert(reduced =~= prefix + suffix);

    //  Decompose w = (prefix + pair) + suffix
    lemma_hom_respects_concat(h, prefix + pair, suffix);
    lemma_hom_respects_concat(h, prefix, pair);
    lemma_hom_respects_concat(h, s1_word, s2_word);
    lemma_hom_respects_concat(h, prefix, suffix);

    lemma_hom_singleton(h, s1);
    lemma_hom_singleton(h, s2);

    let img_s1 = apply_hom_symbol(h, s1);
    let img_s2 = apply_hom_symbol(h, s2);

    //  img_s2 = inverse_word(img_s1)
    match s1 {
        Symbol::Gen(_idx) => {},
        Symbol::Inv(idx) => {
            crate::word::lemma_inverse_involution(h.generator_images[idx as int]);
        },
    }

    lemma_word_inverse_right(h.target, img_s1);

    let hom_prefix = apply_hom(h, prefix);
    let hom_suffix = apply_hom(h, suffix);
    let pair_img = concat(img_s1, img_s2);

    //  apply_hom(w) =~= concat(concat(hom_prefix, pair_img), hom_suffix)
    //  We need: concat(concat(hom_prefix, pair_img), hom_suffix)
    //        =~= concat(hom_prefix, concat(pair_img, hom_suffix))
    lemma_concat_assoc(hom_prefix, pair_img, hom_suffix);

    //  pair_img ≡ ε → concat(pair_img, hom_suffix) ≡ hom_suffix
    lemma_identity_prefix_equiv(h.target, pair_img, hom_suffix);
    //  concat(hom_prefix, concat(pair_img, hom_suffix)) ≡ concat(hom_prefix, hom_suffix)
    lemma_equiv_concat_right(h.target, hom_prefix, concat(pair_img, hom_suffix), hom_suffix);
}

///  Helper: hom preserves FreeExpand step.
proof fn lemma_hom_preserves_free_expand(
    h: HomomorphismData, w: Word, position: int, symbol: Symbol,
)
    requires
        is_valid_homomorphism(h),
        0 <= position <= w.len(),
        symbol_valid(symbol, h.source.num_generators),
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, w),
            apply_hom(h, apply_step(h.source, w, DerivationStep::FreeExpand { position, symbol }).unwrap()),
        ),
{
    let s_word = Seq::new(1, |_i: int| symbol);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(symbol));
    let pair = s_word + inv_s_word;
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position, w.len() as int);
    let w_prime = (prefix + pair) + suffix;
    assert(w =~= prefix + suffix);

    lemma_hom_respects_concat(h, prefix, suffix);
    lemma_hom_respects_concat(h, prefix + pair, suffix);
    lemma_hom_respects_concat(h, prefix, pair);
    lemma_hom_respects_concat(h, s_word, inv_s_word);

    lemma_hom_singleton(h, symbol);
    lemma_hom_singleton(h, inverse_symbol(symbol));

    let img_s = apply_hom_symbol(h, symbol);
    let img_inv_s = apply_hom_symbol(h, inverse_symbol(symbol));

    match symbol {
        Symbol::Gen(_idx) => {},
        Symbol::Inv(idx) => {
            crate::word::lemma_inverse_involution(h.generator_images[idx as int]);
        },
    }

    lemma_word_inverse_right(h.target, img_s);

    let hom_prefix = apply_hom(h, prefix);
    let hom_suffix = apply_hom(h, suffix);
    let pair_img = concat(img_s, img_inv_s);

    //  apply_hom(w_prime) =~= concat(concat(hom_prefix, pair_img), hom_suffix)
    //                     =~= concat(hom_prefix, concat(pair_img, hom_suffix))
    lemma_concat_assoc(hom_prefix, pair_img, hom_suffix);

    //  pair_img ≡ ε
    //  symmetric: ε ≡ pair_img (need word_valid(pair_img) — provable from symbol_valid)
    lemma_apply_hom_symbol_word_valid(h, symbol);
    crate::symbol::lemma_inverse_preserves_valid(symbol, h.source.num_generators);
    lemma_apply_hom_symbol_word_valid(h, inverse_symbol(symbol));
    crate::word::lemma_concat_word_valid(img_s, img_inv_s, h.target.num_generators);
    lemma_equiv_symmetric(h.target, pair_img, empty_word());

    //  ε ≡ pair_img → concat(ε, hom_suffix) ≡ concat(pair_img, hom_suffix)
    lemma_equiv_concat_left(h.target, empty_word(), pair_img, hom_suffix);
    //  concat(ε, hom_suffix) =~= hom_suffix
    //  concat(hom_prefix, concat(ε, hom_suffix)) ≡ concat(hom_prefix, concat(pair_img, hom_suffix))
    lemma_equiv_concat_right(h.target, hom_prefix,
        concat(empty_word(), hom_suffix), concat(pair_img, hom_suffix));

    //  apply_hom(w) =~= concat(hom_prefix, hom_suffix) =~= concat(hom_prefix, concat(ε, hom_suffix))
    //  apply_hom(w_prime) =~= concat(hom_prefix, concat(pair_img, hom_suffix))
}

///  Helper: hom preserves RelatorInsert step.
proof fn lemma_hom_preserves_relator_insert(
    h: HomomorphismData, w: Word,
    position: int, relator_index: nat, inverted: bool,
)
    requires
        is_valid_homomorphism(h),
        0 <= position <= w.len(),
        0 <= relator_index < h.source.relators.len(),
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, w),
            apply_hom(h, apply_step(h.source, w,
                DerivationStep::RelatorInsert { position, relator_index, inverted }).unwrap()),
        ),
{
    reveal(presentation_valid);
    let r = get_relator(h.source, relator_index, inverted);
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position, w.len() as int);
    let w_prime = (prefix + r) + suffix;
    assert(w =~= prefix + suffix);

    lemma_hom_respects_concat(h, prefix, suffix);
    lemma_hom_respects_concat(h, prefix + r, suffix);
    lemma_hom_respects_concat(h, prefix, r);

    let hom_prefix = apply_hom(h, prefix);
    let hom_suffix = apply_hom(h, suffix);
    let hom_r = apply_hom(h, r);

    lemma_relator_image_is_identity(h, relator_index, inverted);

    //  apply_hom(w_prime) =~= concat(concat(hom_prefix, hom_r), hom_suffix)
    //                     =~= concat(hom_prefix, concat(hom_r, hom_suffix))
    lemma_concat_assoc(hom_prefix, hom_r, hom_suffix);

    //  hom_r ≡ ε → symmetric: ε ≡ hom_r
    //  Prove word_valid(hom_r) for symmetric call
    let rel = get_relator(h.source, relator_index, inverted);
    assert(word_valid(h.source.relators[relator_index as int], h.source.num_generators));
    if inverted {
        crate::word::lemma_inverse_word_valid(
            h.source.relators[relator_index as int], h.source.num_generators);
    }
    lemma_apply_hom_word_valid(h, rel);
    lemma_equiv_symmetric(h.target, hom_r, empty_word());

    //  ε ≡ hom_r → concat(ε, hom_suffix) ≡ concat(hom_r, hom_suffix)
    lemma_equiv_concat_left(h.target, empty_word(), hom_r, hom_suffix);
    //  concat(hom_prefix, concat(ε, hom_suffix)) ≡ concat(hom_prefix, concat(hom_r, hom_suffix))
    lemma_equiv_concat_right(h.target, hom_prefix,
        concat(empty_word(), hom_suffix), concat(hom_r, hom_suffix));
    //  apply_hom(w) =~= concat(hom_prefix, hom_suffix) =~= concat(hom_prefix, concat(ε, hom_suffix))
}

///  Helper: hom preserves RelatorDelete step.
proof fn lemma_hom_preserves_relator_delete(
    h: HomomorphismData, w: Word,
    position: int, relator_index: nat, inverted: bool,
)
    requires
        is_valid_homomorphism(h),
        0 <= relator_index < h.source.relators.len(),
        apply_step(h.source, w, DerivationStep::RelatorDelete { position, relator_index, inverted }) is Some,
    ensures
        equiv_in_presentation(
            h.target,
            apply_hom(h, w),
            apply_hom(h, apply_step(h.source, w,
                DerivationStep::RelatorDelete { position, relator_index, inverted }).unwrap()),
        ),
{
    let r = get_relator(h.source, relator_index, inverted);
    let rlen = r.len();
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position + rlen as int, w.len() as int);
    let w_prime = prefix + suffix;
    assert(w.subrange(position, position + rlen as int) == r);
    assert(w =~= (prefix + r) + suffix);

    lemma_hom_respects_concat(h, prefix + r, suffix);
    lemma_hom_respects_concat(h, prefix, r);
    lemma_hom_respects_concat(h, prefix, suffix);

    let hom_prefix = apply_hom(h, prefix);
    let hom_suffix = apply_hom(h, suffix);
    let hom_r = apply_hom(h, r);

    lemma_relator_image_is_identity(h, relator_index, inverted);

    //  apply_hom(w) =~= concat(concat(hom_prefix, hom_r), hom_suffix)
    //               =~= concat(hom_prefix, concat(hom_r, hom_suffix))
    lemma_concat_assoc(hom_prefix, hom_r, hom_suffix);

    lemma_identity_prefix_equiv(h.target, hom_r, hom_suffix);
    lemma_equiv_concat_right(h.target, hom_prefix, concat(hom_r, hom_suffix), hom_suffix);
}

///  Homomorphism preserves a derivation (sequence of steps).
pub proof fn lemma_hom_preserves_derivation(
    h: HomomorphismData,
    steps: Seq<DerivationStep>, w: Word, w_prime: Word,
)
    requires
        is_valid_homomorphism(h),
        derivation_produces(h.source, steps, w) == Some(w_prime),
    ensures
        equiv_in_presentation(h.target, apply_hom(h, w), apply_hom(h, w_prime)),
    decreases steps.len(),
{
    if steps.len() == 0 {
        lemma_equiv_refl(h.target, apply_hom(h, w));
    } else {
        let step = steps.first();
        let rest = steps.drop_first();
        let w_mid = apply_step(h.source, w, step).unwrap();

        lemma_hom_preserves_single_step(h, w, step, w_mid);
        lemma_hom_preserves_derivation(h, rest, w_mid, w_prime);
        lemma_equiv_transitive(h.target,
            apply_hom(h, w), apply_hom(h, w_mid), apply_hom(h, w_prime));
    }
}

///  **Main theorem**: Homomorphisms preserve equivalence.
pub proof fn lemma_hom_preserves_equiv(
    h: HomomorphismData, w1: Word, w2: Word,
)
    requires
        is_valid_homomorphism(h),
        equiv_in_presentation(h.source, w1, w2),
    ensures
        equiv_in_presentation(h.target, apply_hom(h, w1), apply_hom(h, w2)),
{
    let d = choose|d: Derivation| derivation_valid(h.source, d, w1, w2);
    lemma_hom_preserves_derivation(h, d.steps, w1, w2);
}

///  The identity homomorphism is valid (for valid presentations).
pub proof fn lemma_identity_hom_valid(p: Presentation)
    requires
        presentation_valid(p),
    ensures
        is_valid_homomorphism(identity_hom(p)),
{
    reveal(presentation_valid);
    let h = identity_hom(p);
    assert(h.generator_images.len() == p.num_generators);

    assert forall|i: int| 0 <= i < p.relators.len() implies
        equiv_in_presentation(h.target, apply_hom(h, h.source.relators[i]), empty_word())
    by {
        let r = p.relators[i];
        assert(word_valid(r, p.num_generators));
        lemma_identity_hom_apply(h, r, p.num_generators);
        assert(apply_hom(h, r) =~= r);
        lemma_relator_is_identity(p, i);
    }
}

///  Helper: identity homomorphism preserves valid words.
proof fn lemma_identity_hom_apply(h: HomomorphismData, w: Word, n: nat)
    requires
        h.generator_images.len() == n,
        forall|i: int| 0 <= i < n ==>
            h.generator_images[i] =~= Seq::new(1, |_j: int| Symbol::Gen(i as nat)),
        word_valid(w, n),
    ensures
        apply_hom(h, w) =~= w,
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, n));
        assert(word_valid(rest, n)) by {
            assert forall|i: int| 0 <= i < rest.len() implies symbol_valid(rest[i], n) by {
                assert(rest[i] == w[i + 1]);
            }
        }
        lemma_identity_hom_apply(h, rest, n);

        match s {
            Symbol::Gen(idx) => {
                assert(generator_index(s) == idx);
                assert((idx as int) < (n as int));
                assert(h.generator_images[idx as int] =~= Seq::new(1, |_j: int| Symbol::Gen(idx)));
            },
            Symbol::Inv(idx) => {
                assert(generator_index(s) == idx);
                assert((idx as int) < (n as int));
                assert(h.generator_images[idx as int] =~= Seq::new(1, |_j: int| Symbol::Gen(idx)));
                lemma_inverse_singleton(Symbol::Gen(idx));
            },
        }
        assert(concat(Seq::new(1, |_j: int| s), rest) =~= w);
    }
}

} //  verus!


//  ================================================================
//  FILE: benign.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::quotient::*;

verus! {

//  ============================================================
//  Benign Subgroups
//  ============================================================
//
//  A subgroup H of a group G is "benign" if G embeds in a
//  finitely presented group K such that H = G ∩ L for some
//  finitely generated subgroup L of K.
//
//  This is the key concept in Higman's embedding theorem:
//  a recursively presented group embeds in a finitely presented
//  group iff its relators form a benign subgroup of the free group.
//
//  We formalize this at the presentation level:
//  - G is a presented group
//  - The subgroup is specified by a set of generator words
//  - K is a finitely presented overgroup
//  - The embedding is an injective homomorphism G → K
//  - L is generated by finitely many words in K

//  ============================================================
//  Subgroup generated by words
//  ============================================================

///  A word is in the subgroup generated by `gens` if it is equivalent
///  (in presentation p) to some product of generators and their inverses.
///  Formally: the generated subgroup is the closure of gens ∪ gens⁻¹
///  under concatenation and equivalence.
///
///  We define membership inductively via "generator derivations":
///  a sequence of generator words (possibly inverted) whose
///  concatenation is equivalent to w.
pub open spec fn in_generated_subgroup(
    p: Presentation, gens: Seq<Word>, w: Word,
) -> bool {
    exists|factors: Seq<Word>|
        #[trigger] factors_from_generators(gens, factors) &&
        equiv_in_presentation(p, concat_all(factors), w)
}

///  A word is a generator or the inverse of a generator.
pub open spec fn is_generator_or_inverse(gens: Seq<Word>, w: Word) -> bool {
    exists|j: int| 0 <= j < gens.len() &&
        (w == #[trigger] gens[j] || w == inverse_word(gens[j]))
}

///  Each factor is either a generator or the inverse of a generator.
pub open spec fn factors_from_generators(gens: Seq<Word>, factors: Seq<Word>) -> bool {
    forall|k: int| #![trigger factors[k]]
        0 <= k < factors.len() ==>
        is_generator_or_inverse(gens, factors[k])
}

///  Concatenate a sequence of words: w₁ · w₂ · ... · wₙ.
pub open spec fn concat_all(ws: Seq<Word>) -> Word
    decreases ws.len(),
{
    if ws.len() == 0 {
        empty_word()
    } else {
        concat(ws.first(), concat_all(ws.drop_first()))
    }
}

//  ============================================================
//  Embedding application (self-contained, no HomomorphismData)
//  ============================================================

///  Apply an embedding (Seq<Word> of generator images) to a single symbol.
pub open spec fn apply_embedding_symbol(images: Seq<Word>, s: Symbol) -> Word {
    match s {
        Symbol::Gen(i) => images[i as int],
        Symbol::Inv(i) => inverse_word(images[i as int]),
    }
}

///  Apply an embedding to a word: replace each symbol with its image.
pub open spec fn apply_embedding(images: Seq<Word>, w: Word) -> Word
    decreases w.len(),
{
    if w.len() == 0 {
        empty_word()
    } else {
        concat(apply_embedding_symbol(images, w.first()), apply_embedding(images, w.drop_first()))
    }
}

//  ============================================================
//  Benign subgroup definition
//  ============================================================

///  Witness data for a benign subgroup.
pub struct BenignWitness {
    ///  The finitely presented overgroup K.
    pub overgroup: Presentation,
    ///  The embedding G → K (maps each generator i to a word in K).
    pub embedding: Seq<Word>,
    ///  Generators of the subgroup L ≤ K.
    pub l_generators: Seq<Word>,
}

///  The embedding is injective: equiv in K implies equiv in G.
pub open spec fn embedding_injective(
    g: Presentation, k: Presentation, emb: Seq<Word>,
) -> bool {
    emb.len() == g.num_generators &&
    (forall|w1: Word, w2: Word|
        word_valid(w1, g.num_generators) && word_valid(w2, g.num_generators) &&
        equiv_in_presentation(k, apply_embedding(emb,w1), apply_embedding(emb,w2))
        ==> #[trigger] equiv_in_presentation(g, w1, w2))
}

///  The embedding preserves equivalence: equiv in G implies equiv in K.
pub open spec fn embedding_preserving(
    g: Presentation, k: Presentation, emb: Seq<Word>,
) -> bool {
    emb.len() == g.num_generators &&
    (forall|w1: Word, w2: Word|
        word_valid(w1, g.num_generators) && word_valid(w2, g.num_generators) &&
        equiv_in_presentation(g, w1, w2)
        ==> #[trigger] equiv_in_presentation(k, apply_embedding(emb,w1), apply_embedding(emb,w2)))
}

///  A subgroup (specified by generators) of G is benign.
///
///  There exists a finitely presented K, an injective embedding G → K,
///  and finitely generated L ≤ K such that:
///    w ∈ ⟨gens⟩_G  iff  emb(w) ∈ ⟨l_generators⟩_K
///
///  This captures: the image of the subgroup = intersection of L with image of G.
pub open spec fn is_benign(
    g: Presentation, gens: Seq<Word>,
) -> bool {
    exists|w: BenignWitness| #[trigger] benign_witness_valid(g, gens, w)
}

///  A benign witness is valid.
pub open spec fn benign_witness_valid(
    g: Presentation, gens: Seq<Word>, w: BenignWitness,
) -> bool {
    //  K is finitely presented and valid
    &&& presentation_valid(w.overgroup)
    //  Embedding maps G's generators to valid K-words
    &&& w.embedding.len() == g.num_generators
    &&& (forall|i: int| 0 <= i < w.embedding.len() ==>
        word_valid(#[trigger] w.embedding[i], w.overgroup.num_generators))
    //  L generators are valid K-words
    &&& (forall|i: int| 0 <= i < w.l_generators.len() ==>
        word_valid(#[trigger] w.l_generators[i], w.overgroup.num_generators))
    //  Embedding is injective (K-equiv → G-equiv)
    &&& embedding_injective(g, w.overgroup, w.embedding)
    //  Embedding preserves equivalence (G-equiv → K-equiv)
    &&& embedding_preserving(g, w.overgroup, w.embedding)
    //  Forward: subgroup member → image is in L
    &&& (forall|v: Word|
        word_valid(v, g.num_generators) &&
        in_generated_subgroup(g, gens, v)
        ==> #[trigger] in_generated_subgroup(w.overgroup, w.l_generators, apply_embedding(w.embedding,v)))
    //  Backward: image in L → subgroup member
    &&& (forall|v: Word|
        word_valid(v, g.num_generators) &&
        in_generated_subgroup(w.overgroup, w.l_generators, apply_embedding(w.embedding,v))
        ==> #[trigger] in_generated_subgroup(g, gens, v))
    //  Quotient forward: equiv in G/⟨⟨gens⟩⟩ → equiv in K/⟨⟨l_gens⟩⟩ via embedding
    &&& (forall|w1: Word, w2: Word|
        word_valid(w1, g.num_generators) && word_valid(w2, g.num_generators) &&
        equiv_in_presentation(add_relators(g, gens), w1, w2)
        ==> #[trigger] equiv_in_presentation(
            add_relators(w.overgroup, w.l_generators),
            apply_embedding(w.embedding, w1),
            apply_embedding(w.embedding, w2)))
    //  Quotient backward: equiv in K/⟨⟨l_gens⟩⟩ via embedding → equiv in G/⟨⟨gens⟩⟩
    &&& (forall|w1: Word, w2: Word|
        word_valid(w1, g.num_generators) && word_valid(w2, g.num_generators) &&
        equiv_in_presentation(
            add_relators(w.overgroup, w.l_generators),
            apply_embedding(w.embedding, w1),
            apply_embedding(w.embedding, w2))
        ==> #[trigger] equiv_in_presentation(add_relators(g, gens), w1, w2))
}

//  ============================================================
//  Basic lemmas about concat_all
//  ============================================================

///  concat_all of empty is empty_word.
pub proof fn lemma_concat_all_empty()
    ensures
        concat_all(Seq::<Word>::empty()) == empty_word(),
{
}

///  concat_all of a singleton is the word itself (up to trailing ε).
pub proof fn lemma_concat_all_singleton(w: Word)
    ensures
        concat_all(seq![w]) =~= w,
{
    reveal_with_fuel(concat_all, 2);
    assert(seq![w].first() == w);
    assert(seq![w].drop_first() =~= Seq::<Word>::empty());
    assert(concat_all(Seq::<Word>::empty()) =~= empty_word());
    assert(concat(w, empty_word()) =~= w);
}

///  The identity word is in any generated subgroup.
pub proof fn lemma_identity_in_generated_subgroup(p: Presentation, gens: Seq<Word>)
    ensures
        in_generated_subgroup(p, gens, empty_word()),
{
    let factors = Seq::<Word>::empty();
    assert(factors_from_generators(gens, factors));
    assert(concat_all(factors) =~= empty_word());
    lemma_equiv_refl(p, empty_word());
}

///  Each generator is in the generated subgroup.
pub proof fn lemma_generator_in_generated_subgroup(
    p: Presentation, gens: Seq<Word>, i: int,
)
    requires
        0 <= i < gens.len(),
    ensures
        in_generated_subgroup(p, gens, gens[i]),
{
    let factors = seq![gens[i]];
    assert(factors_from_generators(gens, factors)) by {
        assert forall|k: int| 0 <= k < factors.len()
            implies is_generator_or_inverse(gens, #[trigger] factors[k])
        by {
            assert(factors[k] == gens[i]);
            assert(factors[k] == gens[i] || factors[k] == inverse_word(gens[i]));
        }
    }
    lemma_concat_all_singleton(gens[i]);
    lemma_equiv_refl(p, gens[i]);
}

///  apply_embedding preserves word_valid.
pub proof fn lemma_apply_embedding_valid(images: Seq<Word>, w: Word, n: nat)
    requires
        word_valid(w, images.len()),
        forall|i: int| 0 <= i < images.len() ==> word_valid(#[trigger] images[i], n),
    ensures
        word_valid(apply_embedding(images, w), n),
    decreases w.len(),
{
    if w.len() > 0 {
        let sym = w.first();
        let rest = w.drop_first();
        lemma_apply_embedding_valid(images, rest, n);
        match sym {
            Symbol::Inv(idx) => {
                lemma_inverse_word_valid(images[idx as int], n);
            },
            _ => {},
        }
        lemma_concat_word_valid(
            apply_embedding_symbol(images, sym),
            apply_embedding(images, rest),
            n,
        );
    }
}

///  apply_embedding commutes with inverse_word.
pub proof fn lemma_apply_embedding_inverse(images: Seq<Word>, w: Word)
    ensures
        apply_embedding(images, inverse_word(w))
            =~= inverse_word(apply_embedding(images, w)),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let rest = w.drop_first();
        lemma_apply_embedding_inverse(images, rest);
        lemma_apply_embedding_concat(images,
            inverse_word(rest), Seq::new(1, |_i: int| inverse_symbol(w.first())));
    }
}

///  apply_embedding distributes over concat.
pub proof fn lemma_apply_embedding_concat(images: Seq<Word>, w1: Word, w2: Word)
    ensures
        apply_embedding(images, concat(w1, w2))
            =~= concat(apply_embedding(images, w1), apply_embedding(images, w2)),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
    } else {
        let w1_rest = w1.drop_first();
        lemma_apply_embedding_concat(images, w1_rest, w2);
        //  Z3 should unfold apply_embedding and see the mapped seqs match.
    }
}

} //  verus!


//  ================================================================
//  FILE: shortlex.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;

verus! {

//  ============================================================
//  Symbol ordering
//  ============================================================

///  Total ordering on symbols: Gen(0) < Inv(0) < Gen(1) < Inv(1) < ...
///  Maps each symbol to a unique natural number for comparison.
pub open spec fn symbol_ord(s: Symbol) -> nat {
    match s {
        Symbol::Gen(i) => 2 * i,
        Symbol::Inv(i) => 2 * i + 1,
    }
}

///  symbol_ord is injective: distinct symbols have distinct ordinals.
pub proof fn lemma_symbol_ord_injective(s1: Symbol, s2: Symbol)
    requires
        symbol_ord(s1) == symbol_ord(s2),
    ensures
        s1 == s2,
{
}

///  Inverse symbol has adjacent ordinal.
pub proof fn lemma_symbol_ord_inverse(s: Symbol)
    ensures
        symbol_ord(inverse_symbol(s)) != symbol_ord(s),
{
}

//  ============================================================
//  Lexicographic ordering on words (same-length)
//  ============================================================

///  Lexicographic comparison at a given position.
///  Returns true if w1 < w2 at the first position >= `from` where they differ.
pub open spec fn lex_lt_from(w1: Word, w2: Word, from: nat) -> bool
    decreases w1.len() - from,
{
    if from >= w1.len() {
        false  //  identical words are not strictly less
    } else if symbol_ord(w1[from as int]) < symbol_ord(w2[from as int]) {
        true
    } else if symbol_ord(w1[from as int]) > symbol_ord(w2[from as int]) {
        false
    } else {
        lex_lt_from(w1, w2, from + 1)
    }
}

///  Lexicographic strict less-than on same-length words.
pub open spec fn lex_lt(w1: Word, w2: Word) -> bool
    recommends
        w1.len() == w2.len(),
{
    lex_lt_from(w1, w2, 0)
}

//  ============================================================
//  Shortlex ordering
//  ============================================================

///  Shortlex ordering: shorter words first, then lexicographic for same length.
///  This is a reduction ordering (well-founded + compatible with concatenation).
pub open spec fn shortlex_lt(w1: Word, w2: Word) -> bool {
    w1.len() < w2.len() || (w1.len() == w2.len() && lex_lt(w1, w2))
}

//  ============================================================
//  Lex ordering lemmas
//  ============================================================

///  lex_lt_from is irreflexive.
pub proof fn lemma_lex_lt_from_irreflexive(w: Word, from: nat)
    ensures
        !lex_lt_from(w, w, from),
    decreases w.len() - from,
{
    if from >= w.len() {
    } else {
        lemma_lex_lt_from_irreflexive(w, from + 1);
    }
}

///  lex_lt is irreflexive.
pub proof fn lemma_lex_lt_irreflexive(w: Word)
    ensures
        !lex_lt(w, w),
{
    lemma_lex_lt_from_irreflexive(w, 0);
}

///  lex_lt_from is asymmetric.
pub proof fn lemma_lex_lt_from_asymmetric(w1: Word, w2: Word, from: nat)
    requires
        w1.len() == w2.len(),
        lex_lt_from(w1, w2, from),
    ensures
        !lex_lt_from(w2, w1, from),
    decreases w1.len() - from,
{
    if from >= w1.len() {
    } else if symbol_ord(w1[from as int]) < symbol_ord(w2[from as int]) {
        //  w1 < w2 at this position, so w2[from] > w1[from], thus w2 !< w1
    } else if symbol_ord(w1[from as int]) > symbol_ord(w2[from as int]) {
        //  contradicts lex_lt_from(w1, w2, from)
    } else {
        lemma_lex_lt_from_asymmetric(w1, w2, from + 1);
    }
}

///  lex_lt_from is transitive.
pub proof fn lemma_lex_lt_from_transitive(w1: Word, w2: Word, w3: Word, from: nat)
    requires
        w1.len() == w2.len(),
        w2.len() == w3.len(),
        lex_lt_from(w1, w2, from),
        lex_lt_from(w2, w3, from),
    ensures
        lex_lt_from(w1, w3, from),
    decreases w1.len() - from,
{
    if from >= w1.len() {
    } else if symbol_ord(w1[from as int]) < symbol_ord(w2[from as int]) {
        //  w1[from] < w2[from] and w2[from] <= w3[from], so w1[from] < w3[from] or equal then recurse
        if symbol_ord(w2[from as int]) < symbol_ord(w3[from as int]) {
            //  w1[from] < w3[from]
        } else if symbol_ord(w2[from as int]) == symbol_ord(w3[from as int]) {
            //  w1[from] < w2[from] = w3[from]
        } else {
            //  w2[from] > w3[from], contradicts lex_lt_from(w2, w3, from) unless resolved earlier
            //  but w2[from] > w3[from] means lex_lt_from(w2, w3, from) = false, contradiction
        }
    } else if symbol_ord(w1[from as int]) == symbol_ord(w2[from as int]) {
        if symbol_ord(w2[from as int]) < symbol_ord(w3[from as int]) {
            //  w1[from] = w2[from] < w3[from]
        } else if symbol_ord(w2[from as int]) == symbol_ord(w3[from as int]) {
            //  all equal, recurse
            lemma_lex_lt_from_transitive(w1, w2, w3, from + 1);
        } else {
            //  w2[from] > w3[from], contradicts lex_lt_from(w2, w3, from)
        }
    } else {
        //  w1[from] > w2[from], contradicts lex_lt_from(w1, w2, from)
    }
}

///  lex_lt is transitive.
pub proof fn lemma_lex_lt_transitive(w1: Word, w2: Word, w3: Word)
    requires
        w1.len() == w2.len(),
        w2.len() == w3.len(),
        lex_lt(w1, w2),
        lex_lt(w2, w3),
    ensures
        lex_lt(w1, w3),
{
    lemma_lex_lt_from_transitive(w1, w2, w3, 0);
}

///  lex_lt_from is total on same-length distinct words (trichotomy).
pub proof fn lemma_lex_lt_from_total(w1: Word, w2: Word, from: nat)
    requires
        w1.len() == w2.len(),
        w1 !== w2,
        //  They differ at some position >= from
        exists|k: int| from as int <= k < w1.len() as int && w1[k] !== w2[k],
    ensures
        lex_lt_from(w1, w2, from) || lex_lt_from(w2, w1, from),
    decreases w1.len() - from,
{
    if from >= w1.len() {
        //  contradiction: no position exists
    } else if symbol_ord(w1[from as int]) < symbol_ord(w2[from as int]) {
    } else if symbol_ord(w1[from as int]) > symbol_ord(w2[from as int]) {
    } else {
        //  same ordinal means same symbol
        lemma_symbol_ord_injective(w1[from as int], w2[from as int]);
        //  They still differ somewhere after `from`
        let k = choose|k: int| from as int <= k < w1.len() as int && w1[k] !== w2[k];
        assert(k > from as int);  //  since w1[from] == w2[from]
        assert(exists|k: int| (from + 1) as int <= k < w1.len() as int && w1[k] !== w2[k]);
        lemma_lex_lt_from_total(w1, w2, from + 1);
    }
}

///  Same-length words: if not equal, one is lex-less than the other.
pub proof fn lemma_lex_lt_total(w1: Word, w2: Word)
    requires
        w1.len() == w2.len(),
    ensures
        lex_lt(w1, w2) || lex_lt(w2, w1) || w1 =~= w2,
{
    if w1 =~= w2 {
    } else {
        //  They differ somewhere
        assert(exists|k: int| 0 <= k < w1.len() as int && w1[k] !== w2[k]) by {
            if forall|k: int| 0 <= k < w1.len() as int ==> w1[k] === w2[k] {
                assert(w1 =~= w2);
            }
        }
        lemma_lex_lt_from_total(w1, w2, 0);
    }
}

//  ============================================================
//  Shortlex ordering lemmas
//  ============================================================

///  Shortlex is irreflexive.
pub proof fn lemma_shortlex_irreflexive(w: Word)
    ensures
        !shortlex_lt(w, w),
{
    lemma_lex_lt_irreflexive(w);
}

///  Shortlex is transitive.
pub proof fn lemma_shortlex_transitive(w1: Word, w2: Word, w3: Word)
    requires
        shortlex_lt(w1, w2),
        shortlex_lt(w2, w3),
    ensures
        shortlex_lt(w1, w3),
{
    if w1.len() < w2.len() {
        if w2.len() < w3.len() {
            //  w1.len() < w3.len()
        } else {
            //  w2.len() == w3.len() && lex_lt(w2, w3), but w1.len() < w2.len() = w3.len()
        }
    } else {
        //  w1.len() == w2.len() && lex_lt(w1, w2)
        if w2.len() < w3.len() {
            //  w1.len() = w2.len() < w3.len()
        } else {
            //  w1.len() == w2.len() == w3.len()
            lemma_lex_lt_transitive(w1, w2, w3);
        }
    }
}

///  Shortlex is total: any two distinct words are comparable.
pub proof fn lemma_shortlex_total(w1: Word, w2: Word)
    ensures
        shortlex_lt(w1, w2) || shortlex_lt(w2, w1) || w1 =~= w2,
{
    if w1.len() < w2.len() {
    } else if w2.len() < w1.len() {
    } else {
        lemma_lex_lt_total(w1, w2);
    }
}

///  Shortlex is asymmetric.
pub proof fn lemma_shortlex_asymmetric(w1: Word, w2: Word)
    requires
        shortlex_lt(w1, w2),
    ensures
        !shortlex_lt(w2, w1),
{
    if w1.len() < w2.len() {
        //  w2.len() > w1.len(), so w2.len() < w1.len() is false and w2.len() == w1.len() is false
    } else {
        //  w1.len() == w2.len() && lex_lt(w1, w2)
        lemma_lex_lt_from_asymmetric(w1, w2, 0);
    }
}

///  The empty word is shortlex-minimal: nothing is smaller than it.
pub proof fn lemma_empty_shortlex_minimal(w: Word)
    ensures
        !shortlex_lt(w, empty_word()) || w =~= empty_word(),
{
}

//  ============================================================
//  Compatibility with concatenation
//  ============================================================

///  Key lemma: if two words have the same length and one is lex-smaller,
///  then prepending the same prefix preserves the lex ordering.
pub proof fn lemma_lex_lt_from_prepend(w1: Word, w2: Word, prefix: Word, from: nat)
    requires
        w1.len() == w2.len(),
        lex_lt_from(w1, w2, from),
    ensures
        lex_lt_from(prefix + w1, prefix + w2, prefix.len() + from),
    decreases w1.len() - from,
{
    let pw1 = prefix + w1;
    let pw2 = prefix + w2;
    if from >= w1.len() {
    } else {
        let idx = prefix.len() + from;
        assert(pw1[idx as int] == w1[from as int]);
        assert(pw2[idx as int] == w2[from as int]);
        if symbol_ord(w1[from as int]) < symbol_ord(w2[from as int]) {
            //  pw1[idx] < pw2[idx], so lex_lt_from(pw1, pw2, idx) = true
        } else if symbol_ord(w1[from as int]) == symbol_ord(w2[from as int]) {
            lemma_lex_lt_from_prepend(w1, w2, prefix, from + 1);
        }
    }
}

///  Key lemma: if two words have the same length and one is lex-smaller,
///  then appending the same suffix preserves the lex ordering.
pub proof fn lemma_lex_lt_from_append(w1: Word, w2: Word, suffix: Word, from: nat)
    requires
        w1.len() == w2.len(),
        lex_lt_from(w1, w2, from),
    ensures
        lex_lt_from(w1 + suffix, w2 + suffix, from),
    decreases w1.len() - from,
{
    let ws1 = w1 + suffix;
    let ws2 = w2 + suffix;
    if from >= w1.len() {
    } else {
        assert(ws1[from as int] == w1[from as int]);
        assert(ws2[from as int] == w2[from as int]);
        if symbol_ord(w1[from as int]) < symbol_ord(w2[from as int]) {
        } else if symbol_ord(w1[from as int]) == symbol_ord(w2[from as int]) {
            lemma_lex_lt_from_append(w1, w2, suffix, from + 1);
        }
    }
}

///  Shortlex is compatible with concatenation on both sides.
///  If u < v in shortlex, then w·u·x < w·v·x for any w, x.
///  (This is the "reduction ordering" property.)
pub proof fn lemma_shortlex_compatible_concat(u: Word, v: Word, prefix: Word, suffix: Word)
    requires
        shortlex_lt(u, v),
    ensures
        shortlex_lt(prefix + u + suffix, prefix + v + suffix),
{
    let pu = prefix + u + suffix;
    let pv = prefix + v + suffix;

    if u.len() < v.len() {
        //  |prefix + u + suffix| < |prefix + v + suffix|
        assert(pu.len() < pv.len());
    } else {
        //  u.len() == v.len() && lex_lt(u, v)
        assert(pu.len() == pv.len());
        //  First: lex_lt_from(u + suffix, v + suffix, 0)
        lemma_lex_lt_from_append(u, v, suffix, 0);
        //  Then: lex_lt_from(prefix + (u+suffix), prefix + (v+suffix), prefix.len())
        lemma_lex_lt_from_prepend(u + suffix, v + suffix, prefix, 0);
        //  Reassociate
        assert((prefix + u + suffix) =~= (prefix + (u + suffix)));
        assert((prefix + v + suffix) =~= (prefix + (v + suffix)));
        //  The prefix is identical, so lower from prefix.len() to 0
        assert(forall|i: int| 0 <= i < prefix.len() as int ==> pu[i] == pv[i]) by {
            assert forall|i: int| 0 <= i < prefix.len() as int implies pu[i] == pv[i] by {
                assert(pu[i] == prefix[i]);
                assert(pv[i] == prefix[i]);
            }
        }
        lemma_lex_lt_from_lower(pu, pv, 0, prefix.len());
    }
}

///  If words agree on [from, to) and lex_lt_from holds at `to`, then it holds at `from`.
proof fn lemma_lex_lt_from_lower(w1: Word, w2: Word, from: nat, to: nat)
    requires
        w1.len() == w2.len(),
        from <= to,
        forall|i: int| from as int <= i < to as int ==> w1[i] == w2[i],
        lex_lt_from(w1, w2, to),
    ensures
        lex_lt_from(w1, w2, from),
    decreases to - from,
{
    if from == to {
    } else {
        //  w1[from] == w2[from], so symbol_ord equal
        assert(w1[from as int] == w2[from as int]);
        //  lex_lt_from(w1, w2, from) falls through to lex_lt_from(w1, w2, from + 1)
        lemma_lex_lt_from_lower(w1, w2, from + 1, to);
    }
}

//  ============================================================
//  Well-foundedness (via nat measure)
//  ============================================================

///  Shortlex rank: a nat that strictly decreases with shortlex_lt.
///  We use a simple encoding: (word_length, lex_rank) as a pair,
///  but for Verus decreases clauses, we just use the word length
///  as the primary measure since that's sufficient for KB
///  (all rules strictly decrease length, or same length with lex decrease).
///
///  For the general Newman's lemma, we use lexicographic decreases (len, lex_rank).

///  If shortlex_lt(w1, w2), then w1.len() <= w2.len().
pub proof fn lemma_shortlex_lt_len_bound(w1: Word, w2: Word)
    requires
        shortlex_lt(w1, w2),
    ensures
        w1.len() <= w2.len(),
{
}

///  Replacing a subword with a shortlex-smaller one gives a shortlex-smaller word.
///  This is the key lemma for showing that rewrite rules decrease words.
pub proof fn lemma_shortlex_subword_replace(
    w: Word,
    pos: int,
    old_len: nat,
    replacement: Word,
    old_word: Word,
)
    requires
        0 <= pos,
        pos + old_len <= w.len(),
        w.subrange(pos, pos + old_len as int) == old_word,
        shortlex_lt(replacement, old_word),
    ensures
        shortlex_lt(
            w.subrange(0, pos) + replacement + w.subrange(pos + old_len as int, w.len() as int),
            w,
        ),
{
    let prefix = w.subrange(0, pos);
    let suffix = w.subrange(pos + old_len as int, w.len() as int);
    let new_w = prefix + replacement + suffix;

    //  w =~= prefix + old_word + suffix
    assert(w =~= prefix + old_word + suffix) by {
        assert(w =~= w.subrange(0, pos) + w.subrange(pos, w.len() as int));
        assert(w.subrange(pos, w.len() as int) =~=
            w.subrange(pos, pos + old_len as int) + w.subrange(pos + old_len as int, w.len() as int));
    }

    lemma_shortlex_compatible_concat(replacement, old_word, prefix, suffix);
}

} //  verus!


//  ================================================================
//  FILE: todd_coxeter.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
verus! {

///  Coset table for a finitely presented group.
///  table[coset][column] where column = 2*gen for Gen(gen), 2*gen+1 for Inv(gen).
///  None means undefined.
pub struct CosetTable {
    pub num_cosets: nat,
    pub num_gens: nat,
    pub table: Seq<Seq<Option<nat>>>,
}

///  Map a symbol to a column index.
pub open spec fn symbol_to_column(s: Symbol) -> nat {
    match s {
        Symbol::Gen(i) => 2 * i,
        Symbol::Inv(i) => 2 * i + 1,
    }
}

///  Map a column to its inverse column (Gen ↔ Inv for same generator).
pub open spec fn inverse_column(col: nat) -> nat {
    if col % 2 == 0 {
        col + 1
    } else {
        (col - 1) as nat
    }
}

///  A coset table is well-formed: dimensions match and values in range.
#[verifier::opaque]
pub open spec fn coset_table_wf(t: CosetTable) -> bool {
    let num_cols = 2 * t.num_gens;
    t.table.len() == t.num_cosets
    && (forall|c: int| #![trigger t.table[c]]
        0 <= c < t.num_cosets ==> t.table[c].len() == num_cols)
    && (forall|c: int, col: int| #![trigger t.table[c][col]]
        0 <= c < t.num_cosets && 0 <= col < num_cols ==>
            match t.table[c][col] {
                Some(d) => d < t.num_cosets,
                None => true,
            })
}

///  Inverse consistency: if table[c][col] = Some(d), then table[d][inv_col] = Some(c).
#[verifier::opaque]
pub open spec fn coset_table_consistent(t: CosetTable) -> bool {
    let num_cols = 2 * t.num_gens;
    coset_table_wf(t)
    && (forall|c: int, col: int| #![trigger t.table[c][col]]
        0 <= c < t.num_cosets && 0 <= col < num_cols ==>
            match t.table[c][col] {
                Some(d) => t.table[d as int][inverse_column(col as nat) as int] == Some(c as nat),
                None => true,
            })
}

///  Trace a word through the coset table starting from a coset.
///  Returns None if an undefined entry is hit.
pub open spec fn trace_word(t: CosetTable, coset: nat, w: Word) -> Option<nat>
    decreases w.len(),
{
    if w.len() == 0 {
        Some(coset)
    } else {
        let col = symbol_to_column(w.first());
        match t.table[coset as int][col as int] {
            Some(next) => trace_word(t, next, w.drop_first()),
            None => None,
        }
    }
}

///  All relators trace back to the starting coset (closed table).
#[verifier::opaque]
pub open spec fn relator_closed(t: CosetTable, p: Presentation) -> bool {
    forall|c: int, r: int| #![trigger t.table[c as int], p.relators[r]]
        0 <= c < t.num_cosets && 0 <= r < p.relators.len() ==>
            trace_word(t, c as nat, p.relators[r]) == Some(c as nat)
}

//  --- Lemmas ---

///  Tracing the empty word returns the starting coset.
pub proof fn lemma_trace_empty(t: CosetTable, coset: nat)
    ensures
        trace_word(t, coset, empty_word()) == Some(coset),
{
}

///  Tracing a concatenation is composition of traces.
pub proof fn lemma_trace_word_concat(t: CosetTable, c: nat, w1: Word, w2: Word)
    requires
        coset_table_wf(t),
        trace_word(t, c, w1) is Some,
    ensures
        trace_word(t, c, concat(w1, w2)) ==
            trace_word(t, trace_word(t, c, w1).unwrap(), w2),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
        assert(trace_word(t, c, w1) == Some(c));
    } else {
        let col = symbol_to_column(w1.first());
        let next = t.table[c as int][col as int].unwrap();
        assert(concat(w1, w2).first() == w1.first());
        assert(concat(w1, w2).drop_first() =~= concat(w1.drop_first(), w2));
        //  trace_word(t, c, concat(w1, w2))
        //    = trace_word(t, next, concat(w1.drop_first(), w2))
        //  trace_word(t, c, w1)
        //    = trace_word(t, next, w1.drop_first())
        lemma_trace_word_concat(t, next, w1.drop_first(), w2);
    }
}

} //  verus!

//  (Runtime coset enumeration code removed — not needed for the proof.)


//  ================================================================
//  FILE: normal_form_free_product.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::free_product::*;
use crate::homomorphism::*;

verus! {

//  ============================================================
//  Free Product Injectivity via Retraction Homomorphism
//  ============================================================
//
//  Theorem: If w is a G₁-word and w ≡ ε in free_product(p1, p2),
//  then w ≡ ε in p1.
//
//  Proof: Define a retraction ρ: FP → P₁ that collapses G₂ generators
//  to ε and maps G₁ generators to themselves. Then:
//    w ≡ ε in FP  ⟹  ρ(w) ≡ ρ(ε) in P₁  ⟹  w ≡ ε in P₁.

//  ============================================================
//  Left retraction: FP(p1, p2) → p1
//  ============================================================

///  The left retraction homomorphism.
///  Gen(i) for i < n₁ → [Gen(i)]; Gen(j) for j ≥ n₁ → ε.
pub open spec fn fp_left_retraction(p1: Presentation, p2: Presentation) -> HomomorphismData {
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;
    HomomorphismData {
        source: free_product(p1, p2),
        target: p1,
        generator_images: Seq::new(n1 + n2, |i: int|
            if i < n1 {
                Seq::new(1, |_j: int| Symbol::Gen(i as nat))
            } else {
                empty_word()
            }
        ),
    }
}

//  ============================================================
//  Helper: apply_hom collapses a word whose symbols all map to ε
//  ============================================================

///  If every symbol of w maps to ε under h, then apply_hom(h, w) =~= ε.
pub proof fn lemma_hom_collapses_word(h: HomomorphismData, w: Word)
    requires
        forall|k: int| 0 <= k < w.len() ==>
            apply_hom_symbol(h, #[trigger] w[k]) =~= empty_word(),
    ensures
        apply_hom(h, w) =~= empty_word(),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(w[0] == s);
        assert(apply_hom_symbol(h, s) =~= empty_word());
        //  Recurse: rest also collapses
        assert forall|k: int| 0 <= k < rest.len() implies
            apply_hom_symbol(h, #[trigger] rest[k]) =~= empty_word()
        by {
            assert(rest[k] == w[k + 1]);
        }
        lemma_hom_collapses_word(h, rest);
        assert(apply_hom(h, rest) =~= empty_word());
        assert(apply_hom(h, w) =~= concat(empty_word(), empty_word()));
        assert(concat(empty_word(), empty_word()) =~= empty_word());
    }
}

//  ============================================================
//  Helper: apply_hom is the identity on words with identity images
//  ============================================================

///  If images[i] =~= [Gen(i)] for all i < n, and word_valid(w, n),
///  then apply_hom(h, w) =~= w.
pub proof fn lemma_hom_identity_on_word(h: HomomorphismData, w: Word, n: nat)
    requires
        forall|i: int| 0 <= i < n ==>
            h.generator_images[i] =~= Seq::new(1, |_j: int| Symbol::Gen(i as nat)),
        h.generator_images.len() >= n,
        word_valid(w, n),
    ensures
        apply_hom(h, w) =~= w,
    decreases w.len(),
{
    if w.len() == 0 {
        assert(apply_hom(h, w) =~= empty_word());
        assert(w =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        assert(symbol_valid(s, n));

        //  Recurse
        assert(word_valid(rest, n)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(rest[k], n)
            by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_hom_identity_on_word(h, rest, n);
        assert(apply_hom(h, rest) =~= rest);

        //  Show apply_hom_symbol(h, s) =~= Seq::new(1, |_| s)
        let idx = generator_index(s);
        assert(idx < n);
        match s {
            Symbol::Gen(i) => {
                assert(h.generator_images[i as int]
                    =~= Seq::new(1, |_j: int| Symbol::Gen(i)));
                assert(apply_hom_symbol(h, s) =~= h.generator_images[i as int]);
                assert(apply_hom_symbol(h, s)
                    =~= Seq::new(1, |_j: int| Symbol::Gen(i)));
            },
            Symbol::Inv(i) => {
                let img = Seq::new(1, |_j: int| Symbol::Gen(i));
                assert(h.generator_images[i as int] =~= img);
                //  inverse_word([Gen(i)]) = inverse_word([].drop_first()) + [Inv(Gen(i).first())]
                //  = inverse_word(empty) + [Inv(i)] = empty + [Inv(i)] = [Inv(i)]
                assert(img.drop_first() =~= Seq::<Symbol>::empty());
                assert(inverse_word(img.drop_first()) =~= empty_word());
                assert(inverse_symbol(img.first()) == Symbol::Inv(i));
                let inv_img = inverse_word(img);
                assert(inv_img =~= empty_word() + Seq::new(1, |_j: int| Symbol::Inv(i)));
                assert(inv_img =~= Seq::new(1, |_j: int| Symbol::Inv(i)));
                assert(apply_hom_symbol(h, s) =~= inv_img);
            },
        }

        //  apply_hom(h, w) = concat(apply_hom_symbol(h, s), apply_hom(h, rest))
        //                  =~= concat([s], rest) =~= w
        assert(apply_hom_symbol(h, s) =~= Seq::new(1, |_j: int| s));
        assert(apply_hom(h, w) =~= concat(Seq::new(1, |_j: int| s), rest));
        assert(concat(Seq::new(1, |_j: int| s), rest) =~= w) by {
            let lhs = concat(Seq::new(1, |_j: int| s), rest);
            assert(lhs.len() == 1 + rest.len());
            assert(lhs.len() == w.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == w[k] by {
                if k == 0 {
                    assert(lhs[0] == s);
                    assert(w[0] == s);
                } else {
                    assert(lhs[k] == rest[k - 1]);
                    assert(rest[k - 1] == w[k]);
                }
            }
        }
    }
}

//  ============================================================
//  Left retraction is a valid homomorphism
//  ============================================================

///  The left retraction is a valid homomorphism.
pub proof fn lemma_fp_left_retraction_valid(p1: Presentation, p2: Presentation)
    requires
        presentation_valid(p1),
        presentation_valid(p2),
    ensures
        is_valid_homomorphism(fp_left_retraction(p1, p2)),
{
    reveal(presentation_valid);
    let rho = fp_left_retraction(p1, p2);
    let fp = free_product(p1, p2);
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;

    //  generator_images.len() == n1 + n2 = fp.num_generators
    assert(rho.generator_images.len() == n1 + n2);
    assert(rho.source.num_generators == n1 + n2);

    //  source = free_product(p1, p2) is presentation_valid
    assert(presentation_valid(fp)) by {
        assert forall|k: int| 0 <= k < fp.relators.len()
            implies word_valid(fp.relators[k], fp.num_generators)
        by {
            if k < p1.relators.len() as int {
                assert(fp.relators[k] == p1.relators[k]);
                assert(word_valid(p1.relators[k], n1));
                assert forall|m: int| 0 <= m < fp.relators[k].len()
                    implies symbol_valid(fp.relators[k][m], n1 + n2) by {
                    assert(symbol_valid(fp.relators[k][m], n1));
                }
            } else {
                let j = k - p1.relators.len() as int;
                assert(fp.relators[k] == shift_word(p2.relators[j], n1));
                //  shift_word_valid: shifted word is valid for combined generator count
                let sw = shift_word(p2.relators[j], n1);
                assert forall|m: int| 0 <= m < sw.len()
                    implies symbol_valid(sw[m], n1 + n2)
                by {
                    assert(sw[m] == shift_symbol(p2.relators[j][m], n1));
                    assert(symbol_valid(p2.relators[j][m], n2));
                }
            }
        }
    }

    //  target = p1 is presentation_valid (given)

    //  Each image is word_valid for p1
    assert forall|i: int| 0 <= i < rho.generator_images.len()
        implies word_valid(rho.generator_images[i], n1)
    by {
        if i < n1 as int {
            //  Image is [Gen(i)], valid for n1
            assert(rho.generator_images[i] =~=
                Seq::new(1, |_j: int| Symbol::Gen(i as nat)));
            assert(symbol_valid(Symbol::Gen(i as nat), n1));
        } else {
            //  Image is empty_word(), trivially valid
        }
    }

    //  Each source relator maps to ≡ ε in p1
    assert forall|i: int| 0 <= i < fp.relators.len()
        implies equiv_in_presentation(p1, apply_hom(rho, fp.relators[i]), empty_word())
    by {
        if i < p1.relators.len() as int {
            //  G₁-relator: rho maps it to itself
            let r = fp.relators[i];
            assert(r == p1.relators[i]);
            assert(word_valid(r, n1));
            lemma_hom_identity_on_word(rho, r, n1);
            assert(apply_hom(rho, r) =~= r);
            //  r ≡ ε in p1 since it's a relator
            lemma_relator_is_identity(p1, i);
            //  Need: apply_hom(rho, r) ≡ ε. Since apply_hom(rho, r) =~= r and r ≡ ε:
            lemma_equiv_refl(p1, apply_hom(rho, r));
        } else {
            //  Shifted G₂-relator: all symbols have index ≥ n1, so all map to ε
            let j = i - p1.relators.len() as int;
            let r = fp.relators[i];
            assert(r == shift_word(p2.relators[j], n1));
            //  Every symbol in r has generator_index ≥ n1
            assert forall|k: int| 0 <= k < r.len()
                implies apply_hom_symbol(rho, #[trigger] r[k]) =~= empty_word()
            by {
                let s = r[k];
                assert(s == shift_symbol(p2.relators[j][k], n1));
                let orig = p2.relators[j][k];
                match orig {
                    Symbol::Gen(gi) => {
                        assert(s == Symbol::Gen(gi + n1));
                        assert(generator_index(s) == gi + n1);
                        assert(gi + n1 >= n1);
                        assert(rho.generator_images[(gi + n1) as int] =~= empty_word());
                    },
                    Symbol::Inv(gi) => {
                        assert(s == Symbol::Inv(gi + n1));
                        assert(generator_index(s) == gi + n1);
                        assert(gi + n1 >= n1);
                        assert(rho.generator_images[(gi + n1) as int] =~= empty_word());
                        assert(inverse_word(empty_word()) =~= empty_word());
                    },
                }
            }
            lemma_hom_collapses_word(rho, r);
            assert(apply_hom(rho, r) =~= empty_word());
            lemma_equiv_refl(p1, empty_word());
        }
    }
}

//  ============================================================
//  Left retraction is the identity on G₁-words
//  ============================================================

///  For G₁-words: apply_hom(ρ, w) =~= w.
pub proof fn lemma_fp_left_retraction_identity(
    p1: Presentation, p2: Presentation, w: Word,
)
    requires
        word_valid(w, p1.num_generators),
    ensures
        apply_hom(fp_left_retraction(p1, p2), w) =~= w,
{
    let rho = fp_left_retraction(p1, p2);
    let n1 = p1.num_generators;
    lemma_hom_identity_on_word(rho, w, n1);
}

//  ============================================================
//  Main theorem: free product injectivity (left)
//  ============================================================

///  If w is a G₁-word and w ≡ ε in free_product(p1, p2), then w ≡ ε in p1.
pub proof fn lemma_free_product_injective_left(
    p1: Presentation, p2: Presentation, w: Word,
)
    requires
        presentation_valid(p1),
        presentation_valid(p2),
        word_valid(w, p1.num_generators),
        equiv_in_presentation(free_product(p1, p2), w, empty_word()),
    ensures
        equiv_in_presentation(p1, w, empty_word()),
{
    let rho = fp_left_retraction(p1, p2);

    //  rho is a valid homomorphism
    lemma_fp_left_retraction_valid(p1, p2);

    //  rho preserves equivalence: w ≡ ε in FP ⟹ rho(w) ≡ rho(ε) in P₁
    lemma_hom_preserves_equiv(rho, w, empty_word());

    //  rho(w) =~= w
    lemma_fp_left_retraction_identity(p1, p2, w);

    //  rho(ε) =~= ε
    lemma_hom_empty(rho);

    //  So w ≡ ε in P₁
}

//  ============================================================
//  Right retraction: FP(p1, p2) → p2
//  ============================================================

///  The right retraction homomorphism.
///  Gen(i) for i < n₁ → ε; Gen(n₁+j) for j < n₂ → [Gen(j)].
pub open spec fn fp_right_retraction(p1: Presentation, p2: Presentation) -> HomomorphismData {
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;
    HomomorphismData {
        source: free_product(p1, p2),
        target: p2,
        generator_images: Seq::new(n1 + n2, |i: int|
            if i < n1 {
                empty_word()
            } else {
                Seq::new(1, |_j: int| Symbol::Gen((i - n1) as nat))
            }
        ),
    }
}

///  The right retraction is a valid homomorphism.
pub proof fn lemma_fp_right_retraction_valid(p1: Presentation, p2: Presentation)
    requires
        presentation_valid(p1),
        presentation_valid(p2),
    ensures
        is_valid_homomorphism(fp_right_retraction(p1, p2)),
{
    reveal(presentation_valid);
    let rho = fp_right_retraction(p1, p2);
    let fp = free_product(p1, p2);
    let n1 = p1.num_generators;
    let n2 = p2.num_generators;

    //  source = free_product(p1, p2) is presentation_valid
    assert(presentation_valid(fp)) by {
        assert forall|k: int| 0 <= k < fp.relators.len()
            implies word_valid(fp.relators[k], fp.num_generators)
        by {
            if k < p1.relators.len() as int {
                assert(fp.relators[k] == p1.relators[k]);
                assert(word_valid(p1.relators[k], n1));
                assert forall|m: int| 0 <= m < fp.relators[k].len()
                    implies symbol_valid(fp.relators[k][m], n1 + n2) by {
                    assert(symbol_valid(fp.relators[k][m], n1));
                }
            } else {
                let j = k - p1.relators.len() as int;
                assert(fp.relators[k] == shift_word(p2.relators[j], n1));
                //  shift_word_valid: shifted word is valid for combined generator count
                let sw = shift_word(p2.relators[j], n1);
                assert forall|m: int| 0 <= m < sw.len()
                    implies symbol_valid(sw[m], n1 + n2)
                by {
                    assert(sw[m] == shift_symbol(p2.relators[j][m], n1));
                    assert(symbol_valid(p2.relators[j][m], n2));
                }
            }
        }
    }

    //  Each image is word_valid for p2
    assert forall|i: int| 0 <= i < rho.generator_images.len()
        implies word_valid(rho.generator_images[i], n2)
    by {
        if i < n1 as int {
            //  empty_word() is trivially valid
        } else {
            let gi = (i - n1) as nat;
            assert(rho.generator_images[i] =~=
                Seq::new(1, |_j: int| Symbol::Gen(gi)));
            assert(gi < n2);
            assert(symbol_valid(Symbol::Gen(gi), n2));
        }
    }

    //  Each source relator maps to ≡ ε in p2
    assert forall|i: int| 0 <= i < fp.relators.len()
        implies equiv_in_presentation(p2, apply_hom(rho, fp.relators[i]), empty_word())
    by {
        if i < p1.relators.len() as int {
            //  G₁-relator: all symbols have index < n1, all map to ε
            let r = fp.relators[i];
            assert(r == p1.relators[i]);
            assert(word_valid(r, n1));
            assert forall|k: int| 0 <= k < r.len()
                implies apply_hom_symbol(rho, #[trigger] r[k]) =~= empty_word()
            by {
                let s = r[k];
                assert(symbol_valid(s, n1));
                assert(generator_index(s) < n1);
                match s {
                    Symbol::Gen(gi) => {
                        assert(rho.generator_images[gi as int] =~= empty_word());
                    },
                    Symbol::Inv(gi) => {
                        assert(rho.generator_images[gi as int] =~= empty_word());
                        assert(inverse_word(empty_word()) =~= empty_word());
                    },
                }
            }
            lemma_hom_collapses_word(rho, r);
            lemma_equiv_refl(p2, empty_word());
        } else {
            //  Shifted G₂-relator: rho maps shift(Gen(j)) = Gen(n1+j) → [Gen(j)]
            //  So rho(shift(r_j)) =~= r_j (the original G₂ relator)
            let j = i - p1.relators.len() as int;
            let sr = fp.relators[i];
            assert(sr == shift_word(p2.relators[j], n1));
            let r = p2.relators[j];

            //  Show apply_hom(rho, sr) =~= r by showing it's the identity on shifted words
            lemma_right_retraction_unshifts(p1, p2, r);
            assert(apply_hom(rho, sr) =~= r);

            //  r ≡ ε in p2 since it's a relator
            lemma_relator_is_identity(p2, j);
            lemma_equiv_refl(p2, apply_hom(rho, sr));
        }
    }
}

///  Helper: The right retraction unshifts a shifted G₂-word back to the original.
///  apply_hom(right_rho, shift_word(w, n1)) =~= w for G₂-words.
proof fn lemma_right_retraction_unshifts(
    p1: Presentation, p2: Presentation, w: Word,
)
    requires
        word_valid(w, p2.num_generators),
    ensures
        apply_hom(fp_right_retraction(p1, p2), shift_word(w, p1.num_generators)) =~= w,
    decreases w.len(),
{
    let rho = fp_right_retraction(p1, p2);
    let n1 = p1.num_generators;
    let sw = shift_word(w, n1);

    if w.len() == 0 {
        assert(sw =~= empty_word());
        assert(apply_hom(rho, sw) =~= empty_word());
    } else {
        let s = w.first();
        let rest = w.drop_first();
        let ss = shift_symbol(s, n1);
        let srest = shift_word(rest, n1);

        assert(sw.first() == ss);
        assert(sw.drop_first() =~= srest);

        //  Recurse
        assert(word_valid(rest, p2.num_generators)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies symbol_valid(rest[k], p2.num_generators)
            by {
                assert(rest[k] == w[k + 1]);
            }
        }
        lemma_right_retraction_unshifts(p1, p2, rest);
        assert(apply_hom(rho, srest) =~= rest);

        //  Show apply_hom_symbol(rho, ss) =~= Seq::new(1, |_| s)
        assert(symbol_valid(s, p2.num_generators));
        match s {
            Symbol::Gen(gi) => {
                assert(ss == Symbol::Gen(gi + n1));
                assert((gi + n1) >= n1);
                assert(rho.generator_images[(gi + n1) as int]
                    =~= Seq::new(1, |_j: int| Symbol::Gen(gi)));
                assert(apply_hom_symbol(rho, ss)
                    =~= Seq::new(1, |_j: int| Symbol::Gen(gi)));
                assert(Seq::new(1, |_j: int| Symbol::Gen(gi))
                    =~= Seq::new(1, |_j: int| s));
            },
            Symbol::Inv(gi) => {
                assert(ss == Symbol::Inv(gi + n1));
                assert((gi + n1) >= n1);
                let img = Seq::new(1, |_j: int| Symbol::Gen(gi));
                assert(rho.generator_images[(gi + n1) as int] =~= img);
                //  Expand inverse_word on single-element seq
                assert(img.drop_first() =~= Seq::<Symbol>::empty());
                assert(inverse_word(img.drop_first()) =~= empty_word());
                assert(inverse_symbol(img.first()) == Symbol::Inv(gi));
                let inv_img = inverse_word(img);
                assert(inv_img =~= empty_word() + Seq::new(1, |_j: int| Symbol::Inv(gi)));
                assert(inv_img =~= Seq::new(1, |_j: int| Symbol::Inv(gi)));
                assert(apply_hom_symbol(rho, ss) =~= inv_img);
                assert(Seq::new(1, |_j: int| Symbol::Inv(gi))
                    =~= Seq::new(1, |_j: int| s));
            },
        }

        //  apply_hom(rho, sw) = concat(apply_hom_symbol(rho, ss), apply_hom(rho, srest))
        //                     =~= concat([s], rest) =~= w
        assert(apply_hom_symbol(rho, ss) =~= Seq::new(1, |_j: int| s));
        assert(apply_hom(rho, sw) =~= concat(Seq::new(1, |_j: int| s), rest));
        assert(concat(Seq::new(1, |_j: int| s), rest) =~= w) by {
            let lhs = concat(Seq::new(1, |_j: int| s), rest);
            assert(lhs.len() == w.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == w[k] by {
                if k == 0 {
                } else {
                    assert(lhs[k] == rest[k - 1]);
                    assert(rest[k - 1] == w[k]);
                }
            }
        }
    }
}

///  For shifted G₂-words: apply_hom(right_rho, shift_word(w, n1)) =~= w.
pub proof fn lemma_fp_right_retraction_identity(
    p1: Presentation, p2: Presentation, w: Word,
)
    requires
        word_valid(w, p2.num_generators),
    ensures
        apply_hom(fp_right_retraction(p1, p2), shift_word(w, p1.num_generators)) =~= w,
{
    lemma_right_retraction_unshifts(p1, p2, w);
}

//  ============================================================
//  Main theorem: free product injectivity (right)
//  ============================================================

///  If w is a G₂-word and shift(w) ≡ ε in free_product(p1, p2), then w ≡ ε in p2.
pub proof fn lemma_free_product_injective_right(
    p1: Presentation, p2: Presentation, w: Word,
)
    requires
        presentation_valid(p1),
        presentation_valid(p2),
        word_valid(w, p2.num_generators),
        equiv_in_presentation(
            free_product(p1, p2),
            shift_word(w, p1.num_generators),
            empty_word(),
        ),
    ensures
        equiv_in_presentation(p2, w, empty_word()),
{
    let rho = fp_right_retraction(p1, p2);

    //  rho is a valid homomorphism
    lemma_fp_right_retraction_valid(p1, p2);

    //  rho preserves equivalence
    lemma_hom_preserves_equiv(rho, shift_word(w, p1.num_generators), empty_word());

    //  rho(shift(w)) =~= w
    lemma_fp_right_retraction_identity(p1, p2, w);

    //  rho(ε) =~= ε
    lemma_hom_empty(rho);
}

//  ============================================================
//  General form: two G₁-words equivalent in FP are equivalent in P₁
//  ============================================================

///  If w₁, w₂ are G₁-words and w₁ ≡ w₂ in FP, then w₁ ≡ w₂ in P₁.
pub proof fn lemma_free_product_reflects_left(
    p1: Presentation, p2: Presentation, w1: Word, w2: Word,
)
    requires
        presentation_valid(p1),
        presentation_valid(p2),
        word_valid(w1, p1.num_generators),
        word_valid(w2, p1.num_generators),
        equiv_in_presentation(free_product(p1, p2), w1, w2),
    ensures
        equiv_in_presentation(p1, w1, w2),
{
    let rho = fp_left_retraction(p1, p2);
    lemma_fp_left_retraction_valid(p1, p2);
    lemma_hom_preserves_equiv(rho, w1, w2);
    lemma_fp_left_retraction_identity(p1, p2, w1);
    lemma_fp_left_retraction_identity(p1, p2, w2);
}

} //  verus!


//  ================================================================
//  FILE: normal_form_amalgamated.rs
//  ================================================================

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::quotient::*;
use crate::reduction::*;
use crate::normal_form_free_product::*;
use crate::benign::*;

verus! {

//  ============================================================
//  Amalgamated Free Product — Structural Lemmas
//  ============================================================
//
//  Key structural property: free reductions NEVER cross factor boundaries.
//  is_inverse_pair requires the same generator index, and G₁ uses < n₁
//  while G₂ uses ≥ n₁.

//  ============================================================
//  Definitions
//  ============================================================

///  The identifications define an isomorphism between generated subgroups.
pub open spec fn identifications_isomorphic(data: AmalgamatedData) -> bool {
    let k = data.identifications.len();
    let a_words = Seq::new(k, |i: int| data.identifications[i].0);
    let b_words = Seq::new(k, |i: int| data.identifications[i].1);
    forall|w: Word| word_valid(w, k as nat) ==> (
        equiv_in_presentation(data.p1, apply_embedding(a_words, w), empty_word())
        <==>
        equiv_in_presentation(data.p2, apply_embedding(b_words, w), empty_word())
    )
}

///  A word is a "left word" (uses only G₁ generators).
pub open spec fn is_left_word(w: Word, n1: nat) -> bool {
    forall|k: int| 0 <= k < w.len() ==> generator_index(#[trigger] w[k]) < n1
}

//  ============================================================
//  add_relators structure
//  ============================================================

///  add_relators(p, rs).relators =~= p.relators + rs.
pub proof fn lemma_add_relators_concat(p: Presentation, rs: Seq<Word>)
    ensures
        add_relators(p, rs).relators =~= p.relators + rs,
    decreases rs.len(),
{
    if rs.len() == 0 {
        assert(add_relators(p, rs) == p);
        assert(p.relators + rs =~= p.relators);
    } else {
        let p1 = add_relator(p, rs.first());
        assert(p1.relators =~= p.relators.push(rs.first()));
        assert(p1.relators =~= p.relators + Seq::new(1, |_i: int| rs.first()));
        lemma_add_relators_concat(p1, rs.drop_first());
        assert((p.relators + Seq::new(1, |_i: int| rs.first())) + rs.drop_first()
            =~= p.relators + rs) by {
            let lhs = (p.relators + Seq::new(1, |_i: int| rs.first())) + rs.drop_first();
            let rhs = p.relators + rs;
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                if k < p.relators.len() {
                } else if k == p.relators.len() {
                    assert(lhs[k] == rs.first());
                    assert(rhs[k] == rs[0]);
                } else {
                    let j = (k - p.relators.len() - 1) as int;
                    assert(lhs[k] == rs.drop_first()[j]);
                    assert(rs.drop_first()[j] == rs[j + 1]);
                    assert(rhs[k] == rs[k - p.relators.len()]);
                }
            }
        }
    }
}

///  The AFP's relators are: fp.relators ++ amalgamation_relators(data).
pub proof fn lemma_afp_relators(data: AmalgamatedData)
    ensures
        amalgamated_free_product(data).relators =~=
            free_product(data.p1, data.p2).relators + amalgamation_relators(data),
{
    lemma_add_relators_concat(
        free_product(data.p1, data.p2),
        amalgamation_relators(data),
    );
}

//  ============================================================
//  Relator classification helpers
//  ============================================================

///  AFP relator at index < p1.relators.len() equals p1's relator.
pub proof fn lemma_afp_relator_g1(data: AmalgamatedData, idx: nat)
    requires idx < data.p1.relators.len(),
    ensures ({
        let afp = amalgamated_free_product(data);
        &&& idx < afp.relators.len()
        &&& afp.relators[idx as int] == data.p1.relators[idx as int]
    }),
{
    lemma_afp_relators(data);
    let fp = free_product(data.p1, data.p2);
    assert(fp.relators[idx as int] == data.p1.relators[idx as int]);
}

///  Shifted G₂ relators have all symbols with generator_index >= n1.
proof fn lemma_shifted_relator_has_g2(data: AmalgamatedData, g2_idx: nat)
    requires g2_idx < data.p2.relators.len(),
    ensures
        forall|k: int| 0 <= k < shift_word(data.p2.relators[g2_idx as int], data.p1.num_generators).len()
            ==> generator_index(
                #[trigger] shift_word(data.p2.relators[g2_idx as int], data.p1.num_generators)[k]
            ) >= data.p1.num_generators,
{
    let n1 = data.p1.num_generators;
    let r = data.p2.relators[g2_idx as int];
    let sr = shift_word(r, n1);
    assert forall|k: int| 0 <= k < sr.len()
        implies generator_index(#[trigger] sr[k]) >= n1
    by {
        assert(sr[k] == shift_symbol(r[k], n1));
        match r[k] {
            Symbol::Gen(gi) => { assert(generator_index(sr[k]) == gi + n1); },
            Symbol::Inv(gi) => { assert(generator_index(sr[k]) == gi + n1); },
        }
    }
}

///  If v_i non-empty, identification relator has a G₂ symbol.
proof fn lemma_ident_relator_has_g2_if_v_nonempty(
    data: AmalgamatedData, ident_idx: int,
)
    requires
        0 <= ident_idx < data.identifications.len(),
        data.identifications[ident_idx].1.len() > 0,
    ensures
        exists|k: int| 0 <= k < amalgamation_relator(data, ident_idx).len()
            && generator_index(amalgamation_relator(data, ident_idx)[k])
                >= data.p1.num_generators,
{
    let n1 = data.p1.num_generators;
    let (u_i, v_i) = data.identifications[ident_idx];
    let shifted_v = shift_word(v_i, n1);
    let inv_sv = inverse_word(shifted_v);
    let rel = amalgamation_relator(data, ident_idx);
    assert(rel == concat(u_i, inv_sv));
    lemma_inverse_word_len(shifted_v);
    lemma_inverse_word_last_is_inv_of_first(shifted_v);
    let last_idx = (inv_sv.len() - 1) as int;
    assert(inv_sv[last_idx] == inverse_symbol(shifted_v.first()));
    assert(shifted_v.first() == shift_symbol(v_i.first(), n1));
    match v_i.first() {
        Symbol::Gen(gi) => {
            assert(generator_index(inverse_symbol(shifted_v.first())) == gi + n1);
        },
        Symbol::Inv(gi) => {
            assert(generator_index(inverse_symbol(shifted_v.first())) == gi + n1);
        },
    }
    let pos = (u_i.len() as int) + last_idx;
    assert(rel[pos] == inv_sv[last_idx]) by {
        assert(concat(u_i, inv_sv)[pos] == inv_sv[last_idx]);
    }
}

///  inverse_word(w)[w.len()-1] == inverse_symbol(w.first()) when non-empty.
proof fn lemma_inverse_word_last_is_inv_of_first(w: Word)
    requires w.len() > 0,
    ensures
        inverse_word(w).len() == w.len(),
        inverse_word(w)[(w.len() - 1) as int] == inverse_symbol(w.first()),
{
    lemma_inverse_word_len(w);
    let inv_rest = inverse_word(w.drop_first());
    let inv_first_sym = inverse_symbol(w.first());
    let tail = Seq::new(1, |_i: int| inv_first_sym);
    assert(inverse_word(w) =~= inv_rest + tail);
    lemma_inverse_word_len(w.drop_first());
    assert((inv_rest + tail)[(w.len() - 1) as int] == tail[0]);
}

///  If w has a symbol with generator_index >= n, so does inverse_word(w).
proof fn lemma_inverse_preserves_gen_bound_lower(w: Word, n: nat)
    requires
        w.len() > 0,
        exists|k: int| 0 <= k < w.len() && generator_index(w[k]) >= n,
    ensures
        exists|k: int| 0 <= k < inverse_word(w).len()
            && generator_index(inverse_word(w)[k]) >= n,
    decreases w.len(),
{
    lemma_inverse_word_len(w);
    let first = w.first();
    let rest = w.drop_first();
    let inv_rest = inverse_word(rest);
    let inv_first = inverse_symbol(first);
    assert(inverse_word(w) =~= inv_rest + Seq::new(1, |_i: int| inv_first));

    if generator_index(first) >= n {
        assert(generator_index(inv_first) == generator_index(first));
        let pos = (inverse_word(w).len() - 1) as int;
        assert(inverse_word(w)[pos] == inv_first);
    } else {
        let k = choose|k: int| 0 <= k < w.len() && generator_index(w[k]) >= n;
        assert(k > 0);
        assert(rest[k - 1] == w[k]);
        assert(rest.len() > 0);
        lemma_inverse_preserves_gen_bound_lower(rest, n);
        lemma_inverse_word_len(rest);
        let k2 = choose|k2: int| 0 <= k2 < inv_rest.len()
            && generator_index(inv_rest[k2]) >= n;
        assert(inverse_word(w)[k2] == inv_rest[k2]);
    }
}

///  If v_i is empty, then u_i ≡ ε in G₁ (via isomorphism condition).
proof fn lemma_empty_v_means_u_trivial(
    data: AmalgamatedData, ident_idx: nat,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        ident_idx < data.identifications.len(),
        data.identifications[ident_idx as int].1.len() == 0,
    ensures
        equiv_in_presentation(data.p1, data.identifications[ident_idx as int].0, empty_word()),
{
    let k = data.identifications.len();
    let a_words = Seq::new(k, |i: int| data.identifications[i].0);
    let b_words = Seq::new(k, |i: int| data.identifications[i].1);
    let (u_i, v_i) = data.identifications[ident_idx as int];
    let gen_word = Seq::new(1, |_j: int| Symbol::Gen(ident_idx));

    assert(word_valid(gen_word, k as nat)) by {
        assert(symbol_valid(Symbol::Gen(ident_idx), k as nat));
    }

    assert(gen_word.first() == Symbol::Gen(ident_idx));
    assert(gen_word.drop_first() =~= Seq::<Symbol>::empty());
    assert(apply_embedding_symbol(b_words, Symbol::Gen(ident_idx)) == v_i);
    assert(apply_embedding(b_words, gen_word.drop_first()) =~= empty_word());
    assert(apply_embedding(b_words, gen_word) =~= concat(v_i, empty_word()));
    assert(v_i =~= empty_word());
    assert(apply_embedding(b_words, gen_word) =~= empty_word());
    lemma_equiv_refl(data.p2, empty_word());

    assert(apply_embedding_symbol(a_words, Symbol::Gen(ident_idx)) == u_i);
    assert(apply_embedding(a_words, gen_word)
        == concat(apply_embedding_symbol(a_words, gen_word.first()),
                  apply_embedding(a_words, gen_word.drop_first())));
    assert(apply_embedding(a_words, gen_word) =~= concat(u_i, empty_word()));
    assert(concat(u_i, empty_word()) =~= u_i);
    assert(apply_embedding(a_words, gen_word) =~= u_i);
}

//  ============================================================
//  Inverse of trivial is trivial (with proper preconditions)
//  ============================================================

///  If w ≡ ε and we have word_valid + presentation_valid, inverse_word(w) ≡ ε.
pub proof fn lemma_inverse_of_trivial(p: Presentation, w: Word)
    requires
        presentation_valid(p),
        word_valid(w, p.num_generators),
        equiv_in_presentation(p, w, empty_word()),
    ensures
        equiv_in_presentation(p, inverse_word(w), empty_word()),
{
    //  w ≡ ε, so by symmetry (needs word_valid + pres_valid): ε ≡ w
    lemma_equiv_symmetric(p, w, empty_word());
    //  concat(inv(w), ε) ≡ concat(inv(w), w)   (concat_right with ε ≡ w)
    lemma_equiv_concat_right(p, inverse_word(w), empty_word(), w);
    //  concat(inv(w), ε) =~= inv(w)
    assert(concat(inverse_word(w), empty_word()) =~= inverse_word(w));
    //  concat(inv(w), w) ≡ ε   (word_inverse_left)
    lemma_word_inverse_left(p, w);
    //  Chain: inv(w) =~= concat(inv(w), ε) ≡ concat(inv(w), w) ≡ ε
    lemma_equiv_transitive(p, concat(inverse_word(w), empty_word()),
        concat(inverse_word(w), w), empty_word());
    lemma_equiv_refl(p, inverse_word(w));
    lemma_equiv_transitive(p, inverse_word(w),
        concat(inverse_word(w), empty_word()), empty_word());
}

//  ============================================================
//  Insert/delete of trivial word preserves equivalence
//  ============================================================

///  Inserting r ≡ ε at position preserves equivalence.
///  Proves w ≡ (w[0..p] + r + w[p..]) by building w_prime → w (reducing r to ε)
///  then using symmetry.
proof fn lemma_insert_trivial_preserves_equiv(
    p: Presentation, w: Word, r: Word, position: int,
)
    requires
        presentation_valid(p),
        word_valid(w, p.num_generators),
        word_valid(r, p.num_generators),
        0 <= position <= w.len(),
        equiv_in_presentation(p, r, empty_word()),
    ensures
        equiv_in_presentation(
            p, w,
            w.subrange(0, position) + r + w.subrange(position, w.len() as int),
        ),
{
    let prefix = w.subrange(0, position);
    let suffix = w.subrange(position, w.len() as int);
    let w_prime = prefix + r + suffix;

    assert(w =~= prefix + suffix) by {
        assert((prefix + suffix).len() == w.len());
        assert forall|k: int| 0 <= k < w.len()
            implies (prefix + suffix)[k] == w[k]
        by { if k < position { } else { } }
    }

    //  Build: w_prime ≡ w (direction: derivation from w_prime to w)
    //  concat(r, suffix) ≡ concat(ε, suffix) =~= suffix
    lemma_equiv_concat_left(p, r, empty_word(), suffix);
    assert(concat(empty_word(), suffix) =~= suffix);
    lemma_equiv_refl(p, suffix);
    lemma_equiv_transitive(p, concat(r, suffix), concat(empty_word(), suffix), suffix);

    //  concat(prefix, concat(r, suffix)) ≡ concat(prefix, suffix)
    lemma_equiv_concat_right(p, prefix, concat(r, suffix), suffix);

    //  w_prime =~= concat(prefix, concat(r, suffix))
    assert(w_prime =~= concat(prefix, concat(r, suffix))) by {
        let lhs = prefix + r + suffix;
        let rhs = concat(prefix, concat(r, suffix));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < prefix.len() as int { }
            else if k < (prefix.len() + r.len()) as int {
                assert(lhs[k] == r[k - prefix.len()]);
                assert(concat(r, suffix)[k - prefix.len()] == r[k - prefix.len()]);
            } else {
                assert(lhs[k] == suffix[k - prefix.len() - r.len()]);
                assert(concat(r, suffix)[k - prefix.len()]
                    == suffix[k - prefix.len() - r.len()]);
            }
        }
    }

    //  w =~= concat(prefix, suffix)
    //  So: w_prime ≡ w (derivation from w_prime to w)
    //  Now use symmetry to get w ≡ w_prime.
    //  Need word_valid(w_prime, n) for symmetry.
    reveal(presentation_valid);
    assert(word_valid(w_prime, p.num_generators)) by {
        assert forall|k: int| 0 <= k < w_prime.len()
            implies symbol_valid(w_prime[k], p.num_generators)
        by {
            if k < prefix.len() as int {
                assert(w_prime[k] == prefix[k]);
                assert(prefix[k] == w[k]);
            } else if k < (prefix.len() + r.len()) as int {
                assert(w_prime[k] == r[k - prefix.len()]);
            } else {
                assert(w_prime[k] == suffix[k - prefix.len() - r.len()]);
                assert(suffix[k - prefix.len() - r.len()] == w[k - r.len()]);
            }
        }
    }
    lemma_equiv_symmetric(p, w_prime, w);
}

//  ============================================================
//  Non-G₁ AFP relator that's all-G₁ must be trivial in G₁
//  ============================================================

///  Any AFP relator at index >= p1.relators.len(), if all-G₁, is ≡ ε in G₁.
proof fn lemma_nonstandard_afp_relator_trivial(
    data: AmalgamatedData, relator_index: nat, inverted: bool,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        relator_index < amalgamated_free_product(data).relators.len(),
        relator_index >= data.p1.relators.len(),
        get_relator(amalgamated_free_product(data), relator_index, inverted).len() > 0,
        forall|k: int| 0 <= k < get_relator(amalgamated_free_product(data), relator_index, inverted).len()
            ==> generator_index(
                #[trigger] get_relator(amalgamated_free_product(data), relator_index, inverted)[k]
            ) < data.p1.num_generators,
    ensures
        equiv_in_presentation(
            data.p1,
            get_relator(amalgamated_free_product(data), relator_index, inverted),
            empty_word(),
        ),
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;
    let r = get_relator(afp, relator_index, inverted);
    let raw_rel = afp.relators[relator_index as int];
    let n_g1 = data.p1.relators.len();
    let n_g2 = data.p2.relators.len();

    lemma_afp_relators(data);

    //  Case: shifted G₂ relator — impossible (has G₂ symbols)
    if relator_index < n_g1 + n_g2 {
        let g2_idx = (relator_index - n_g1) as nat;
        lemma_shifted_relator_has_g2(data, g2_idx);
        let sr = shift_word(data.p2.relators[g2_idx as int], n1);
        assert(raw_rel == sr) by {
            let fp = free_product(data.p1, data.p2);
            assert(fp.relators[relator_index as int] ==
                shift_relators(data.p2.relators, n1)[g2_idx as int]);
        }
        if sr.len() > 0 {
            if !inverted {
                assert(r == raw_rel);
                assert(generator_index(r[0]) >= n1);
                assert(generator_index(r[0]) < n1);
            } else {
                lemma_inverse_preserves_gen_bound_lower(raw_rel, n1);
                let k2 = choose|k2: int| 0 <= k2 < inverse_word(raw_rel).len()
                    && generator_index(inverse_word(raw_rel)[k2]) >= n1;
                assert(r == inverse_word(raw_rel));
                assert(generator_index(r[k2]) >= n1);
                assert(generator_index(r[k2]) < n1);
            }
        }
        //  sr empty → raw_rel empty → r empty (contradicts r.len() > 0)
        assert(sr.len() == 0);
        assert(raw_rel.len() == 0);
        if !inverted { assert(r.len() == 0); }
        else { lemma_inverse_word_len(raw_rel); assert(r.len() == 0); }
        assert(false);
    }

    //  Case: identification relator
    let ident_idx = (relator_index - n_g1 - n_g2) as nat;
    assert(ident_idx < data.identifications.len()) by {
        let ident_rels = amalgamation_relators(data);
        let fp = free_product(data.p1, data.p2);
        assert(afp.relators.len() == fp.relators.len() + ident_rels.len());
        assert(fp.relators.len() == n_g1 + n_g2);
        assert(ident_rels.len() == data.identifications.len());
    }
    let (u_i, v_i) = data.identifications[ident_idx as int];
    let raw_ident = amalgamation_relator(data, ident_idx as int);

    assert(raw_rel == raw_ident) by {
        let fp = free_product(data.p1, data.p2);
        let ident_rels = amalgamation_relators(data);
        assert((fp.relators + ident_rels)[relator_index as int]
            == ident_rels[ident_idx as int]);
    }

    //  If v_i non-empty → contradiction (relator has G₂ symbol)
    if v_i.len() > 0 {
        lemma_ident_relator_has_g2_if_v_nonempty(data, ident_idx as int);
        let g2_k = choose|k: int| 0 <= k < raw_ident.len()
            && generator_index(raw_ident[k]) >= n1;
        if !inverted {
            assert(r == raw_rel);
            assert(generator_index(r[g2_k]) >= n1);
            assert(generator_index(r[g2_k]) < n1);
        } else {
            lemma_inverse_preserves_gen_bound_lower(raw_rel, n1);
            let k2 = choose|k2: int| 0 <= k2 < inverse_word(raw_rel).len()
                && generator_index(inverse_word(raw_rel)[k2]) >= n1;
            assert(r == inverse_word(raw_rel));
            assert(generator_index(r[k2]) >= n1);
            assert(generator_index(r[k2]) < n1);
        }
        assert(false);
    }

    //  v_i empty → u_i ≡ ε in G₁
    lemma_empty_v_means_u_trivial(data, ident_idx);

    assert(v_i =~= empty_word());
    assert(shift_word(v_i, n1) =~= empty_word());
    assert(inverse_word(shift_word(v_i, n1)) =~= empty_word());
    assert(raw_ident =~= concat(u_i, empty_word()));
    assert(raw_ident =~= u_i);
    assert(raw_rel =~= u_i);

    if !inverted {
        assert(r == raw_rel);
    } else {
        //  r = inverse_word(u_i), u_i ≡ ε, need inverse_word(u_i) ≡ ε
        //  u_i is word_valid (from amalgamated_data_valid) and p1 is presentation_valid
        reveal(presentation_valid);
        assert(word_valid(u_i, n1));
        assert(presentation_valid(data.p1));
        lemma_inverse_of_trivial(data.p1, u_i);
        assert(r == inverse_word(raw_rel));
    }
}

//  ============================================================
//  Left-to-left steps are G₁ steps
//  ============================================================

///  KEY LEMMA: If both w and w' are left words and the AFP step takes w to w',
///  then w ≡ w' in G₁.
pub proof fn lemma_left_step_valid_in_g1(
    data: AmalgamatedData,
    w: Word, step: DerivationStep, w_prime: Word,
)
    requires
        amalgamated_data_valid(data),
        identifications_isomorphic(data),
        apply_step(amalgamated_free_product(data), w, step) == Some(w_prime),
        is_left_word(w, data.p1.num_generators),
        is_left_word(w_prime, data.p1.num_generators),
    ensures
        equiv_in_presentation(data.p1, w, w_prime),
{
    let afp = amalgamated_free_product(data);
    let n1 = data.p1.num_generators;

    match step {
        DerivationStep::FreeReduce { position } => {
            let s = DerivationStep::FreeReduce { position };
            assert(apply_step(data.p1, w, s) == Some(w_prime));
            let steps = Seq::new(1, |_i: int| s);
            assert(derivation_produces(data.p1, steps.drop_first(), w_prime) == Some(w_prime));
            assert(derivation_produces(data.p1, steps, w) == Some(w_prime));
            let d = Derivation { steps };
            assert(derivation_valid(data.p1, d, w, w_prime));
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let pair = Seq::new(1, |_i: int| symbol)
                + Seq::new(1, |_i: int| inverse_symbol(symbol));
            assert(w_prime =~= w.subrange(0, position) + pair
                + w.subrange(position, w.len() as int));
            assert(w_prime[position] == symbol);
            assert(generator_index(symbol) < n1);
            assert(symbol_valid(symbol, n1));
            let s = DerivationStep::FreeExpand { position, symbol };
            assert(apply_step(data.p1, w, s) == Some(w_prime));
            let steps = Seq::new(1, |_i: int| s);
            assert(derivation_produces(data.p1, steps.drop_first(), w_prime) == Some(w_prime));
            assert(derivation_produces(data.p1, steps, w) == Some(w_prime));
            let d = Derivation { steps };
            assert(derivation_valid(data.p1, d, w, w_prime));
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let r = get_relator(afp, relator_index, inverted);
            assert(w_prime =~= w.subrange(0, position) + r
                + w.subrange(position, w.len() as int));
            assert forall|k: int| 0 <= k < r.len()
                implies generator_index(#[trigger] r[k]) < n1
            by { assert(w_prime[position + k] == r[k]); }

            lemma_afp_relators(data);

            if relator_index < data.p1.relators.len() {
                lemma_afp_relator_g1(data, relator_index);
                assert(get_relator(afp, relator_index, inverted)
                    == get_relator(data.p1, relator_index, inverted));
                let s = DerivationStep::RelatorInsert { position, relator_index, inverted };
                assert(apply_step(data.p1, w, s) == Some(w_prime));
                let steps = Seq::new(1, |_i: int| s);
                assert(derivation_produces(data.p1, steps.drop_first(), w_prime) == Some(w_prime));
                assert(derivation_produces(data.p1, steps, w) == Some(w_prime));
                let d = Derivation { steps };
                assert(derivation_valid(data.p1, d, w, w_prime));
            } else if r.len() == 0 {
                assert(w_prime =~= w);
                lemma_equiv_refl(data.p1, w);
            } else {
                lemma_nonstandard_afp_relator_trivial(data, relator_index, inverted);
                lemma_insert_trivial_preserves_equiv(data.p1, w, r, position);
            }
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let r = get_relator(afp, relator_index, inverted);
            let rlen = r.len();
            assert forall|k: int| 0 <= k < r.len()
                implies generator_index(#[trigger] r[k]) < n1
            by { assert(r[k] == w[position + k]); }

            lemma_afp_relators(data);

            if relator_index < data.p1.relators.len() {
                lemma_afp_relator_g1(data, relator_index);
                assert(get_relator(afp, relator_index, inverted)
                    == get_relator(data.p1, relator_index, inverted));
                let s = DerivationStep::RelatorDelete { position, relator_index, inverted };
                assert(apply_step(data.p1, w, s) == Some(w_prime));
                let steps = Seq::new(1, |_i: int| s);
                assert(derivation_produces(data.p1, steps.drop_first(), w_prime) == Some(w_prime));
                assert(derivation_produces(data.p1, steps, w) == Some(w_prime));
                let d = Derivation { steps };
                assert(derivation_valid(data.p1, d, w, w_prime));
            } else if r.len() == 0 {
                assert(w_prime =~= w);
                lemma_equiv_refl(data.p1, w);
            } else {
                lemma_nonstandard_afp_relator_trivial(data, relator_index, inverted);
                //  r ≡ ε in G₁. w = prefix + r + suffix, w_prime = prefix + suffix.
                //  Need w ≡ w_prime. Since r ≡ ε: w = prefix + r + suffix ≡ prefix + suffix = w_prime.
                let prefix = w.subrange(0, position);
                let suffix = w.subrange(position + rlen as int, w.len() as int);

                //  concat(r, suffix) ≡ suffix
                lemma_equiv_concat_left(data.p1, r, empty_word(), suffix);
                assert(concat(empty_word(), suffix) =~= suffix);
                lemma_equiv_refl(data.p1, suffix);
                lemma_equiv_transitive(data.p1, concat(r, suffix),
                    concat(empty_word(), suffix), suffix);

                //  prefix + concat(r, suffix) ≡ prefix + suffix = w_prime
                lemma_equiv_concat_right(data.p1, prefix, concat(r, suffix), suffix);

                //  w =~= concat(prefix, concat(r, suffix))
                assert(w =~= concat(prefix, concat(r, suffix))) by {
                    let lhs = w;
                    let rhs = concat(prefix, concat(r, suffix));
                    assert(lhs.len() == rhs.len()) by {
                        assert(prefix.len() == position);
                        assert(suffix.len() == w.len() - position - rlen);
                    }
                    assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                        if k < position { }
                        else if k < position + rlen as int {
                            assert(lhs[k] == w[k]);
                            assert(w.subrange(position, position + rlen as int) == r);
                            assert(w[k] == r[k - position]);
                            assert(concat(r, suffix)[k - position] == r[k - position]);
                        } else {
                            assert(lhs[k] == w[k]);
                            assert(suffix[k - position - rlen] == w[k]);
                            assert(concat(r, suffix)[k - position]
                                == suffix[k - position - rlen]);
                        }
                    }
                }

                assert(w_prime =~= concat(prefix, suffix));
            }
        },
    }
}

//  ============================================================
//  Part F: Van der Waerden action — state and action definitions
//  ============================================================
//
//  The action is on states (h, syllables) where:
//    h: Word — an element of A (the amalgamated subgroup in G₁)
//    syllables: Seq<(bool, nat)> — alternating (is_left, coset_index) pairs
//      is_left = true means the syllable is from G₁/A
//      is_left = false means the syllable is from G₂/B
//      Each coset_index represents a non-trivial coset (different from the subgroup coset)
//
//  The action of a G₁-symbol on a state processes through the coset structure.
//  The action of a G₂-symbol similarly.
//  Well-definedness means AFP-equivalent words act the same (up to G₁-equiv of h).

///  A word is in the left amalgamated subgroup A (generated by u_i words).
pub open spec fn in_left_subgroup(data: AmalgamatedData, w: Word) -> bool {
    let k = data.identifications.len();
    let a_words = Seq::new(k, |i: int| data.identifications[i].0);
    in_generated_subgroup(data.p1, a_words, w)
}

///  A word is in the right amalgamated subgroup B (generated by v_i words).
pub open spec fn in_right_subgroup(data: AmalgamatedData, w: Word) -> bool {
    let k = data.identifications.len();
    let b_words = Seq::new(k, |i: int| data.identifications[i].1);
    in_generated_subgroup(data.p2, b_words, w)
}

///  Two G₁-words are in the same A-coset: w₁⁻¹ · w₂ ∈ A.
pub open spec fn same_left_coset(data: AmalgamatedData, w1: Word, w2: Word) -> bool {
    in_left_subgroup(data, concat(inverse_word(w1), w2))
}

///  Two G₂-words are in the same B-coset.
pub open spec fn same_right_coset(data: AmalgamatedData, w1: Word, w2: Word) -> bool {
    in_right_subgroup(data, concat(inverse_word(w1), w2))
}


//  ============================================================
//  Part G: H-only VDW action (no syllables)
//  ============================================================
//
//  For AFP injectivity, we only need the h-component of the VDW state.
//  The h-only action tracks a single nat (ct1 Cayley table element).
//
//  G₁ symbol s: h → ct1.table[h][sym_col(s)]  (trace in G₁)
//  G₂ symbol s: h → phi(ct2.table[phi_inv(h)][sym_col(unshift(s))])
//               (translate to G₂, trace, translate back)
//
//  This is the "H-projection" of the full VDW action. It's sufficient for
//  injectivity because for G₁-words on h=0, it equals trace_word(ct1, 0, w).

///  Lookup in a Cayley table: ct.table[elem][col], defaulting to 0.
pub open spec fn ct_lookup(
    ct: crate::todd_coxeter::CosetTable, elem: nat, col: nat,
) -> nat {
    match ct.table[elem as int][col as int] {
        Some(next) => next,
        None => 0,
    }
}

///  symbol_to_column shorthand.
pub open spec fn sym_col(s: Symbol) -> nat {
    crate::todd_coxeter::symbol_to_column(s)
}

///  Unshift a G₂ symbol.
pub open spec fn unshift_sym(s: Symbol, n1: nat) -> Symbol {
    match s {
        Symbol::Gen(i) => Symbol::Gen((i - n1) as nat),
        Symbol::Inv(i) => Symbol::Inv((i - n1) as nat),
    }
}


} //  verus!


//  ================================================================
//  FILE: normal_form_afp_textbook.rs
//  ================================================================

//  Textbook AFP injectivity via reduced sequences (Lyndon-Schupp Ch. IV).
//
//  Phase 1: Definitions only. All spec fns, no proof obligations.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::normal_form_amalgamated::{
    in_left_subgroup, in_right_subgroup,
    same_left_coset, same_right_coset,
    unshift_sym,
    identifications_isomorphic,
};
use crate::benign::*;
use crate::shortlex::*;

verus! {

//  ============================================================
//  Part A: Helpers
//  ============================================================

///  The K-word generators for the left factor (u_i words).
pub open spec fn a_words(data: AmalgamatedData) -> Seq<Word> {
    Seq::new(data.identifications.len(), |i: int| data.identifications[i].0)
}

///  The K-word generators for the right factor (v_i words).
pub open spec fn b_words(data: AmalgamatedData) -> Seq<Word> {
    Seq::new(data.identifications.len(), |i: int| data.identifications[i].1)
}

///  Number of identification generators.
pub open spec fn k_size(data: AmalgamatedData) -> nat {
    data.identifications.len() as nat
}

//  ============================================================
//  Part B: Shortlex-canonical coset representatives
//  ============================================================

///  Lex rank of a word with explicit base (alphabet size).
///  For word_valid(w, n): each symbol_to_column < 2*n.
///  With base = 2*n: this is a standard base-(2n) representation, injective on same-length words.
pub open spec fn word_lex_rank(w: Word) -> nat
    decreases w.len(),
{
    if w.len() == 0 { 0 }
    else {
        //  Use the word itself to provide a stable base.
        //  For proper injectivity, use word_lex_rank_base with explicit base.
        crate::todd_coxeter::symbol_to_column(w.first())
            + (2 * w.len() as nat) * word_lex_rank(w.drop_first())
    }
}

///  Lex rank with explicit base for injectivity proof.
pub open spec fn word_lex_rank_base(w: Word, base: nat) -> nat
    decreases w.len(),
{
    if w.len() == 0 { 0 }
    else {
        crate::todd_coxeter::symbol_to_column(w.first())
            + base * word_lex_rank_base(w.drop_first(), base)
    }
}

///  Lex rank with proper base is injective on same-length words.
proof fn lemma_word_lex_rank_base_injective(w1: Word, w2: Word, base: nat)
    requires
        w1.len() == w2.len(),
        word_lex_rank_base(w1, base) == word_lex_rank_base(w2, base),
        //  Each symbol's column < base (ensures proper base-n representation)
        forall|k: int| 0 <= k < w1.len() ==>
            crate::todd_coxeter::symbol_to_column(#[trigger] w1[k]) < base,
        forall|k: int| 0 <= k < w2.len() ==>
            crate::todd_coxeter::symbol_to_column(#[trigger] w2[k]) < base,
        base > 0,
    ensures
        w1 =~= w2,
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(w2.len() == 0);
        assert forall|k: int| 0 <= k < w1.len() implies w1[k] == w2[k] by {}
        return;
    } else {
        let col1 = crate::todd_coxeter::symbol_to_column(w1.first());
        let col2 = crate::todd_coxeter::symbol_to_column(w2.first());
        let rest_rank1 = word_lex_rank_base(w1.drop_first(), base);
        let rest_rank2 = word_lex_rank_base(w2.drop_first(), base);
        //  col1 + base * rest_rank1 == col2 + base * rest_rank2
        //  col1 < base, col2 < base. So col1 == (total) % base and rest_rank1 == (total) / base.
        //  col1 == col2 (mod base) and rest_rank1 == rest_rank2 (div base).
        assert(col1 < base);
        assert(col2 < base);
        //  col1 + base * rest1 == col2 + base * rest2
        //  → col1 - col2 == base * (rest2 - rest1)
        //  |col1 - col2| < base, |base * (rest2 - rest1)| is 0 or >= base
        //  So col1 == col2 and rest1 == rest2.
        assert(col1 == col2) by (nonlinear_arith)
            requires col1 + base * rest_rank1 == col2 + base * rest_rank2,
                     col1 < base, col2 < base;
        //  col1 == col2, so base * rest1 == base * rest2, so rest1 == rest2 (since base > 0)
        assert(base * rest_rank1 == base * rest_rank2) by (nonlinear_arith)
            requires col1 + base * rest_rank1 == col2 + base * rest_rank2,
                     col1 == col2;
        assert(rest_rank1 == rest_rank2) by (nonlinear_arith)
            requires base * rest_rank1 == base * rest_rank2, base > 0;
        //  col1 == col2 → w1.first() == w2.first() (symbol_to_column is injective on symbols)
        //  rest_rank1 == rest_rank2 → w1.rest =~= w2.rest (by IH)
        assert forall|k: int| 0 <= k < w1.drop_first().len()
            implies crate::todd_coxeter::symbol_to_column(#[trigger] w1.drop_first()[k]) < base
        by { assert(w1.drop_first()[k] == w1[k + 1]); }
        assert forall|k: int| 0 <= k < w2.drop_first().len()
            implies crate::todd_coxeter::symbol_to_column(#[trigger] w2.drop_first()[k]) < base
        by { assert(w2.drop_first()[k] == w2[k + 1]); }
        lemma_word_lex_rank_base_injective(w1.drop_first(), w2.drop_first(), base);
        //  w1.first() == w2.first(): from col1 == col2.
        //  symbol_to_column is injective: Gen(i) → 2*i, Inv(i) → 2*i+1. Different symbols → different columns.
        match w1.first() {
            Symbol::Gen(i1) => match w2.first() {
                Symbol::Gen(i2) => { assert(2 * i1 == 2 * i2); }
                Symbol::Inv(i2) => { assert(2 * i1 == 2 * i2 + 1); } //  impossible since even ≠ odd
            }
            Symbol::Inv(i1) => match w2.first() {
                Symbol::Gen(i2) => { assert(2 * i1 + 1 == 2 * i2); } //  impossible
                Symbol::Inv(i2) => { assert(2 * i1 + 1 == 2 * i2 + 1); }
            }
        }
        //  w1.first() == w2.first() and w1.drop_first() =~= w2.drop_first() → w1 =~= w2
        assert forall|k: int| 0 <= k < w1.len() implies w1[k] == w2[k] by {
            if k == 0 {} else { assert(w1[k] == w1.drop_first()[k - 1]); assert(w2[k] == w2.drop_first()[k - 1]); }
        }
    }
}

///  Does the left A-coset of g contain a valid word of length l?
pub open spec fn has_left_coset_word_of_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g, w) && w.len() == l
}

///  The lex base for a given alphabet: 2*n + 1 ensures injectivity.
pub open spec fn lex_base(data: AmalgamatedData) -> nat {
    2 * data.p1.num_generators + 1
}

///  Does the coset contain a valid word of length l and lex rank r?
pub open spec fn has_left_coset_word_of_len_rank(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g, w) && w.len() == l
        && word_lex_rank_base(w, lex_base(data)) == r
}

///  No coset word exists below length l (named recursive, avoids lambda issues).
pub open spec fn no_shorter_coset_word(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool
    decreases l,
{
    if l == 0 { true }
    else { !has_left_coset_word_of_len(data, g, (l - 1) as nat)
           && no_shorter_coset_word(data, g, (l - 1) as nat) }
}

///  l is the minimum coset length: has a word AND nothing shorter.
pub open spec fn is_min_coset_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    has_left_coset_word_of_len(data, g, l) && no_shorter_coset_word(data, g, l)
}

///  Minimum length of any valid word in g's left A-coset.
pub open spec fn left_min_coset_len(data: AmalgamatedData, g: Word) -> nat {
    choose|l: nat| #[trigger] is_min_coset_len(data, g, l)
}

///  No coset word exists at length l with lex rank below r (named recursive).
pub open spec fn no_smaller_coset_lex(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool
    decreases r,
{
    if r == 0 { true }
    else { !has_left_coset_word_of_len_rank(data, g, l, (r - 1) as nat)
           && no_smaller_coset_lex(data, g, l, (r - 1) as nat) }
}

///  r is the minimum lex rank at length l.
pub open spec fn is_min_coset_lex(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool {
    has_left_coset_word_of_len_rank(data, g, l, r)
    && no_smaller_coset_lex(data, g, l, r)
}

///  Minimum lex rank at the minimum length.
pub open spec fn left_min_coset_lex(data: AmalgamatedData, g: Word) -> nat {
    let l = left_min_coset_len(data, g);
    choose|r: nat| #[trigger] is_min_coset_lex(data, g, l, r)
}

///  Canonical coset representative: the UNIQUE word with min length and min lex rank.
///  Three-step choose enables coset invariance via uniqueness.
pub open spec fn left_canonical_rep(data: AmalgamatedData, g: Word) -> Word {
    let l = left_min_coset_len(data, g);
    let r = left_min_coset_lex(data, g);
    choose|rep: Word|
        word_valid(rep, data.p1.num_generators)
        && same_left_coset(data, g, rep)
        && rep.len() == l
        && word_lex_rank_base(rep, lex_base(data)) == r
}

///  Does a K-word of length l exist that embeds to the target?
pub open spec fn has_left_h_witness_of_len(
    data: AmalgamatedData, target: Word, l: nat,
) -> bool {
    exists|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h), target)
}

///  Min-length K-word witnessing the subgroup decomposition.
pub open spec fn left_h_min_len(data: AmalgamatedData, g: Word) -> nat {
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    choose|l: nat| #[trigger] has_left_h_witness_of_len(data, target, l)
        && no_pred_below(|l2: nat| has_left_h_witness_of_len(data, target, l2), l)
}

///  The lex base for K-words: 2*k + 1 ensures injectivity.
pub open spec fn h_lex_base(data: AmalgamatedData) -> nat {
    2 * k_size(data) + 1
}

///  Does a K-word of length l and lex rank r exist that embeds to the target?
pub open spec fn has_left_h_witness_of_len_rank(
    data: AmalgamatedData, target: Word, l: nat, r: nat,
) -> bool {
    exists|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && word_lex_rank_base(h, h_lex_base(data)) == r
        && equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h), target)
}

///  No h-witness exists at length l with lex rank below r (named recursive).
pub open spec fn no_smaller_h_lex(
    data: AmalgamatedData, target: Word, l: nat, r: nat,
) -> bool
    decreases r,
{
    if r == 0 { true }
    else { !has_left_h_witness_of_len_rank(data, target, l, (r - 1) as nat)
           && no_smaller_h_lex(data, target, l, (r - 1) as nat) }
}

///  r is the minimum h-witness lex rank at length l.
pub open spec fn is_min_h_lex(
    data: AmalgamatedData, target: Word, l: nat, r: nat,
) -> bool {
    has_left_h_witness_of_len_rank(data, target, l, r)
    && no_smaller_h_lex(data, target, l, r)
}

///  Minimum lex rank among K-words of minimum length.
pub open spec fn left_h_min_lex(data: AmalgamatedData, g: Word) -> nat {
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    let l = left_h_min_len(data, g);
    choose|r: nat| #[trigger] is_min_h_lex(data, target, l, r)
}

///  The subgroup part: canonical (min-length, min-lex) K-word h such that embed_a(h) ≡ inv(rep) * g.
///  Three-step choose enables h-part invariance under G₁-equivalence.
pub open spec fn left_h_part(data: AmalgamatedData, g: Word) -> Word {
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    let l = left_h_min_len(data, g);
    let r = left_h_min_lex(data, g);
    choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && word_lex_rank_base(h, h_lex_base(data)) == r
        && equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h), target)
}

///  Does the right B-coset of g contain a valid word of length l?
pub open spec fn has_right_coset_word_of_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p2.num_generators)
        && same_right_coset(data, g, w) && w.len() == l
}

///  Minimum length of any valid word in g's right B-coset.
pub open spec fn right_min_coset_len(data: AmalgamatedData, g: Word) -> nat {
    choose|l: nat| #[trigger] has_right_coset_word_of_len(data, g, l)
        && no_pred_below(|l2: nat| has_right_coset_word_of_len(data, g, l2), l)
}

///  Canonical right coset representative.
pub open spec fn right_canonical_rep(data: AmalgamatedData, g: Word) -> Word {
    let l = right_min_coset_len(data, g);
    choose|rep: Word|
        word_valid(rep, data.p2.num_generators)
        && same_right_coset(data, g, rep)
        && rep.len() == l
}

///  Does a K-word of length l exist for the right decomposition?
pub open spec fn has_right_h_witness_of_len(
    data: AmalgamatedData, target: Word, l: nat,
) -> bool {
    exists|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h), target)
}

///  Min-length K-word for right decomposition.
pub open spec fn right_h_min_len(data: AmalgamatedData, g: Word) -> nat {
    let rep = right_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    choose|l: nat| #[trigger] has_right_h_witness_of_len(data, target, l)
        && no_pred_below(|l2: nat| has_right_h_witness_of_len(data, target, l2), l)
}

///  The subgroup part for G₂: min-length K-word.
pub open spec fn right_h_part(data: AmalgamatedData, g: Word) -> Word {
    let rep = right_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    let l = right_h_min_len(data, g);
    choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h), target)
}

//  ============================================================
//  Part B1c: RIGHT cosets of A in G₁ (textbook Lyndon-Schupp convention)
//  ============================================================
//  The textbook decomposes g = h·c where h ∈ A (on LEFT) and c is a RIGHT
//  coset representative (on RIGHT). This means g·c⁻¹ ∈ A.
//  Using this convention, the action has clean inverse cancellation:
//    s⁻¹ · (embed_a(h') · c') = s⁻¹ · (s · h · c₁) = h · c₁

///  Two G₁-words are in the same RIGHT coset of A: w₁·w₂⁻¹ ∈ A.
pub open spec fn same_a_rcoset(data: AmalgamatedData, w1: Word, w2: Word) -> bool {
    in_left_subgroup(data, concat(w1, inverse_word(w2)))
}

///  Does the right A-coset of g contain a valid word of length l?
pub open spec fn has_a_rcoset_word_of_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p1.num_generators)
        && same_a_rcoset(data, g, w) && w.len() == l
}

///  No right-A-coset word below length l (named recursive).
pub open spec fn no_shorter_a_rcoset_word(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool
    decreases l,
{
    if l == 0 { true }
    else { !has_a_rcoset_word_of_len(data, g, (l - 1) as nat)
           && no_shorter_a_rcoset_word(data, g, (l - 1) as nat) }
}

///  l is the minimum right-A-coset length.
pub open spec fn is_min_a_rcoset_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    has_a_rcoset_word_of_len(data, g, l) && no_shorter_a_rcoset_word(data, g, l)
}

///  Minimum right-A-coset length.
pub open spec fn a_rcoset_min_len(data: AmalgamatedData, g: Word) -> nat {
    choose|l: nat| #[trigger] is_min_a_rcoset_len(data, g, l)
}

///  Right-A-coset word of length l and lex rank r.
pub open spec fn has_a_rcoset_word_of_len_rank(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p1.num_generators)
        && same_a_rcoset(data, g, w) && w.len() == l
        && word_lex_rank_base(w, lex_base(data)) == r
}

///  No right-A-coset word at length l with lex rank below r.
pub open spec fn no_smaller_a_rcoset_lex(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool
    decreases r,
{
    if r == 0 { true }
    else { !has_a_rcoset_word_of_len_rank(data, g, l, (r - 1) as nat)
           && no_smaller_a_rcoset_lex(data, g, l, (r - 1) as nat) }
}

///  r is the minimum right-A-coset lex rank at length l.
pub open spec fn is_min_a_rcoset_lex(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool {
    has_a_rcoset_word_of_len_rank(data, g, l, r)
    && no_smaller_a_rcoset_lex(data, g, l, r)
}

///  Minimum lex rank at the minimum length for right A-coset.
pub open spec fn a_rcoset_min_lex(data: AmalgamatedData, g: Word) -> nat {
    let l = a_rcoset_min_len(data, g);
    choose|r: nat| #[trigger] is_min_a_rcoset_lex(data, g, l, r)
}

///  Canonical right A-coset representative (textbook: c in g = h·c).
///  Three-step choose: min length, min lex rank, unique word.
pub open spec fn a_rcoset_rep(data: AmalgamatedData, g: Word) -> Word {
    let l = a_rcoset_min_len(data, g);
    let r = a_rcoset_min_lex(data, g);
    choose|rep: Word|
        word_valid(rep, data.p1.num_generators)
        && same_a_rcoset(data, g, rep)
        && rep.len() == l
        && word_lex_rank_base(rep, lex_base(data)) == r
}

///  Min-length K-word for right-coset h-part.
///  Target = g · inv(rep) (textbook: h = g · c⁻¹).
///  Reuses has_left_h_witness_of_len since the predicate structure is identical.
pub open spec fn a_rcoset_h_min_len(data: AmalgamatedData, g: Word) -> nat {
    let rep = a_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    choose|l: nat| #[trigger] has_left_h_witness_of_len(data, target, l)
        && no_pred_below(|l2: nat| has_left_h_witness_of_len(data, target, l2), l)
}

///  Min lex rank for right-coset h-part.
pub open spec fn a_rcoset_h_min_lex(data: AmalgamatedData, g: Word) -> nat {
    let rep = a_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    let l = a_rcoset_h_min_len(data, g);
    choose|r: nat| #[trigger] is_min_h_lex(data, target, l, r)
}

///  The textbook h-part: canonical K-word h such that embed_a(h) ≡ g · c⁻¹.
///  Three-step choose for invariance under G₁-equivalence.
pub open spec fn a_rcoset_h(data: AmalgamatedData, g: Word) -> Word {
    let rep = a_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    let l = a_rcoset_h_min_len(data, g);
    let r = a_rcoset_h_min_lex(data, g);
    choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && word_lex_rank_base(h, h_lex_base(data)) == r
        && equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h), target)
}

//  ============================================================
//  Part B1d: RIGHT cosets of B in G₂ (textbook convention, mirrors A-cosets)
//  ============================================================

///  Two G₂-words in same RIGHT B-coset: w₁·w₂⁻¹ ∈ B.
pub open spec fn same_b_rcoset(data: AmalgamatedData, w1: Word, w2: Word) -> bool {
    in_right_subgroup(data, concat(w1, inverse_word(w2)))
}

pub open spec fn has_b_rcoset_word_of_len(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p2.num_generators)
        && same_b_rcoset(data, g, w) && w.len() == l
}

pub open spec fn no_shorter_b_rcoset_word(
    data: AmalgamatedData, g: Word, l: nat,
) -> bool
    decreases l,
{
    if l == 0 { true }
    else { !has_b_rcoset_word_of_len(data, g, (l - 1) as nat)
           && no_shorter_b_rcoset_word(data, g, (l - 1) as nat) }
}

pub open spec fn is_min_b_rcoset_len(data: AmalgamatedData, g: Word, l: nat) -> bool {
    has_b_rcoset_word_of_len(data, g, l) && no_shorter_b_rcoset_word(data, g, l)
}

pub open spec fn b_rcoset_min_len(data: AmalgamatedData, g: Word) -> nat {
    choose|l: nat| #[trigger] is_min_b_rcoset_len(data, g, l)
}

pub open spec fn has_b_rcoset_word_of_len_rank(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool {
    exists|w: Word| word_valid(w, data.p2.num_generators)
        && same_b_rcoset(data, g, w) && w.len() == l
        && word_lex_rank_base(w, 2 * data.p2.num_generators + 1) == r
}

pub open spec fn no_smaller_b_rcoset_lex(
    data: AmalgamatedData, g: Word, l: nat, r: nat,
) -> bool
    decreases r,
{
    if r == 0 { true }
    else { !has_b_rcoset_word_of_len_rank(data, g, l, (r - 1) as nat)
           && no_smaller_b_rcoset_lex(data, g, l, (r - 1) as nat) }
}

pub open spec fn is_min_b_rcoset_lex(data: AmalgamatedData, g: Word, l: nat, r: nat) -> bool {
    has_b_rcoset_word_of_len_rank(data, g, l, r)
    && no_smaller_b_rcoset_lex(data, g, l, r)
}

pub open spec fn b_rcoset_min_lex(data: AmalgamatedData, g: Word) -> nat {
    let l = b_rcoset_min_len(data, g);
    choose|r: nat| #[trigger] is_min_b_rcoset_lex(data, g, l, r)
}

///  Canonical right B-coset representative (textbook: c in g = h·c for G₂).
pub open spec fn b_rcoset_rep(data: AmalgamatedData, g: Word) -> Word {
    let l = b_rcoset_min_len(data, g);
    let r = b_rcoset_min_lex(data, g);
    choose|rep: Word|
        word_valid(rep, data.p2.num_generators)
        && same_b_rcoset(data, g, rep)
        && rep.len() == l
        && word_lex_rank_base(rep, 2 * data.p2.num_generators + 1) == r
}

///  G₂ h-witness with lex rank (uses p2/b_words instead of p1/a_words).
pub open spec fn has_right_h_witness_of_len_rank(
    data: AmalgamatedData, target: Word, l: nat, r: nat,
) -> bool {
    exists|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && word_lex_rank_base(h, h_lex_base(data)) == r
        && equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h), target)
}

///  No G₂ h-witness at length l with lex rank below r.
pub open spec fn no_smaller_h_lex_g2(
    data: AmalgamatedData, target: Word, l: nat, r: nat,
) -> bool
    decreases r,
{
    if r == 0 { true }
    else { !has_right_h_witness_of_len_rank(data, target, l, (r - 1) as nat)
           && no_smaller_h_lex_g2(data, target, l, (r - 1) as nat) }
}

pub open spec fn is_min_h_lex_g2(
    data: AmalgamatedData, target: Word, l: nat, r: nat,
) -> bool {
    has_right_h_witness_of_len_rank(data, target, l, r)
    && no_smaller_h_lex_g2(data, target, l, r)
}

///  Scan for min G₂ h-lex rank.
proof fn lemma_scan_min_h_lex_g2(
    data: AmalgamatedData, target: Word, l: nat, current: nat, bound: nat,
)
    requires
        has_right_h_witness_of_len_rank(data, target, l, bound),
        current <= bound,
        no_smaller_h_lex_g2(data, target, l, current),
    ensures
        exists|r: nat| current <= r && r <= bound
            && #[trigger] is_min_h_lex_g2(data, target, l, r),
    decreases bound - current,
{
    if has_right_h_witness_of_len_rank(data, target, l, current) {
        assert(is_min_h_lex_g2(data, target, l, current));
    } else {
        lemma_scan_min_h_lex_g2(data, target, l, current + 1, bound);
    }
}

///  Right B-coset h-part: target = g · inv(rep).
pub open spec fn b_rcoset_h_min_len(data: AmalgamatedData, g: Word) -> nat {
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    choose|l: nat| #[trigger] has_right_h_witness_of_len(data, target, l)
        && no_pred_below(|l2: nat| has_right_h_witness_of_len(data, target, l2), l)
}

pub open spec fn b_rcoset_h_min_lex(data: AmalgamatedData, g: Word) -> nat {
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    let l = b_rcoset_h_min_len(data, g);
    choose|r: nat| #[trigger] is_min_h_lex_g2(data, target, l, r)
}

///  The textbook h-part for G₂: canonical K-word h such that embed_b(h) ≡ g · c⁻¹.
pub open spec fn b_rcoset_h(data: AmalgamatedData, g: Word) -> Word {
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    let l = b_rcoset_h_min_len(data, g);
    let r = b_rcoset_h_min_lex(data, g);
    choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && word_lex_rank_base(h, h_lex_base(data)) == r
        && equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h), target)
}

//  ============================================================
//  Part B2: Well-ordering and transversal existence
//  ============================================================

///  No value less than m satisfies p (recursive, avoids quantifier trigger issues).
pub open spec fn no_pred_below(p: spec_fn(nat) -> bool, m: nat) -> bool
    decreases m,
{
    if m == 0 { true }
    else { !p((m - 1) as nat) && no_pred_below(p, (m - 1) as nat) }
}

///  m is the minimum of predicate p.
pub open spec fn is_nat_min(p: spec_fn(nat) -> bool, m: nat) -> bool {
    p(m) && no_pred_below(p, m)
}

///  Well-ordering: scan from `current` to `bound` to find the minimum of p.
proof fn lemma_nat_scan_for_min(p: spec_fn(nat) -> bool, current: nat, bound: nat)
    requires
        p(bound),
        current <= bound,
        no_pred_below(p, current),
    ensures
        exists|m: nat| current <= m && m <= bound && #[trigger] is_nat_min(p, m),
    decreases bound - current,
{
    if p(current) {
        assert(is_nat_min(p, current));
    } else {
        //  !p(current) && no_pred_below(p, current) => no_pred_below(p, current + 1)
        lemma_nat_scan_for_min(p, current + 1, bound);
    }
}

///  Well-ordering principle for nats: any inhabited predicate has a minimum.
pub proof fn lemma_nat_well_ordering(p: spec_fn(nat) -> bool, bound: nat)
    requires
        p(bound),
    ensures
        exists|m: nat| m <= bound && #[trigger] is_nat_min(p, m),
{
    //  no_pred_below(p, 0) is trivially true (base case of recursion)
    lemma_nat_scan_for_min(p, 0, bound);
}

///  The generated subgroup is closed under equivalence.
proof fn lemma_in_subgroup_equiv(
    p: Presentation, gens: Seq<Word>, w1: Word, w2: Word,
)
    requires
        in_generated_subgroup(p, gens, w1),
        equiv_in_presentation(p, w1, w2),
    ensures
        in_generated_subgroup(p, gens, w2),
{
    //  w1 is in subgroup: exists factors with concat_all(factors) ≡ w1
    //  w1 ≡ w2, so by transitivity: concat_all(factors) ≡ w2
    let factors: Seq<Word> = choose|factors: Seq<Word>|
        #[trigger] factors_from_generators(gens, factors)
        && equiv_in_presentation(p, concat_all(factors), w1);
    crate::presentation::lemma_equiv_transitive(
        p, concat_all(factors), w1, w2);
}

///  The left coset of g contains g itself (reflexivity).
proof fn lemma_same_left_coset_reflexive(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        same_left_coset(data, g, g),
{
    let inv_g = inverse_word(g);
    let product = concat(inv_g, g);
    let p1 = data.p1;
    let n1 = p1.num_generators;
    //  concat(inv(g), g) ≡ ε in G₁
    crate::presentation_lemmas::lemma_word_inverse_left(p1, g);
    //  ε is in the generated subgroup
    crate::benign::lemma_identity_in_generated_subgroup(p1, a_words(data));
    //  We need: in_generated_subgroup(p1, a_words, product)
    //  = in_generated_subgroup(p1, a_words, concat(inv(g), g))
    //  From: ε ≡ product, and ε is in the subgroup
    //  Need symmetry: product ≡ ε => ε ≡ product (for equiv closure)
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(g, n1);
    crate::word::lemma_concat_word_valid(inv_g, g, n1);
    //  product is word_valid
    //  Now get: equiv(ε, product) from equiv(product, ε) + symmetry
    //  Actually equiv(product, ε) is what lemma_word_inverse_left gives.
    //  For subgroup closure we need: in_subgroup(ε) && equiv(ε, product) => in_subgroup(product)
    //  lemma_equiv_symmetric gives equiv(ε, product) from equiv(product, ε)
    crate::presentation::lemma_equiv_symmetric(p1, product, empty_word());
    lemma_in_subgroup_equiv(p1, a_words(data), empty_word(), product);
}

//  ============================================================
//  Part C: Syllable type and reduced state
//  ============================================================

///  A syllable: a non-trivial coset representative from one factor.
pub struct Syllable {
    pub is_left: bool,
    pub rep: Word,
}

///  Well-formed reduced state.
pub open spec fn state_valid(data: AmalgamatedData, h: Word, syllables: Seq<Syllable>) -> bool {
    let k = k_size(data);
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;

    &&& word_valid(h, k)
    &&& (forall|i: int| 0 <= i < syllables.len() - 1 ==>
        (#[trigger] syllables[i]).is_left != (#[trigger] syllables[i + 1]).is_left)
    &&& (forall|i: int| 0 <= i < syllables.len() ==> ({
        let syl = #[trigger] syllables[i];
        if syl.is_left {
            word_valid(syl.rep, n1) && !(syl.rep =~= empty_word())
            && !in_left_subgroup(data, syl.rep)
        } else {
            word_valid(syl.rep, n2) && !(syl.rep =~= empty_word())
            && !in_right_subgroup(data, syl.rep)
        }
    }))
}

//  ============================================================
//  Part D: Single-symbol action
//  ============================================================

///  Apply a single G₁ symbol to the state (textbook Lyndon-Schupp Ch. IV).
///  product = s · embed_a(h) in G₁.
///  RIGHT coset decomposition: product ≡ embed_a(new_h) · new_rep (h on LEFT, rep on RIGHT).
///  This gives clean inverse cancellation: s⁻¹ · embed_a(h') · rep' = s⁻¹ · product.
pub open spec fn act_left_sym(
    data: AmalgamatedData,
    s: Symbol,  //  a G₁ symbol (gen_index < n1)
    h: Word,
    syllables: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
    let new_h = a_rcoset_h(data, product);
    let new_rep = a_rcoset_rep(data, product);

    if new_rep =~= empty_word() {
        //  Product is in the subgroup
        (new_h, syllables)
    } else if syllables.len() == 0 || !syllables.first().is_left {
        //  Prepend new left syllable (different factor or empty)
        (new_h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: new_rep }) + syllables)
    } else {
        //  Merge (textbook): compute s·h·u₁ and decompose once with RIGHT cosets.
        let full_product = concat(product, syllables.first().rep);
        let combined_h = a_rcoset_h(data, full_product);
        let merged_rep = a_rcoset_rep(data, full_product);

        if merged_rep =~= empty_word() {
            //  Merge absorbed into subgroup
            (combined_h, syllables.drop_first())
        } else {
            //  Replace first syllable
            (combined_h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep })
                + syllables.drop_first())
        }
    }
}

///  Apply a single G₂ symbol to the state (textbook, RIGHT B-coset decomposition).
///  Mirrors act_left_sym with b_rcoset_h/b_rcoset_rep instead of a_rcoset_h/a_rcoset_rep.
pub open spec fn act_right_sym(
    data: AmalgamatedData,
    s: Symbol,  //  a G₂ symbol (local, already unshifted)
    h: Word,
    syllables: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let new_h = b_rcoset_h(data, product);
    let new_rep = b_rcoset_rep(data, product);

    if new_rep =~= empty_word() {
        (new_h, syllables)
    } else if syllables.len() == 0 || syllables.first().is_left {
        (new_h, Seq::new(1, |_i: int| Syllable { is_left: false, rep: new_rep }) + syllables)
    } else {
        //  Merge (textbook): compute g·h·u₁ and decompose once with RIGHT B-cosets.
        let full_product = concat(product, syllables.first().rep);
        let combined_h = b_rcoset_h(data, full_product);
        let merged_rep = b_rcoset_rep(data, full_product);

        if merged_rep =~= empty_word() {
            (combined_h, syllables.drop_first())
        } else {
            (combined_h, Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
                + syllables.drop_first())
        }
    }
}

///  Apply an AFP symbol to the state. Dispatches to left or right.
pub open spec fn act_sym(
    data: AmalgamatedData,
    s: Symbol,  //  AFP symbol (gen_index < n1+n2)
    h: Word,
    syllables: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let n1 = data.p1.num_generators;
    if generator_index(s) < n1 {
        act_left_sym(data, s, h, syllables)
    } else {
        act_right_sym(data, unshift_sym(s, n1), h, syllables)
    }
}

///  Apply an AFP word to the state (left-to-right, one symbol at a time).
///  Apply an AFP word to the state (right-to-left, textbook LEFT action convention).
///  For a left action φ: G → Perm(S), φ(g₁·g₂) = φ(g₁) ∘ φ(g₂).
///  Processing right-to-left: last symbol first → gives φ(s₁·...·sₙ) = φ(s₁) ∘ ... ∘ φ(sₙ).
pub open spec fn act_word(
    data: AmalgamatedData,
    w: Word,
    h: Word,
    syllables: Seq<Syllable>,
) -> (Word, Seq<Syllable>)
    decreases w.len(),
{
    if w.len() == 0 {
        (h, syllables)
    } else {
        let (new_h, new_syls) = act_sym(data, w.last(), h, syllables);
        act_word(data, w.drop_last(), new_h, new_syls)
    }
}

//  ============================================================
//  Part E: Composition lemma
//  ============================================================

///  act_word(concat(w1, w2), h, syls) == act_word(w2, act_word(w1, h, syls)).
///  This is the fundamental composition property.
///  Composition: act_word(w1·w2, h, syls) = act_word(w1, act_word(w2, h, syls)).
///  With right-to-left processing: w2 is processed first, then w1 (textbook left action).
pub proof fn lemma_act_word_concat(
    data: AmalgamatedData,
    w1: Word, w2: Word,
    h: Word,
    syllables: Seq<Syllable>,
)
    ensures
        act_word(data, concat(w1, w2), h, syllables)
            == act_word(data, w1,
                act_word(data, w2, h, syllables).0,
                act_word(data, w2, h, syllables).1),
    decreases w2.len(),
{
    if w2.len() == 0 {
        //  concat(w1, ε) =~= w1 and act_word(ε, h, syls) = (h, syls)
        assert(concat(w1, w2) =~= w1) by {
            assert(w2.len() == 0);
            assert(concat(w1, w2).len() == w1.len());
            assert forall|k: int| 0 <= k < w1.len()
                implies concat(w1, w2)[k] == w1[k] by {}
        }
    } else {
        //  concat(w1, w2).last() == w2.last()
        //  concat(w1, w2).drop_last() =~= concat(w1, w2.drop_last())
        assert(concat(w1, w2).last() == w2.last()) by {
            let cw = concat(w1, w2);
            assert(cw.len() == w1.len() + w2.len());
            assert(cw[cw.len() - 1] == w2[w2.len() - 1]);
        }
        assert(concat(w1, w2).drop_last() =~= concat(w1, w2.drop_last())) by {
            let cw = concat(w1, w2);
            let rest = concat(w1, w2.drop_last());
            assert(cw.drop_last().len() == rest.len());
            assert forall|k: int| 0 <= k < rest.len()
                implies cw.drop_last()[k] == rest[k]
            by {
                if k < w1.len() as int {
                    assert(cw[k] == w1[k]);
                    assert(rest[k] == w1[k]);
                } else {
                    assert(cw[k] == w2[(k - w1.len() as int)]);
                    assert(rest[k] == w2.drop_last()[(k - w1.len() as int)]);
                }
            }
        }

        let (mid_h, mid_syls) = act_sym(data, w2.last(), h, syllables);
        //  IH: act_word(concat(w1, w2.drop_last()), mid_h, mid_syls)
        //     = act_word(w1, act_word(w2.drop_last(), mid_h, mid_syls))
        lemma_act_word_concat(data, w1, w2.drop_last(), mid_h, mid_syls);
    }
}

///  act_word of the empty word is the identity.
pub proof fn lemma_act_word_empty(
    data: AmalgamatedData,
    h: Word,
    syllables: Seq<Syllable>,
)
    ensures
        act_word(data, empty_word(), h, syllables) == (h, syllables),
{
    //  Direct from the definition: empty_word().len() == 0
}

//  ============================================================
//  Part F: Well-definedness — derivation steps
//  ============================================================

///  The action respects derivation: if w1 derives to w2 via steps,
///  then act_word(w1, h, syls) == act_word(w2, h, syls).
///
///  This follows from:
///    1. lemma_act_word_concat (composition)
///    2. Per-step: for each step type, the inserted/deleted pair acts trivially
///
///  We state the derivation-level well-definedness and build up to it.
///  The per-step proofs (inverse pairs, relators) are the key lemmas.

///  If two words are equivalent in the AFP, they have the same action on any state.
///  This is the top-level well-definedness theorem.
///
///  Proof chain:
///    equiv_in_presentation(AFP, w1, w2)
///    => there exist derivation steps from w1 to w2
///    => each step preserves the action (by per-step lemmas)
///    => act_word(w1, ...) == act_word(w2, ...)
///
///  This will be proved once all per-step lemmas are in place.
///  Infrastructure built below.

///  A single AFP-symbol word acts the same as act_sym.
pub proof fn lemma_act_word_single(
    data: AmalgamatedData,
    s: Symbol,
    h: Word,
    syllables: Seq<Syllable>,
)
    ensures
        act_word(data, Seq::new(1, |_i: int| s), h, syllables)
            == act_sym(data, s, h, syllables),
{
    let w = Seq::new(1, |_i: int| s);
    assert(w.len() == 1);
    assert(w.last() == s);
    let rest = w.drop_last();
    assert(rest.len() == 0);
    assert(rest =~= empty_word()) by {
        assert(rest.len() == 0);
        assert(empty_word().len() == 0);
    }
    let (mid_h, mid_syls) = act_sym(data, s, h, syllables);
    //  act_word unfolds (right-to-left): w.len() != 0, so:
    //    act_word(w, h, syls) = act_word(rest, mid_h, mid_syls)
    //  rest =~= ε, so act_word(rest, ...) = (mid_h, mid_syls)
    assert(act_word(data, rest, mid_h, mid_syls) == (mid_h, mid_syls));
    assert(act_word(data, w, h, syllables) == (mid_h, mid_syls));
}

//  ============================================================
//  Part G: Per-step well-definedness helpers
//  ============================================================

///  Two AFP words produce the same action on any state.
pub open spec fn same_action(data: AmalgamatedData, w1: Word, w2: Word) -> bool {
    forall|h: Word, syllables: Seq<Syllable>|
        act_word(data, w1, h, syllables) == act_word(data, w2, h, syllables)
}

//  ============================================================
//  Part H: One-shot decomposition and faithfulness
//  ============================================================

///  For a G₁ word g, its one-shot state: decompose g directly into (h, rep).
///  If rep = ε, state is (h, []). If rep ≠ ε, state is (h, [left_syl(rep)]).
///  This is the "answer" the action should give for a G₁-word on the identity state.
pub open spec fn g1_decompose_state(
    data: AmalgamatedData,
    g: Word,
) -> (Word, Seq<Syllable>) {
    let rep = a_rcoset_rep(data, g);
    let h = a_rcoset_h(data, g);
    if rep =~= empty_word() {
        (h, Seq::empty())
    } else {
        (h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: rep }))
    }
}

///  The identity state decomposes to (ε, []).
pub proof fn lemma_g1_decompose_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        g1_decompose_state(data, empty_word())
            == (empty_word(), Seq::<Syllable>::empty()),
{
    let e = empty_word();
    reveal(presentation_valid);
    assert(word_valid(e, data.p1.num_generators)) by { assert(e.len() == 0); }

    //  ε is in the subgroup → a_rcoset_rep(ε) =~= ε
    crate::benign::lemma_identity_in_generated_subgroup(data.p1, a_words(data));
    lemma_a_rcoset_in_subgroup(data, e);

    //  a_rcoset_h(ε) =~= ε:
    assert(word_valid(e, k_size(data))) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    crate::presentation::lemma_equiv_refl(data.p1, e);
    let target_e = concat(e, inverse_word(a_rcoset_rep(data, e)));
    //  target =~= ε (since rep =~= ε), so embed_a(ε) = ε ≡ target → witness at length 0
    assert(has_left_h_witness_of_len(data, target_e, 0nat));
    //  min len = 0 by forces_zero
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target_e, l);
    assert(pred_h(0nat));
    assert(no_pred_below(pred_h, 0nat));
    lemma_nat_well_ordering(pred_h, 0nat);
    let hl = a_rcoset_h_min_len(data, e);
    lemma_no_pred_below_forces_zero(pred_h, hl);
    //  hl == 0 → h has length 0
    //  lex at length 0: only ε with rank 0
    assert(word_lex_rank_base(e, h_lex_base(data)) == 0nat);
    assert(has_left_h_witness_of_len_rank(data, target_e, 0nat, 0nat));
    assert(no_smaller_h_lex(data, target_e, 0nat, 0nat));
    lemma_scan_min_h_lex(data, target_e, 0, 0, 0);
    //  a_rcoset_h =~= ε (length 0 word)
}

///  If g ≡ ε in G₁, then inv(g) ≡ ε.
proof fn lemma_inv_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        equiv_in_presentation(data.p1, inverse_word(g), empty_word()),
{
    reveal(presentation_valid);
    let p1 = data.p1;
    let inv_g = inverse_word(g);
    //  g * inv(g) ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_right(p1, g);
    //  g ≡ ε, so concat(g, inv(g)) ≡ concat(ε, inv(g)) by left-congruence
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, g, empty_word(), inv_g);
    //  concat(ε, inv(g)) =~= inv(g)
    assert(concat(empty_word(), inv_g) =~= inv_g) by {
        let c = concat(empty_word(), inv_g);
        assert(c.len() == inv_g.len());
        assert forall|k: int| 0 <= k < c.len() implies c[k] == inv_g[k] by {}
    }
    //  We have:
    //    equiv(concat(g, inv_g), ε)                     -- from word_inverse_right
    //    equiv(concat(g, inv_g), concat(ε, inv_g))      -- from equiv_concat_left
    //  So by symmetry + transitivity:
    //    equiv(ε, concat(g, inv_g))
    //    equiv(concat(g, inv_g), concat(ε, inv_g))
    //    => equiv(ε, concat(ε, inv_g))
    crate::word::lemma_inverse_word_valid(g, p1.num_generators);
    crate::word::lemma_concat_word_valid(g, inv_g, p1.num_generators);
    crate::presentation::lemma_equiv_symmetric(p1, concat(g, inv_g), empty_word());
    crate::presentation::lemma_equiv_transitive(
        p1, empty_word(), concat(g, inv_g), concat(empty_word(), inv_g));
    //  Now: equiv(ε, concat(ε, inv_g)) and concat(ε, inv_g) =~= inv_g
    //  So equiv(ε, inv_g), i.e., equiv(inv_g, ε) by symmetry
    crate::word::lemma_inverse_word_valid(g, p1.num_generators);
    crate::presentation::lemma_equiv_symmetric(p1, empty_word(), inv_g);
}

///  If g ≡ ε in G₁, then g is in the left subgroup.
proof fn lemma_equiv_eps_in_subgroup(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        in_left_subgroup(data, g),
{
    reveal(presentation_valid);
    crate::benign::lemma_identity_in_generated_subgroup(data.p1, a_words(data));
    crate::presentation::lemma_equiv_symmetric(data.p1, g, empty_word());
    lemma_in_subgroup_equiv(data.p1, a_words(data), empty_word(), g);
}

///  If g ≡ ε in G₁, then same_left_coset(g, ε).
proof fn lemma_same_coset_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        same_left_coset(data, g, empty_word()),
{
    reveal(presentation_valid);
    let inv_g = inverse_word(g);
    crate::word::lemma_inverse_word_valid(g, data.p1.num_generators);
    lemma_inv_equiv_eps(data, g);
    //  inv(g) ≡ ε and word_valid(inv(g), n1)
    lemma_equiv_eps_in_subgroup(data, inv_g);
    //  in_left_subgroup(data, inv(g))

    //  same_left_coset(g, ε) = in_left_subgroup(concat(inv(g), ε))
    //  concat(inv(g), ε) =~= inv(g), so same truth value
    assert(concat(inv_g, empty_word()) =~= inv_g) by {
        let c = concat(inv_g, empty_word());
        assert(c.len() == inv_g.len());
        assert forall|k: int| 0 <= k < c.len() implies c[k] == inv_g[k] by {}
    }
}

///  If g ≡ ε in G₁, then left_canonical_rep(g) = ε.
///  If g ≡ ε, then left_min_coset_len(g) == 0.
proof fn lemma_left_min_coset_len_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        left_min_coset_len(data, g) == 0,
{
    let e = empty_word();
    let n1 = data.p1.num_generators;

    //  ε is in g's coset (since g ≡ ε → same_left_coset(g, ε))
    lemma_same_coset_equiv_eps(data, g);
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }
    //  ε has length 0 → has_left_coset_word_of_len(data, g, 0)
    assert(has_left_coset_word_of_len(data, g, 0nat));

    //  is_min_coset_len(data, g, 0) holds: has word at 0 + no_shorter
    assert(no_shorter_coset_word(data, g, 0nat));
    assert(is_min_coset_len(data, g, 0nat));

    let l = left_min_coset_len(data, g);
    //  l satisfies is_min_coset_len(data, g, l). has(g, 0) holds. By no_shorter_implies_ge: 0 >= l.
    lemma_no_shorter_coset_word_implies_ge(data, g, l, 0nat);
}

proof fn lemma_left_rep_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        left_canonical_rep(data, g) =~= empty_word(),
{
    lemma_left_min_coset_len_equiv_eps(data, g);
    //  left_min_coset_len(g) == 0

    let e = empty_word();
    lemma_same_coset_equiv_eps(data, g);
    assert(word_valid(e, data.p1.num_generators)) by { assert(e.len() == 0); }
    assert(word_lex_rank(e) == 0);

    //  ε has length 0 and lex rank 0, in g's coset
    assert(has_left_coset_word_of_len_rank(data, g, 0nat, 0nat));

    assert(no_smaller_coset_lex(data, g, 0nat, 0nat));
    assert(is_min_coset_lex(data, g, 0nat, 0nat));
    let lex_min = left_min_coset_lex(data, g);
    lemma_no_smaller_coset_lex_implies_ge(data, g, 0nat, lex_min, 0nat);
    //  lex_min == 0

    //  left_canonical_rep: choose with length 0, lex rank 0 → length 0 → it's ε.
}

///  If g ≡ ε in G₁, then left_h_part(g) = ε.
///  If g ≡ ε, then left_h_min_len(g) == 0.
proof fn lemma_left_h_min_len_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        left_h_min_len(data, g) == 0,
{
    let e = empty_word();
    let k = k_size(data);
    let p1 = data.p1;
    reveal(presentation_valid);

    lemma_left_rep_equiv_eps(data, g);
    let rep = left_canonical_rep(data, g);
    //  rep =~= ε, so target = concat(inv(ε), g) =~= g
    let target = concat(inverse_word(rep), g);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= g) by {
        let c = concat(e, g);
        assert(c.len() == g.len());
        assert forall|j: int| 0 <= j < g.len() implies c[j] == g[j] by {}
    }

    //  ε is a length-0 K-word with embed_a(ε) = ε ≡ g ≡ target
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    crate::presentation::lemma_equiv_symmetric(p1, g, e);
    assert(has_left_h_witness_of_len(data, target, 0nat));

    let pred = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred(0nat));
    assert(no_pred_below(pred, 0nat));
    let l = left_h_min_len(data, g);
    lemma_no_pred_below_forces_zero(pred, l);
}

proof fn lemma_left_h_equiv_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        left_h_part(data, g) =~= empty_word(),
{
    lemma_left_rep_equiv_eps(data, g);
    lemma_left_h_min_len_equiv_eps(data, g);
    //  left_h_min_len(g) == 0, so left_h_part(g) picks a K-word of length 0 → ε

    //  Show the choose is satisfiable (ε works):
    let e = empty_word();
    let k = k_size(data);
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= g) by {
        let c = concat(e, g);
        assert(c.len() == g.len());
        assert forall|j: int| 0 <= j < g.len() implies c[j] == g[j] by {}
    }
    reveal(presentation_valid);
    crate::presentation::lemma_equiv_symmetric(data.p1, g, e);

    //  Establish h-lex satisfiability: ε has lex rank 0
    assert(word_lex_rank_base(e, h_lex_base(data)) == 0nat);
    assert(has_left_h_witness_of_len_rank(data, target, 0nat, 0nat));
    assert(no_smaller_h_lex(data, target, 0nat, 0nat));
    assert(is_min_h_lex(data, target, 0nat, 0nat));
}

///  If g ≡ ε in G₁, then g1_decompose_state gives the identity state.
pub proof fn lemma_g1_decompose_trivial(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, empty_word()),
    ensures
        g1_decompose_state(data, g)
            == (empty_word(), Seq::<Syllable>::empty()),
{
    let e = empty_word();
    let p1 = data.p1;
    reveal(presentation_valid);

    //  g ≡ ε → g is in the subgroup
    crate::benign::lemma_identity_in_generated_subgroup(p1, a_words(data));
    crate::presentation::lemma_equiv_symmetric(p1, g, e);
    lemma_in_subgroup_equiv(p1, a_words(data), e, g);

    //  g in subgroup → a_rcoset_rep(g) =~= ε
    lemma_a_rcoset_in_subgroup(data, g);

    //  a_rcoset_h(g) =~= ε: target = concat(g, inv(ε)) =~= g ≡ ε
    assert(word_valid(e, k_size(data))) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    crate::presentation::lemma_equiv_symmetric(p1, g, e);
    //  embed_a(ε) = ε ≡ g =~= target → witness at length 0
    let target_g = concat(g, inverse_word(a_rcoset_rep(data, g)));
    assert(has_left_h_witness_of_len(data, target_g, 0nat));
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target_g, l);
    assert(pred_h(0nat));
    assert(no_pred_below(pred_h, 0nat));
    lemma_nat_well_ordering(pred_h, 0nat);
    let hl = a_rcoset_h_min_len(data, g);
    lemma_no_pred_below_forces_zero(pred_h, hl);
    assert(word_lex_rank_base(e, h_lex_base(data)) == 0nat);
    assert(has_left_h_witness_of_len_rank(data, target_g, 0nat, 0nat));
    assert(no_smaller_h_lex(data, target_g, 0nat, 0nat));
    lemma_scan_min_h_lex(data, target_g, 0, 0, 0);
}

//  ============================================================
//  Part H2: Converse faithfulness
//  ============================================================

///  The choose for left_canonical_rep is in g's coset.
///  left_min_coset_len(g) satisfies its choose predicate.
///  Scan for the minimum coset length, building no_shorter_coset_word.
proof fn lemma_scan_min_coset_len(
    data: AmalgamatedData, g: Word, current: nat, bound: nat,
)
    requires
        amalgamated_data_valid(data),
        has_left_coset_word_of_len(data, g, bound),
        current <= bound,
        no_shorter_coset_word(data, g, current),
    ensures
        exists|l: nat| current <= l && l <= bound && #[trigger] is_min_coset_len(data, g, l),
    decreases bound - current,
{
    if has_left_coset_word_of_len(data, g, current) {
        assert(is_min_coset_len(data, g, current));
    } else {
        lemma_scan_min_coset_len(data, g, current + 1, bound);
    }
}

proof fn lemma_left_min_coset_len_satisfiable(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        is_min_coset_len(data, g, left_min_coset_len(data, g)),
{
    //  g is in its own coset at length g.len()
    lemma_same_left_coset_reflexive(data, g);
    assert(has_left_coset_word_of_len(data, g, g.len() as nat));

    //  Scan from 0 to g.len() to find minimum with is_min_coset_len
    assert(no_shorter_coset_word(data, g, 0nat));
    lemma_scan_min_coset_len(data, g, 0, g.len() as nat);
    //  Now: exists l with is_min_coset_len(data, g, l)
    //  So left_min_coset_len's choose is satisfiable → result satisfies has_left_coset_word_of_len.
}

///  left_canonical_rep(g) satisfies all four choose properties:
///  in g's coset, word_valid, correct length, correct lex rank.
proof fn lemma_left_rep_props(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        same_left_coset(data, g, left_canonical_rep(data, g)),
        word_valid(left_canonical_rep(data, g), data.p1.num_generators),
        left_canonical_rep(data, g).len() == left_min_coset_len(data, g),
        word_lex_rank_base(left_canonical_rep(data, g), lex_base(data)) == left_min_coset_lex(data, g),
{
    lemma_left_min_coset_len_satisfiable(data, g);
    lemma_left_min_coset_lex_satisfiable(data, g);
    //  Both chooses are satisfiable → left_canonical_rep's choose is satisfiable
    //  → the result satisfies all four predicate conjuncts
}

///  Converse: if same_left_coset(g, ε) and left_h_part(g) = ε, then g ≡ ε.
///
///  This relies on the left_h_part choose being satisfiable when g is in the
///  subgroup coset. When the predicate is satisfiable and the result is ε:
///    equiv(p1, embed_a(ε), concat(inv(ε), g)) = equiv(p1, ε, g).
///
///  Proving satisfiability requires: in_generated_subgroup → exists K-word
///  witness. This is the key infrastructure lemma connecting the two notions
///  of subgroup membership.
///
///  The satisfiability witness (h_witness) is provided by the caller.
pub proof fn lemma_g1_decompose_converse(
    data: AmalgamatedData, g: Word,
    //  The K-word witness: there exists h0 with embed_a(h0) ≡ g
    h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        left_canonical_rep(data, g) =~= empty_word(),
        left_h_part(data, g) =~= empty_word(),
        //  Witness: the choose predicate for left_h_part is satisfiable
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1, apply_embedding(a_words(data), h_witness), g),
    ensures
        equiv_in_presentation(data.p1, g, empty_word()),
{
    //  left_h_part(g) is a choose with a satisfiable predicate (h_witness works).
    //  The choose returned ε, so ε satisfies the predicate:
    //    equiv(p1, embed_a(ε), concat(inv(rep), g))
    //  With rep = ε: equiv(p1, ε, g).
    //  Hence g ≡ ε.

    //  The key: with a satisfiable choose, the result satisfies the predicate.
    //  embed_a(ε) = ε. concat(inv(ε), g) =~= g.
    //  So: equiv(p1, ε, g) holds.
    reveal(presentation_valid);
    assert(apply_embedding(a_words(data), empty_word()) =~= empty_word());
    assert(inverse_word(empty_word()) =~= empty_word()) by {
        assert(inverse_word(empty_word()).len() == 0);
    }
    assert(concat(inverse_word(left_canonical_rep(data, g)), g) =~= g) by {
        assert(inverse_word(left_canonical_rep(data, g)) =~= empty_word());
        let c = concat(empty_word(), g);
        assert(c.len() == g.len());
        assert forall|k: int| 0 <= k < g.len() implies c[k] == g[k] by {}
    }
    //  h_witness satisfies the left_h_part choose predicate at level left_h_min_len.
    //  First: show left_h_min_len's choose is satisfiable via h_witness.
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);

    //  h_witness has embed_a(h_witness) ≡ g. And target =~= g (since rep = ε).
    //  So embed_a(h_witness) ≡ target. This means h_witness witnesses
    //  has_left_h_witness_of_len(data, target, h_witness.len()).
    assert(has_left_h_witness_of_len(data, target, h_witness.len() as nat));

    //  Use nat well-ordering on has_left_h_witness_of_len
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);

    //  Establish h-lex satisfiability for the three-step choose
    lemma_left_h_min_lex_satisfiable(data, g, h_witness);

    //  Three-step choose satisfiable → left_h_part(g) satisfies its predicate.
    //  left_h_part(g) = ε → equiv(embed_a(ε), target) = equiv(ε, g)
    assert(word_valid(empty_word(), data.p1.num_generators)) by {
        assert(empty_word().len() == 0);
    }
    crate::presentation::lemma_equiv_symmetric(data.p1, empty_word(), g);
}

///  The empty word is shortlex-minimal: nothing is shortlex-smaller.
///  (Already proved in shortlex.rs as lemma_empty_shortlex_minimal.)

///  left_canonical_rep of the empty word (identity element) is the empty word.
///  Because: ε is in ε's coset (reflexive), and ε is shortlex-minimal.
///  If pred(0) is true and no_pred_below(pred, l) holds, then l must be 0.
///  Because no_pred_below(pred, l) for l > 0 requires !pred(l-1), and eventually !pred(0).
proof fn lemma_no_pred_below_forces_zero(pred: spec_fn(nat) -> bool, l: nat)
    requires
        no_pred_below(pred, l),
        pred(0nat),
    ensures
        l == 0,
    decreases l,
{
    if l == 0 {
    } else {
        //  no_pred_below(pred, l) = !pred(l-1) && no_pred_below(pred, l-1)
        //  By IH: no_pred_below(pred, l-1) && pred(0) → l-1 == 0
        lemma_no_pred_below_forces_zero(pred, (l - 1) as nat);
        //  l - 1 == 0, so l == 1. And no_pred_below(pred, 1) = !pred(0) && true = false.
        //  But no_pred_below(pred, l) = no_pred_below(pred, 1) is given as true. Contradiction.
    }
}

///  Transfer no_pred_below through implication: if pred2(l) → pred1(l) for all l,
///  and no_pred_below(pred1, n), then no_pred_below(pred2, n).
proof fn lemma_no_pred_below_transfer(
    pred1: spec_fn(nat) -> bool, pred2: spec_fn(nat) -> bool, n: nat,
)
    requires
        no_pred_below(pred1, n),
        forall|l: nat| pred2(l) ==> #[trigger] pred1(l),
    ensures
        no_pred_below(pred2, n),
    decreases n,
{
    if n == 0 {} else {
        lemma_no_pred_below_transfer(pred1, pred2, (n - 1) as nat);
    }
}

///  Transfer no_smaller_h_lex (A-side) to no_smaller_h_lex_g2 (B-side).
proof fn lemma_no_smaller_h_lex_transfer(
    data: AmalgamatedData, target_a: Word, target_b: Word, l: nat, r: nat,
)
    requires
        no_smaller_h_lex(data, target_a, l, r),
        forall|r2: nat| has_right_h_witness_of_len_rank(data, target_b, l, r2)
            ==> #[trigger] has_left_h_witness_of_len_rank(data, target_a, l, r2),
    ensures
        no_smaller_h_lex_g2(data, target_b, l, r),
    decreases r,
{
    if r == 0 {} else {
        lemma_no_smaller_h_lex_transfer(data, target_a, target_b, l, (r - 1) as nat);
    }
}

///  Extract all four choose properties from b_rcoset_h.
///  Mirrors lemma_left_h_part_full_props for the B-side.
proof fn lemma_b_rcoset_h_full_props(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p2.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness),
            concat(g, inverse_word(b_rcoset_rep(data, g)))),
    ensures ({
        let rep = b_rcoset_rep(data, g);
        let target = concat(g, inverse_word(rep));
        let h = b_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& h.len() == b_rcoset_h_min_len(data, g)
        &&& word_lex_rank_base(h, h_lex_base(data)) == b_rcoset_h_min_lex(data, g)
        &&& equiv_in_presentation(data.p2,
                apply_embedding(b_words(data), h), target)
    }),
{
    //  Mirror the A-side approach: satisfiable → nat_well_ordering → scan
    lemma_b_rcoset_h_satisfiable(data, g, h_witness);
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));

    //  min-len satisfiability: h_witness gives a witness → nat_well_ordering
    let pred_len = |l: nat| has_right_h_witness_of_len(data, target, l);
    assert(pred_len(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_len, h_witness.len() as nat);
    let l = b_rcoset_h_min_len(data, g);

    //  The choose for b_rcoset_h(g) returns word at length l (from full choose predicate)
    //  Extract a witness at length l from has_right_h_witness_of_len(target, l)
    let w_at_l: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(data.p2, apply_embedding(b_words(data), w), target);
    let wr = word_lex_rank_base(w_at_l, h_lex_base(data));
    assert(has_right_h_witness_of_len_rank(data, target, l, wr));
    assert(no_smaller_h_lex_g2(data, target, l, 0nat));
    lemma_scan_min_h_lex_g2(data, target, l, 0, wr);
}

///  If no_smaller_h_lex_g2(target, l, m) and has_right_h_witness_of_len_rank(target, l, k),
///  then k >= m. (Analog of lemma_no_pred_below_implies_ge for the G₂ lex structure.)
proof fn lemma_no_smaller_g2_implies_ge(
    data: AmalgamatedData, target: Word, l: nat, m: nat, k: nat,
)
    requires
        no_smaller_h_lex_g2(data, target, l, m),
        has_right_h_witness_of_len_rank(data, target, l, k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {} else {
        if k < m {
            lemma_no_smaller_g2_implies_ge(data, target, l, (m - 1) as nat, k);
        }
    }
}

///  left_min_coset_len for the empty word is 0.
proof fn lemma_left_min_coset_len_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_min_coset_len(data, empty_word()) == 0,
{
    let e = empty_word();
    let n1 = data.p1.num_generators;

    //  ε is in its own coset with length 0
    lemma_same_left_coset_reflexive(data, e);
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }
    assert(has_left_coset_word_of_len(data, e, 0nat));

    //  no_shorter_coset_word(data, ε, 0) is true (base case of recursion)
    assert(no_shorter_coset_word(data, e, 0nat));

    //  So is_min_coset_len(data, ε, 0) holds — the choose is satisfiable at l = 0.
    assert(is_min_coset_len(data, e, 0nat));

    let l = left_min_coset_len(data, e);
    //  l satisfies is_min_coset_len(data, ε, l), which includes no_shorter_coset_word.
    //  has_left_coset_word_of_len(data, ε, 0) holds. By no_shorter_implies_ge: 0 >= l. So l == 0.
    lemma_no_shorter_coset_word_implies_ge(data, e, l, 0nat);
}

pub proof fn lemma_left_rep_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_canonical_rep(data, empty_word()) =~= empty_word(),
{
    let n1 = data.p1.num_generators;
    let e = empty_word();

    lemma_left_min_coset_len_identity(data);
    //  left_min_coset_len(ε) == 0

    lemma_same_left_coset_reflexive(data, e);
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }

    //  ε has lex rank 0:
    assert(word_lex_rank(e) == 0);

    //  has_left_coset_word_of_len_rank(data, ε, 0, 0) — ε witnesses it
    assert(has_left_coset_word_of_len_rank(data, e, 0nat, 0nat));

    //  is_min_coset_lex(data, ε, 0, 0): has word at (0, 0) + no smaller lex
    assert(no_smaller_coset_lex(data, e, 0nat, 0nat));
    assert(is_min_coset_lex(data, e, 0nat, 0nat));

    let lex_min = left_min_coset_lex(data, e);
    //  lex_min satisfies is_min_coset_lex(ε, 0, lex_min).
    //  has(ε, 0, 0) holds. By no_smaller_implies_ge: 0 >= lex_min. So lex_min == 0.
    lemma_no_smaller_coset_lex_implies_ge(data, e, 0nat, lex_min, 0nat);
    //  left_min_coset_lex(ε) == 0

    //  left_canonical_rep(ε): choose with length 0, lex rank 0.
    //  Any word of length 0 is ε. The choose result has length 0 → it's ε.
}

///  left_h_part of the empty word is the empty K-word.
///  Because: left_canonical_rep(ε) = ε, so inv(rep) ++ ε = ε.
///  embed_a(ε) = ε ≡ ε in G₁. And ε is the shortlex-min such K-word.
///  left_h_min_len for the empty word is 0.
proof fn lemma_left_h_min_len_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_h_min_len(data, empty_word()) == 0,
{
    let e = empty_word();
    let k = k_size(data);
    let p1 = data.p1;
    lemma_left_rep_identity(data);

    //  target = concat(inv(rep), ε) =~= ε (since rep = ε)
    let rep = left_canonical_rep(data, e);
    let target = concat(inverse_word(rep), e);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= e) by { assert(concat(e, e).len() == 0); }

    //  ε is a K-word of length 0 with embed_a(ε) = ε ≡ ε = target
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    crate::presentation::lemma_equiv_refl(p1, e);
    assert(has_left_h_witness_of_len(data, target, 0nat));

    let pred = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred(0nat));
    assert(no_pred_below(pred, 0nat));

    let l = left_h_min_len(data, e);
    lemma_no_pred_below_forces_zero(pred, l);
}

pub proof fn lemma_left_h_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        left_h_part(data, empty_word()) =~= empty_word(),
{
    let e = empty_word();
    let k = k_size(data);
    let p1 = data.p1;
    lemma_left_rep_identity(data);
    lemma_left_h_min_len_identity(data);

    //  left_h_min_len(ε) == 0
    let l = left_h_min_len(data, e);
    assert(l == 0);

    let rep = left_canonical_rep(data, e);
    let target = concat(inverse_word(rep), e);

    //  ε satisfies the predicate (makes the choose satisfiable):
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= e) by { assert(concat(e, e).len() == 0); }
    crate::presentation::lemma_equiv_refl(p1, e);

    //  Establish h-lex satisfiability: ε has lex rank 0
    assert(word_lex_rank_base(e, h_lex_base(data)) == 0nat);
    assert(has_left_h_witness_of_len_rank(data, target, 0nat, 0nat));
    assert(no_smaller_h_lex(data, target, 0nat, 0nat));
    assert(is_min_h_lex(data, target, 0nat, 0nat));
    //  left_h_min_lex's choose is satisfiable → three-step choose satisfiable

    //  The choose is satisfiable → result h satisfies: h.len() == 0
    let h = left_h_part(data, e);
    //  h.len() == l == 0, so h =~= ε
}

///  b_rcoset_h_min_len of ε is 0 (mirrors lemma_left_h_min_len_identity for B-side).
proof fn lemma_b_rcoset_h_min_len_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        b_rcoset_h_min_len(data, empty_word()) == 0,
{
    let e = empty_word();
    let k = k_size(data);
    let p2 = data.p2;
    reveal(presentation_valid);

    //  b_rcoset_rep(ε) = ε
    lemma_identity_in_generated_subgroup(p2, b_words(data));
    lemma_b_rcoset_in_subgroup(data, e);

    //  target =~= ε
    let rep = b_rcoset_rep(data, e);
    let target = concat(e, inverse_word(rep));
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= e) by { assert(concat(e, e).len() == 0); }

    //  ε is a K-word of length 0 with embed_b(ε) ≡ target
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(b_words(data), e) =~= e);
    crate::presentation::lemma_equiv_refl(p2, e);
    assert(has_right_h_witness_of_len(data, target, 0nat));

    let pred = |l: nat| has_right_h_witness_of_len(data, target, l);
    assert(pred(0nat));
    assert(no_pred_below(pred, 0nat));

    let l = b_rcoset_h_min_len(data, e);
    lemma_no_pred_below_forces_zero(pred, l);
}

///  Establish h-part satisfiability for right B-coset decomposition.
///  Mirrors lemma_a_rcoset_h_satisfiable for G₂.
pub proof fn lemma_b_rcoset_h_satisfiable(data: AmalgamatedData, g: Word, h_witness: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p2.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness),
            concat(g, inverse_word(b_rcoset_rep(data, g)))),
    ensures ({
        let rep = b_rcoset_rep(data, g);
        let target = concat(g, inverse_word(rep));
        let h = b_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& equiv_in_presentation(data.p2,
                apply_embedding(b_words(data), h), target)
    }),
{
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));

    //  h_witness witnesses has_right_h_witness_of_len(target, h_witness.len())
    assert(has_right_h_witness_of_len(data, target, h_witness.len() as nat));

    //  Nat well-ordering → b_rcoset_h_min_len satisfiable
    let pred_h = |l: nat| has_right_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);

    //  h-lex satisfiability (scan for min lex at min length)
    let l = b_rcoset_h_min_len(data, g);
    let w: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(data.p2, apply_embedding(b_words(data), w), target);
    let wr = word_lex_rank_base(w, h_lex_base(data));
    assert(has_right_h_witness_of_len_rank(data, target, l, wr));
    assert(no_smaller_h_lex_g2(data, target, l, 0nat));
    lemma_scan_min_h_lex_g2(data, target, l, 0, wr);
}

///  b_rcoset_h of the empty word is ε (mirrors lemma_left_h_identity for the B-side).
pub proof fn lemma_b_rcoset_h_identity(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        b_rcoset_h(data, empty_word()) =~= empty_word(),
{
    let e = empty_word();
    let k = k_size(data);
    let p2 = data.p2;
    reveal(presentation_valid);

    //  b_rcoset_rep(ε) = ε
    lemma_identity_in_generated_subgroup(p2, b_words(data));
    lemma_b_rcoset_in_subgroup(data, e);
    lemma_b_rcoset_h_min_len_identity(data);

    let l = b_rcoset_h_min_len(data, e);
    assert(l == 0);

    let rep = b_rcoset_rep(data, e);
    let target = concat(e, inverse_word(rep));

    //  ε satisfies the predicate
    assert(word_valid(e, k)) by { assert(e.len() == 0); }
    assert(apply_embedding(b_words(data), e) =~= e);
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(target =~= e) by { assert(concat(e, e).len() == 0); }
    crate::presentation::lemma_equiv_refl(p2, e);

    //  Establish h-lex satisfiability: ε has lex rank 0
    assert(word_lex_rank_base(e, h_lex_base(data)) == 0nat);
    assert(has_right_h_witness_of_len_rank(data, target, 0nat, 0nat));
    assert(no_smaller_h_lex_g2(data, target, 0nat, 0nat));
    assert(is_min_h_lex_g2(data, target, 0nat, 0nat));

    //  The choose gives h with h.len() == 0, so h =~= ε
}

///  The identity state (ε, []) is canonical.
pub proof fn lemma_identity_state_canonical(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
    ensures
        is_canonical_state(data, empty_word(), Seq::<Syllable>::empty()),
{
    let e = empty_word();
    let syls = Seq::<Syllable>::empty();

    //  word_valid(ε, k_size)
    assert(word_valid(e, k_size(data)));

    //  left_h_part(embed_a(ε)) =~= ε
    assert(apply_embedding(a_words(data), e) =~= e);
    lemma_left_h_identity(data);

    //  b_rcoset_h(embed_b(ε)) =~= ε
    assert(apply_embedding(b_words(data), e) =~= e);
    lemma_b_rcoset_h_identity(data);

    //  Syllable conditions: vacuously true for empty syls
}

///  Inserting a word at a position preserves the action if the word acts trivially
///  on ALL states (universal version).
pub proof fn lemma_insert_trivial_preserves_action(
    data: AmalgamatedData,
    prefix: Word, middle: Word, suffix: Word,
    h: Word, syllables: Seq<Syllable>,
)
    requires
        same_action(data, middle, empty_word()),
    ensures
        act_word(data, concat(prefix, concat(middle, suffix)), h, syllables)
            == act_word(data, concat(prefix, suffix), h, syllables),
{
    //  Right-to-left: suffix processed first, then middle, then prefix.
    //  concat(prefix, middle·suffix) → act_word(prefix, act_word(middle·suffix, h, syls))
    //  middle·suffix → act_word(middle, act_word(suffix, h, syls))
    //  Since middle ≡ ε (same_action): act_word(middle, sh, ss) = act_word(ε, sh, ss) = (sh, ss)
    lemma_act_word_concat(data, prefix, concat(middle, suffix), h, syllables);
    let (sh, ss) = act_word(data, suffix, h, syllables);
    lemma_act_word_concat(data, middle, suffix, h, syllables);
    lemma_act_word_concat(data, prefix, suffix, h, syllables);
}

///  Inserting a word preserves the action when the word acts trivially on the
///  SPECIFIC intermediate state (targeted version for canonical states).
///  Inserting a trivially-acting middle word preserves the action.
///  With right-to-left processing: suffix processed first, then middle acts on that state.
pub proof fn lemma_insert_trivial_at_state(
    data: AmalgamatedData,
    prefix: Word, middle: Word, suffix: Word,
    h: Word, syllables: Seq<Syllable>,
)
    requires ({
        let (sh, ss) = act_word(data, suffix, h, syllables);
        act_word(data, middle, sh, ss) == (sh, ss)
    }),
    ensures
        act_word(data, concat(prefix, concat(middle, suffix)), h, syllables)
            == act_word(data, concat(prefix, suffix), h, syllables),
{
    lemma_act_word_concat(data, prefix, concat(middle, suffix), h, syllables);
    let (sh, ss) = act_word(data, suffix, h, syllables);
    lemma_act_word_concat(data, middle, suffix, h, syllables);
    lemma_act_word_concat(data, prefix, suffix, h, syllables);
}

//  ============================================================
//  Part I: AFP injectivity theorem
//  ============================================================

///  The inverse pair word [s, inv(s)].
///  The inverse pair word [inv(s), s]. With right-to-left processing, this applies s first
///  then inv(s), giving φ(inv(s)) ∘ φ(s) = φ(inv(s)·s) = φ(ε) = identity.
///  Note: action_well_defined quantifies over ALL symbols s, so this covers both orderings.
pub open spec fn inverse_pair_word(s: Symbol) -> Word {
    Seq::new(1, |_j: int| inverse_symbol(s)) + Seq::new(1, |_j: int| s)
}

///  A specific relator acts trivially on a specific state.
pub open spec fn relator_acts_trivially(
    data: AmalgamatedData, r: Word, h: Word, syls: Seq<Syllable>,
) -> bool {
    act_word(data, r, h, syls) == (h, syls)
}

///  State canonicity: h is a valid K-word AND is the canonical representative
///  for its subgroup equivalence class (matching textbook element-level states).
///  The action always produces canonical K-words (from left_h_part choose).
///  The identity state (ε, []) satisfies this: left_h_part(embed_a(ε)) = left_h_part(ε) =~= ε.
pub open spec fn is_canonical_state(data: AmalgamatedData, h: Word, syls: Seq<Syllable>) -> bool {
    word_valid(h, k_size(data))
    && left_h_part(data, apply_embedding(a_words(data), h)) =~= h
    && b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h
    //  Left syllable reps are canonical, word_valid, and non-identity (textbook reduced sequence)
    && (forall|j: int| #![trigger syls[j]]
        0 <= j < syls.len() && syls[j].is_left ==> (
        word_valid(syls[j].rep, data.p1.num_generators)
        && a_rcoset_rep(data, syls[j].rep) =~= syls[j].rep
        && !(syls[j].rep =~= empty_word())))
    //  Right syllable reps: canonical, word_valid, non-identity (mirrors left)
    && (forall|j: int| #![trigger syls[j]]
        0 <= j < syls.len() && !syls[j].is_left ==> (
        word_valid(syls[j].rep, data.p2.num_generators)
        && b_rcoset_rep(data, syls[j].rep) =~= syls[j].rep
        && !(syls[j].rep =~= empty_word())))
    //  Alternating: adjacent syllables from different factors (textbook reduced sequence)
    && (forall|j: int| #![trigger syls[j]]
        0 <= j < syls.len() - 1 ==> syls[j].is_left != syls[j + 1].is_left)
}

///  The action of a single symbol preserves canonical state (h is word_valid for k).
///  This follows from left_h_part and right_h_part always producing word_valid K-words.
///
///  Stated as a spec-level property; proved from identifications_isomorphic via lemma_iso_implies_apc.
///  A full inductive proof requires showing act_sym preserves word_valid(h, k),
///  which follows from the choose predicates of left_h_part/right_h_part.
pub open spec fn action_preserves_canonical(data: AmalgamatedData) -> bool {
    let n = data.p1.num_generators + data.p2.num_generators;
    forall|w: Word, h: Word, syls: Seq<Syllable>|
        word_valid(w, n) && is_canonical_state(data, h, syls) ==>
        #[trigger] is_canonical_state(data,
            act_word(data, w, h, syls).0,
            act_word(data, w, h, syls).1)
}

///  The action is well-defined on canonical states:
///  every AFP relator and inverse pair acts trivially.
pub open spec fn action_well_defined(data: AmalgamatedData) -> bool {
    let afp = amalgamated_free_product(data);
    //  Every AFP relator acts trivially on canonical states
    &&& (forall|i: nat, inverted: bool, h: Word, syls: Seq<Syllable>|
        i < afp.relators.len() && is_canonical_state(data, h, syls) ==>
        #[trigger] relator_acts_trivially(data, get_relator(afp, i, inverted), h, syls))
    //  Every inverse pair of a valid AFP symbol acts trivially on canonical states
    &&& (forall|s: Symbol, h: Word, syls: Seq<Syllable>|
        symbol_valid(s, afp.num_generators) && is_canonical_state(data, h, syls) ==>
        #[trigger] relator_acts_trivially(data, inverse_pair_word(s), h, syls))
}

///  Derivation-level well-definedness: a full derivation preserves the action.
pub proof fn lemma_act_word_deriv(
    data: AmalgamatedData,
    steps: Seq<DerivationStep>,
    w1: Word, w2: Word,
    h: Word,
    syllables: Seq<Syllable>,
)
    requires
        action_well_defined(data),
        action_preserves_canonical(data),
        amalgamated_data_valid(data),
        is_canonical_state(data, h, syllables),
        derivation_produces(amalgamated_free_product(data), steps, w1) == Some(w2),
        word_valid(w1, amalgamated_free_product(data).num_generators),
    ensures
        act_word(data, w1, h, syllables) == act_word(data, w2, h, syllables),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let afp = amalgamated_free_product(data);
        let step = steps.first();
        let w_mid = apply_step(afp, w1, step).unwrap();

        //  Connect afp.num_generators == n1 + n2 for action_preserves_canonical trigger
        crate::amalgamated_free_product::lemma_add_relators_num_generators(
            crate::free_product::free_product(data.p1, data.p2),
            crate::amalgamated_free_product::amalgamation_relators(data));

        //  Per-step: act_word(w1, h, syls) == act_word(w_mid, h, syls)
        //  Each step inserts/deletes a relator or free pair at some position.
        //  By lemma_act_word_concat: we split at the position.
        //  The inserted/deleted part acts trivially (from action_well_defined).
        //  So the action is preserved.

        //  The action_well_defined condition plus the composition lemma
        //  gives us the per-step result. Each step type:
        //    FreeReduce: deletes pair [s, inv(s)] → pair acts trivially
        //    FreeExpand: inserts pair [s, inv(s)] → pair acts trivially
        //    RelatorInsert: inserts relator → relator acts trivially
        //    RelatorDelete: deletes relator → relator acts trivially

        //  The insertion/deletion at a position is handled by lemma_insert_trivial_preserves_action.
        //  We need to match the step type and extract the position + relator/pair.

        //  With right-to-left processing: suffix is processed FIRST, then the middle
        //  (pair/relator), then the prefix. So the trivial-action check uses the suffix state.
        match step {
            DerivationStep::FreeReduce { position } => {
                //  w1 has [s, inv(s)] at position. inverse_pair_word(inv(s)) = [s, inv(s)].
                let s2 = w1[(position + 1) as int];
                let pair = inverse_pair_word(s2);
                let prefix = w1.subrange(0, position);
                let suffix = w1.subrange(position + 2, w1.len() as int);
                assert(w1 =~= concat(prefix, concat(pair, suffix))) by {
                    assert(w1.len() == concat(prefix, concat(pair, suffix)).len());
                    assert forall|k: int| 0 <= k < w1.len()
                        implies w1[k] == concat(prefix, concat(pair, suffix))[k]
                    by { if k < position {} else if k < position + 2 {} else {} }
                }
                assert(w_mid =~= concat(prefix, suffix));
                let (sh, ss) = act_word(data, suffix, h, syllables);
                assert(word_valid(suffix, afp.num_generators)) by {
                    assert forall|k: int| 0 <= k < suffix.len()
                        implies symbol_valid(#[trigger] suffix[k], afp.num_generators) by {}
                }
                assert(is_canonical_state(data, sh, ss));
                assert(symbol_valid(s2, afp.num_generators));
                assert(relator_acts_trivially(data, inverse_pair_word(s2), sh, ss));
                assert(act_word(data, pair, sh, ss) == (sh, ss));
                lemma_insert_trivial_at_state(data, prefix, pair, suffix, h, syllables);
            },
            DerivationStep::FreeExpand { position, symbol } => {
                //  Inserts [symbol, inv(symbol)]. inverse_pair_word(inv(symbol)) = [symbol, inv(symbol)].
                let pair = inverse_pair_word(inverse_symbol(symbol));
                let prefix = w1.subrange(0, position);
                let suffix = w1.subrange(position, w1.len() as int);
                assert(w_mid =~= concat(prefix, concat(pair, suffix)));
                assert(w1 =~= concat(prefix, suffix)) by {
                    assert(w1.len() == concat(prefix, suffix).len());
                    assert forall|k: int| 0 <= k < w1.len()
                        implies w1[k] == concat(prefix, suffix)[k]
                    by { if k < position {} else {} }
                }
                let (sh, ss) = act_word(data, suffix, h, syllables);
                assert(word_valid(suffix, afp.num_generators)) by {
                    assert forall|k: int| 0 <= k < suffix.len()
                        implies symbol_valid(#[trigger] suffix[k], afp.num_generators) by {}
                }
                assert(is_canonical_state(data, sh, ss));
                assert(symbol_valid(inverse_symbol(symbol), afp.num_generators));
                assert(relator_acts_trivially(data, inverse_pair_word(inverse_symbol(symbol)), sh, ss));
                assert(act_word(data, pair, sh, ss) == (sh, ss));
                lemma_insert_trivial_at_state(data, prefix, pair, suffix, h, syllables);
            },
            DerivationStep::RelatorInsert { position, relator_index, inverted } => {
                let r = get_relator(afp, relator_index, inverted);
                let prefix = w1.subrange(0, position);
                let suffix = w1.subrange(position, w1.len() as int);
                assert(w_mid =~= concat(prefix, concat(r, suffix)));
                assert(w1 =~= concat(prefix, suffix)) by {
                    assert(w1.len() == concat(prefix, suffix).len());
                    assert forall|k: int| 0 <= k < w1.len()
                        implies w1[k] == concat(prefix, suffix)[k]
                    by { if k < position {} else {} }
                }
                let (sh, ss) = act_word(data, suffix, h, syllables);
                assert(word_valid(suffix, afp.num_generators)) by {
                    assert forall|k: int| 0 <= k < suffix.len()
                        implies symbol_valid(#[trigger] suffix[k], afp.num_generators) by {}
                }
                assert(is_canonical_state(data, sh, ss));
                assert(relator_acts_trivially(data,
                    get_relator(afp, relator_index, inverted), sh, ss));
                assert(act_word(data, r, sh, ss) == (sh, ss));
                lemma_insert_trivial_at_state(data, prefix, r, suffix, h, syllables);
            },
            DerivationStep::RelatorDelete { position, relator_index, inverted } => {
                let r = get_relator(afp, relator_index, inverted);
                let rlen = r.len();
                let prefix = w1.subrange(0, position);
                let suffix = w1.subrange(position + rlen as int, w1.len() as int);
                assert(w1 =~= concat(prefix, concat(r, suffix))) by {
                    assert(w1.len() == concat(prefix, concat(r, suffix)).len());
                    assert forall|k: int| 0 <= k < w1.len()
                        implies w1[k] == concat(prefix, concat(r, suffix))[k]
                    by {
                        if k < position {} else if k < position + rlen as int {
                            assert(w1.subrange(position, position + rlen as int) == r);
                        } else {}
                    }
                }
                assert(w_mid =~= concat(prefix, suffix));
                let (sh, ss) = act_word(data, suffix, h, syllables);
                assert(word_valid(suffix, afp.num_generators)) by {
                    assert forall|k: int| 0 <= k < suffix.len()
                        implies symbol_valid(#[trigger] suffix[k], afp.num_generators) by {}
                }
                assert(is_canonical_state(data, sh, ss));
                assert(relator_acts_trivially(data,
                    get_relator(afp, relator_index, inverted), sh, ss));
                assert(act_word(data, r, sh, ss) == (sh, ss));
                lemma_insert_trivial_at_state(data, prefix, r, suffix, h, syllables);
            },
        }

        //  Each branch established: act_word(w1, h, syls) == act_word(w_mid, h, syls)
        //  IH: need word_valid(w_mid, n) for the recursive call.
        crate::amalgamated_free_product::lemma_amalgamated_valid(data);
        crate::presentation::lemma_step_preserves_word_valid_pres(
            afp, w1, step, w_mid);
        lemma_act_word_deriv(data, steps.drop_first(), w_mid, w2, h, syllables);
    }
}

///  The action preserves canonical state for a single symbol.
///  act_sym produces h from left_h_part or right_h_part, which are choose results
///  satisfying word_valid(h, k). So the output h is word_valid.
///
///  Note: this requires the left_h_part and right_h_part choose predicates to be
///  satisfiable for the products encountered. This is guaranteed when the
///  starting state is canonical and the transversal decomposition exists.
///
///  For the identity state and action-produced states, satisfiability holds.
///  Taken as a precondition (proved from identifications_isomorphic via lemma_iso_implies_apc).
proof fn lemma_action_preserves_canonical(
    data: AmalgamatedData,
    w: Word,
    h: Word,
    syls: Seq<Syllable>,
)
    requires
        action_preserves_canonical(data),
        is_canonical_state(data, h, syls),
        word_valid(w, data.p1.num_generators + data.p2.num_generators),
    ensures
        is_canonical_state(data,
            act_word(data, w, h, syls).0,
            act_word(data, w, h, syls).1),
{
    //  Direct from action_preserves_canonical spec.
}

//  ============================================================
//  Part I1a: RIGHT A-coset h-part equiv invariance
//  ============================================================

///  RIGHT A-coset h-part min-len equiv: if targets are equivalent, min-len matches.
proof fn lemma_a_rcoset_h_min_len_equiv(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
        a_rcoset_rep(data, g1) =~= a_rcoset_rep(data, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness1),
            concat(g1, inverse_word(a_rcoset_rep(data, g1)))),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness2),
            concat(g2, inverse_word(a_rcoset_rep(data, g2)))),
    ensures
        a_rcoset_h_min_len(data, g1) == a_rcoset_h_min_len(data, g2),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let rep1 = a_rcoset_rep(data, g1);
    let rep2 = a_rcoset_rep(data, g2);
    let target1 = concat(g1, inverse_word(rep1));
    let target2 = concat(g2, inverse_word(rep2));
    reveal(presentation_valid);

    //  rep word_valid from rcoset_rep_props
    lemma_a_rcoset_rep_props(data, g1);
    lemma_a_rcoset_rep_props(data, g2);

    //  target1 ≡ target2 (from g1 ≡ g2 and inv(rep1) =~= inv(rep2))
    crate::word::lemma_inverse_word_valid(rep1, n1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(rep1), n1);
    crate::word::lemma_concat_word_valid(g2, inverse_word(rep2), n1);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, g1, g2, inverse_word(rep1));

    let l1 = a_rcoset_h_min_len(data, g1);
    let l2 = a_rcoset_h_min_len(data, g2);

    //  Satisfiability: has_left_h_witness_of_len(target1, hw1.len()) etc.
    assert(has_left_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_left_h_witness_of_len(data, target2, h_witness2.len() as nat));

    //  Get min-len chooses to fire
    let pred1 = |l: nat| has_left_h_witness_of_len(data, target1, l);
    let pred2 = |l: nat| has_left_h_witness_of_len(data, target2, l);
    lemma_nat_well_ordering(pred1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred2, h_witness2.len() as nat);

    //  Transfer: l1 works for target2 (via h_witness_transfer)
    assert(has_left_h_witness_of_len(data, target1, l1));
    lemma_h_witness_transfer(data, target1, target2, l1);
    //  Transfer: l2 works for target1
    crate::presentation::lemma_equiv_symmetric(p1, target1, target2);
    lemma_h_witness_transfer(data, target2, target1, l2);

    //  Bidirectional ≥: no_pred_below(pred1, l1) + pred2(l1) → l1 ≥ l2 (and vice versa)
    //  no_pred_below gives: nothing shorter than l1 for pred1
    //  But pred2(l1) holds → l1 ≥ l2 (from l2's minimality)
    //  This follows from the choose semantics + no_pred_below
    lemma_no_pred_below_implies_ge(pred2, l2, l1);
    lemma_no_pred_below_implies_ge(pred1, l1, l2);
}

///  RIGHT A-coset h-part equiv invariance: if g₁ ≡ g₂ and reps match, h-parts match.
///  Mirrors lemma_b_rcoset_h_equiv_invariant for A-cosets.
#[verifier::rlimit(40)]
proof fn lemma_a_rcoset_h_equiv_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
        a_rcoset_rep(data, g1) =~= a_rcoset_rep(data, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness1),
            concat(g1, inverse_word(a_rcoset_rep(data, g1)))),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness2),
            concat(g2, inverse_word(a_rcoset_rep(data, g2)))),
    ensures
        a_rcoset_h(data, g1) =~= a_rcoset_h(data, g2),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let rep1 = a_rcoset_rep(data, g1);
    let target1 = concat(g1, inverse_word(rep1));
    let target2 = concat(g2, inverse_word(a_rcoset_rep(data, g2)));
    reveal(presentation_valid);

    //  Min-len equality
    lemma_a_rcoset_h_min_len_equiv(data, g1, g2, h_witness1, h_witness2);
    let l = a_rcoset_h_min_len(data, g1);

    //  Satisfiability for both
    lemma_a_rcoset_h_satisfiable(data, g1, h_witness1);
    lemma_a_rcoset_h_satisfiable(data, g2, h_witness2);

    //  rep word_valid
    lemma_a_rcoset_rep_props(data, g1);
    lemma_a_rcoset_rep_props(data, g2);

    //  target1 ≡ target2
    crate::word::lemma_inverse_word_valid(rep1, n1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(rep1), n1);
    crate::word::lemma_concat_word_valid(g2, inverse_word(a_rcoset_rep(data, g2)), n1);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, g1, g2, inverse_word(rep1));

    //  Establish min-len choose satisfiability via h-witnesses
    assert(has_left_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_left_h_witness_of_len(data, target2, h_witness2.len() as nat));
    let pred_len1 = |l: nat| has_left_h_witness_of_len(data, target1, l);
    let pred_len2 = |l: nat| has_left_h_witness_of_len(data, target2, l);
    lemma_nat_well_ordering(pred_len1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred_len2, h_witness2.len() as nat);
    //  Now the min-len choose is satisfiable → l = a_rcoset_h_min_len fires
    assert(has_left_h_witness_of_len(data, target1, l));
    assert(has_left_h_witness_of_len(data, target2, l));
    let w1: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p1, apply_embedding(a_words(data), w), target1);
    let w2: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p1, apply_embedding(a_words(data), w), target2);
    let wr1 = word_lex_rank_base(w1, h_lex_base(data));
    let wr2 = word_lex_rank_base(w2, h_lex_base(data));

    //  Lex satisfiability: scan to establish min-lex
    assert(has_left_h_witness_of_len_rank(data, target1, l, wr1));
    assert(no_smaller_h_lex(data, target1, l, 0nat));
    lemma_scan_min_h_lex(data, target1, l, 0, wr1);
    assert(has_left_h_witness_of_len_rank(data, target2, l, wr2));
    assert(no_smaller_h_lex(data, target2, l, 0nat));
    lemma_scan_min_h_lex(data, target2, l, 0, wr2);

    let rw1 = a_rcoset_h(data, g1);
    let rw2 = a_rcoset_h(data, g2);
    let r1 = a_rcoset_h_min_lex(data, g1);
    let r2 = a_rcoset_h_min_lex(data, g2);

    //  Transfer: rw1 witnesses for target1 → also for target2
    crate::presentation::lemma_equiv_transitive(p1,
        apply_embedding(a_words(data), rw1), target1, target2);
    crate::presentation::lemma_equiv_symmetric(p1, target1, target2);
    crate::presentation::lemma_equiv_transitive(p1,
        apply_embedding(a_words(data), rw2), target2, target1);

    //  Bidirectional ≥ on lex rank
    lemma_no_smaller_h_lex_implies_ge(data, target2, l, r2, r1);
    lemma_no_smaller_h_lex_implies_ge(data, target1, l, r1, r2);
    //  r1 == r2

    //  Lex rank injectivity → same word
    let base = h_lex_base(data);
    assert forall|k: int| 0 <= k < rw1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw1[k]) < base
    by { assert(symbol_valid(rw1[k], k_size(data))); match rw1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert forall|k: int| 0 <= k < rw2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw2[k]) < base
    by { assert(symbol_valid(rw2[k], k_size(data))); match rw2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert(base > 0) by { assert(h_lex_base(data) == 2 * k_size(data) + 1); }
    lemma_word_lex_rank_base_injective(rw1, rw2, base);
}

//  ============================================================
//  Part I1b: One-shot action and relator triviality
//  ============================================================

///  One-shot G₁ action: apply a full G₁ word g to syllables via a single coset decomposition.
///  This is act_left_sym generalized from a single symbol to a full word product.
///  The key property: this depends only on the G₁-equivalence class of g.
pub open spec fn g1_one_shot_action(
    data: AmalgamatedData,
    g: Word,       //  full G₁ product (e.g., concat(w, embed_a(h)))
    syls: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let rep = a_rcoset_rep(data, g);
    let h_new = a_rcoset_h(data, g);

    if rep =~= empty_word() {
        (h_new, syls)
    } else if syls.len() == 0 || !syls.first().is_left {
        (h_new, Seq::new(1, |_i: int| Syllable { is_left: true, rep: rep }) + syls)
    } else {
        let full = concat(g, syls.first().rep);
        let merged_rep = a_rcoset_rep(data, full);
        let merged_h = a_rcoset_h(data, full);
        if merged_rep =~= empty_word() {
            (merged_h, syls.drop_first())
        } else {
            (merged_h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep })
                + syls.drop_first())
        }
    }
}

///  One-shot on embed_a(h) returns (h, syls) for canonical h.
///  Because embed_a(h) is in the subgroup when h is A-canonical.
proof fn lemma_one_shot_identity(
    data: AmalgamatedData, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
    ensures
        g1_one_shot_action(data, apply_embedding(a_words(data), h), syls) == (h, syls),
{
    let embed_h = apply_embedding(a_words(data), h);
    let n1 = data.p1.num_generators;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  embed_a(h) is in the A-subgroup → rep = ε
    lemma_apply_embedding_in_subgroup(data.p1, a_words(data), h);
    lemma_a_rcoset_in_subgroup(data, embed_h);
    //  a_rcoset_rep(embed_h) =~= ε

    //  h-part = h (from is_canonical_state: left_h_part(embed_a(h)) =~= h)
    //  a_rcoset_h involves the same choose as left_h_part (via the target)
    //  Since rep = ε, target = concat(embed_h, inv(ε)) = embed_h
    //  is_canonical_state gives: left_h_part(embed_a(h)) =~= h
    //  We need: a_rcoset_h(embed_h) =~= h
    //  This follows from the h-part equiv invariance on embed_h
    //  embed_h ≡ embed_h (reflexivity) + left_h_part =~= h (canonical)
    crate::presentation::lemma_equiv_refl(data.p1, embed_h);
    lemma_subgroup_rcoset_restore(data, embed_h, h);
}

///  One-shot on a subgroup element g ≡ embed_a(h) returns (h, syls) for canonical h.
///  This is the special case needed for relator triviality:
///  if r ≡ ε in G₁, then concat(r, embed_a(h)) ≡ embed_a(h), so the one-shot gives (h, syls).
proof fn lemma_one_shot_subgroup_restore(
    data: AmalgamatedData, g: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        is_canonical_state(data, h, syls),
        equiv_in_presentation(data.p1, g, apply_embedding(a_words(data), h)),
    ensures
        g1_one_shot_action(data, g, syls) == (h, syls),
{
    let embed_h = apply_embedding(a_words(data), h);
    let n1 = data.p1.num_generators;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  g ≡ embed_a(h) ∈ A-subgroup → a_rcoset_rep(g) =~= ε
    lemma_apply_embedding_in_subgroup(data.p1, a_words(data), h);
    crate::presentation::lemma_equiv_symmetric(data.p1, g, embed_h);
    lemma_in_subgroup_equiv(data.p1, a_words(data), embed_h, g);
    lemma_a_rcoset_in_subgroup(data, g);

    //  a_rcoset_h(g) =~= h (by subgroup_rcoset_restore)
    lemma_subgroup_rcoset_restore(data, g, h);
}

///  Prepend-cancel: peeling off coset rep c from product p and prepending as syllable
///  gives the same one-shot result. Takes new_syls as parameter to avoid lambda mismatch.
#[verifier::rlimit(60)]
proof fn lemma_one_shot_prepend_cancel(
    data: AmalgamatedData, p: Word, c: Word, syls: Seq<Syllable>, new_syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(p, data.p1.num_generators),
        word_valid(c, data.p1.num_generators),
        !(c =~= empty_word()),
        a_rcoset_rep(data, c) =~= c,
        !(a_rcoset_rep(data, concat(p, inverse_word(c))) =~= empty_word()),
        syls.len() == 0 || !syls.first().is_left,
        new_syls.len() > 0,
        new_syls.first().is_left,
        new_syls.first().rep == c,
        new_syls.drop_first() =~= syls,
    ensures
        g1_one_shot_action(data, concat(p, inverse_word(c)), new_syls)
            == g1_one_shot_action(data, p, syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let q = concat(p, inverse_word(c));
    reveal(presentation_valid);

    //  concat(q, c) = concat(p·c⁻¹, c) ≡ p via left inverse cancellation
    crate::word::lemma_inverse_word_valid(c, n1);
    crate::word::lemma_concat_word_valid(p, inverse_word(c), n1);
    crate::word::lemma_concat_word_valid(q, c, n1);

    //  Associativity: concat(q, c) =~= concat(p, concat(inv(c), c))
    assert(concat(q, c) =~= concat(p, concat(inverse_word(c), c))) by {
        let lhs = concat(q, c);
        let rhs = concat(p, concat(inverse_word(c), c));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < p.len() as int {} else {
                let j = k - p.len() as int;
                if j < inverse_word(c).len() as int {} else {}
            }
        }
    }
    //  inv(c) · c ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_left(p1, c);
    //  concat(p, concat(inv(c), c)) ≡ concat(p, ε) =~= p
    crate::presentation_lemmas::lemma_equiv_concat_right(p1, p, concat(inverse_word(c), c), empty_word());
    assert(concat(p, empty_word()) =~= p) by {
        assert(concat(p, empty_word()).len() == p.len());
        assert forall|k: int| 0 <= k < p.len() implies concat(p, empty_word())[k] == p[k] by {}
    }
    crate::word::lemma_concat_word_valid(inverse_word(c), c, n1);
    crate::word::lemma_concat_word_valid(p, concat(inverse_word(c), c), n1);
    //  concat(p, ε) =~= p → equiv via equiv_refl
    crate::presentation::lemma_equiv_refl(p1, concat(p, empty_word()));
    //  Now chain: concat(p, inv(c)·c) ≡ concat(p, ε) ≡ p (=~= gives ≡ automatically)
    //  Since concat(q, c) =~= concat(p, inv(c)·c), Z3 derives equiv(concat(q, c), p).

    //  Coset invariance: concat(q, c) ≡ p → same coset → same rep
    lemma_same_a_rcoset_from_equiv(data, concat(q, c), p);
    lemma_a_rcoset_rep_invariant(data, concat(q, c), p);

    //  H-part invariance: derive h-witnesses, then call equiv invariant
    lemma_a_rcoset_rep_props(data, concat(q, c));
    lemma_a_rcoset_rep_props(data, p);
    crate::word::lemma_inverse_word_valid(a_rcoset_rep(data, concat(q, c)), n1);
    crate::word::lemma_inverse_word_valid(a_rcoset_rep(data, p), n1);
    crate::word::lemma_concat_word_valid(concat(q, c), inverse_word(a_rcoset_rep(data, concat(q, c))), n1);
    crate::word::lemma_concat_word_valid(p, inverse_word(a_rcoset_rep(data, p)), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(concat(q, c), inverse_word(a_rcoset_rep(data, concat(q, c)))));
    lemma_subgroup_to_k_word(p1, a_words(data), concat(p, inverse_word(a_rcoset_rep(data, p))));
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(concat(q, c), inverse_word(a_rcoset_rep(data, concat(q, c)))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(p, inverse_word(a_rcoset_rep(data, p))));
    assert(a_words(data).len() == k_size(data));
    lemma_a_rcoset_h_equiv_invariant(data, concat(q, c), p, hw1, hw2);

    //  rep_q ≠ ε (precondition): merge case. concat(q, c) is the merge product.
    //  Z3 sees: merge rep = a_rcoset_rep(concat(q,c)) =~= a_rcoset_rep(p), etc.
}

///  Subgroup-prepend: when q ∈ A (rep = ε), prepending c as syllable = one-shot of concat(q, c).
///  Handles the subgroup sub-case that prepend-cancel doesn't cover.
///  one_shot(q, [Syl(left, c)] + syls) = one_shot(concat(q, c), syls)
#[verifier::rlimit(300)]
proof fn lemma_one_shot_subgroup_prepend(
    data: AmalgamatedData, q: Word, c: Word, syls: Seq<Syllable>, new_syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(q, data.p1.num_generators),
        word_valid(c, data.p1.num_generators),
        !(c =~= empty_word()),
        a_rcoset_rep(data, c) =~= c,
        a_rcoset_rep(data, q) =~= empty_word(), //  q ∈ A
        syls.len() == 0 || !syls.first().is_left,
        new_syls.len() > 0,
        new_syls.first().is_left,
        new_syls.first().rep == c,
        new_syls.drop_first() =~= syls,
    ensures
        g1_one_shot_action(data, q, new_syls)
            == g1_one_shot_action(data, concat(q, c), syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let p = concat(q, c);
    //  new_syls is now a parameter (not locally constructed)
    reveal(presentation_valid);

    //  LHS: rep_q = ε → subgroup case → (a_rcoset_h(q), new_syls)
    //  RHS: one_shot(p, syls). q ∈ A → same_a_rcoset(p, c) → rep(p) =~= c ≠ ε.
    //  First syl right/empty → prepend: (a_rcoset_h(p), [Syl(left, rep(p))] + syls)
    //    = (a_rcoset_h(p), [Syl(left, c)] + syls) = (a_rcoset_h(p), new_syls)
    //  Need: a_rcoset_h(q) =~= a_rcoset_h(p).

    //  q ∈ A: establish in_left_subgroup for the coset chain
    lemma_a_rcoset_rep_props(data, q);
    crate::presentation::lemma_equiv_refl(p1, q);
    lemma_in_subgroup_equiv(p1, a_words(data),
        concat(q, inverse_word(a_rcoset_rep(data, q))), q);
    //  q ∈ A → concat(q, c) · inv(c) = q ∈ A → same_a_rcoset(p, c) → rep(p) =~= c
    crate::word::lemma_inverse_word_valid(c, n1);
    crate::word::lemma_concat_word_valid(q, c, n1);
    crate::word::lemma_concat_word_valid(p, inverse_word(c), n1);
    lemma_right_cancel(p1, q, c);
    //  right_cancel gives: equiv(concat(p, inv(c)), q). Symmetric → equiv(q, concat(p, inv(c))).
    crate::presentation::lemma_equiv_symmetric(p1,
        concat(concat(q, c), inverse_word(c)), q);
    lemma_in_subgroup_equiv(p1, a_words(data), q, concat(p, inverse_word(c)));
    //  same_a_rcoset(p, c)
    lemma_a_rcoset_rep_invariant(data, p, c);
    //  rep(p) =~= rep(c) =~= c

    //  H-part: target(q) = q (since rep_q = ε). target(p) = concat(p, inv(rep(p))) ≡ concat(p, inv(c)) ≡ q.
    //  Both targets ≡ q → same h-part via the three-step choose.
    lemma_a_rcoset_rep_props(data, p);
    crate::word::lemma_inverse_word_valid(a_rcoset_rep(data, p), n1);
    crate::word::lemma_concat_word_valid(p, inverse_word(a_rcoset_rep(data, p)), n1);
    //  target(p) ≡ q established above

    //  H-part invariance: equiv targets → same choose result
    //  Use the full machinery: target_q = q, target_p ≡ q. Both in A-subgroup.
    //  h-witnesses for both
    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::word::lemma_concat_word_valid(q, inverse_word(a_rcoset_rep(data, q)), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(q, inverse_word(a_rcoset_rep(data, q))));
    lemma_subgroup_to_k_word(p1, a_words(data), concat(p, inverse_word(a_rcoset_rep(data, p))));
    assert(a_words(data).len() == k_size(data));
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(q, inverse_word(a_rcoset_rep(data, q))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(p, inverse_word(a_rcoset_rep(data, p))));
    //  equiv between the two targets: target_q = concat(q, inv(ε)) = q.
    //  target_p = concat(p, inv(rep_p)) ≡ q (from the cancel chain above).
    //  But q and p have different reps, so we can't use lemma_a_rcoset_h_equiv_invariant directly.
    //  Instead, note: both targets are ≡ q and both are in A-subgroup.
    //  Use: a_rcoset_h(q) is determined by target q. And a_rcoset_h(p) is determined by target ≡ q.
    //  The h-min-len for q: target = q. The h-min-len for p: target = concat(p, inv(rep_p)).
    //  These targets are ≡ q → same h by the transfer chain.

    //  Targets: target_q = concat(q, inv(ε)) =~= q. target_p = concat(p, inv(rep_p)) ≡ q.
    let target_q = concat(q, inverse_word(a_rcoset_rep(data, q)));
    let target_p = concat(p, inverse_word(a_rcoset_rep(data, p)));
    assert(target_q =~= q) by {
        assert(a_rcoset_rep(data, q) =~= empty_word());
        assert(inverse_word(empty_word()).len() == 0);
        assert(concat(q, inverse_word(a_rcoset_rep(data, q))).len() == q.len());
        assert forall|k: int| 0 <= k < q.len()
            implies concat(q, inverse_word(a_rcoset_rep(data, q)))[k] == q[k] by {}
    }
    //  target_p ≡ q (from the cancel chain: concat(p, inv(c)) ≡ q, and rep_p =~= c)
    crate::presentation::lemma_equiv_transitive(p1,
        apply_embedding(a_words(data), hw2), target_p, target_q);
    //  Now hw2 witnesses for target_q too

    //  Min-len: both targets ≡ q → same min K-word length
    assert(has_left_h_witness_of_len(data, target_q, hw1.len() as nat));
    assert(has_left_h_witness_of_len(data, target_p, hw2.len() as nat));
    let pred_q = |l: nat| has_left_h_witness_of_len(data, target_q, l);
    let pred_p = |l: nat| has_left_h_witness_of_len(data, target_p, l);
    lemma_nat_well_ordering(pred_q, hw1.len() as nat);
    lemma_nat_well_ordering(pred_p, hw2.len() as nat);
    let l_q = a_rcoset_h_min_len(data, q);
    let l_p = a_rcoset_h_min_len(data, p);
    //  Transfer: has_witness(target_q, l_q) → has_witness(target_p, l_q) (via equiv)
    assert(has_left_h_witness_of_len(data, target_q, l_q));
    crate::presentation::lemma_equiv_symmetric(p1, target_q, target_p);
    lemma_h_witness_transfer(data, target_q, target_p, l_q);
    lemma_h_witness_transfer(data, target_p, target_q, l_p);
    lemma_no_pred_below_implies_ge(pred_p, l_p, l_q);
    lemma_no_pred_below_implies_ge(pred_q, l_q, l_p);
    //  l_q == l_p

    //  Lex: extract witnesses, scan, transfer, bidirectional ≥
    lemma_a_rcoset_h_satisfiable(data, q, hw1);
    lemma_a_rcoset_h_satisfiable(data, p, hw2);
    let rw_q = a_rcoset_h(data, q);
    let rw_p = a_rcoset_h(data, p);
    let r_q = a_rcoset_h_min_lex(data, q);
    let r_p = a_rcoset_h_min_lex(data, p);

    //  Extract witnesses at min length for lex scan
    assert(has_left_h_witness_of_len(data, target_q, l_q));
    assert(has_left_h_witness_of_len(data, target_p, l_q));
    let w_q: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l_q
        && equiv_in_presentation(p1, apply_embedding(a_words(data), w), target_q);
    let w_p: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l_q
        && equiv_in_presentation(p1, apply_embedding(a_words(data), w), target_p);
    let wr_q = word_lex_rank_base(w_q, h_lex_base(data));
    let wr_p = word_lex_rank_base(w_p, h_lex_base(data));
    assert(has_left_h_witness_of_len_rank(data, target_q, l_q, wr_q));
    assert(has_left_h_witness_of_len_rank(data, target_p, l_q, wr_p));
    assert(no_smaller_h_lex(data, target_q, l_q, 0nat));
    assert(no_smaller_h_lex(data, target_p, l_q, 0nat));
    lemma_scan_min_h_lex(data, target_q, l_q, 0, wr_q);
    lemma_scan_min_h_lex(data, target_p, l_q, 0, wr_p);

    //  Transfer rw witnesses between targets
    crate::presentation::lemma_equiv_transitive(p1,
        apply_embedding(a_words(data), rw_q), target_q, target_p);
    crate::presentation::lemma_equiv_transitive(p1,
        apply_embedding(a_words(data), rw_p), target_p, target_q);
    lemma_no_smaller_h_lex_implies_ge(data, target_p, l_q, r_p, r_q);
    lemma_no_smaller_h_lex_implies_ge(data, target_q, l_q, r_q, r_p);
    //  r_q == r_p

    //  Lex rank injectivity
    let base = h_lex_base(data);
    assert forall|k: int| 0 <= k < rw_q.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw_q[k]) < base
    by { assert(symbol_valid(rw_q[k], k_size(data))); match rw_q[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert forall|k: int| 0 <= k < rw_p.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw_p[k]) < base
    by { assert(symbol_valid(rw_p[k], k_size(data))); match rw_p[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert(base > 0) by { assert(h_lex_base(data) == 2 * k_size(data) + 1); }
    lemma_word_lex_rank_base_injective(rw_q, rw_p, base);
}

///  One-shot G₁-invariance: if g ≡ g' in G₁ with same syllables, one-shot gives same result.
///  Combines rep invariance + h-part invariance for the full tuple.
#[verifier::rlimit(40)]
proof fn lemma_one_shot_g1_invariant(
    data: AmalgamatedData, g: Word, g_prime: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        word_valid(g_prime, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, g_prime),
        //  First syl (if left) must be word_valid in G₁ for the merge case
        (syls.len() > 0 && syls.first().is_left
            ==> word_valid(syls.first().rep, data.p1.num_generators)),
    ensures
        g1_one_shot_action(data, g, syls) == g1_one_shot_action(data, g_prime, syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    reveal(presentation_valid);

    //  Rep invariance
    lemma_same_a_rcoset_from_equiv(data, g, g_prime);
    lemma_a_rcoset_rep_invariant(data, g, g_prime);

    //  H-part invariance (need h-witnesses)
    lemma_a_rcoset_rep_props(data, g);
    lemma_a_rcoset_rep_props(data, g_prime);
    crate::word::lemma_inverse_word_valid(a_rcoset_rep(data, g), n1);
    crate::word::lemma_concat_word_valid(g, inverse_word(a_rcoset_rep(data, g)), n1);
    crate::word::lemma_concat_word_valid(g_prime, inverse_word(a_rcoset_rep(data, g_prime)), n1);
    lemma_subgroup_to_k_word(p1, a_words(data),
        concat(g, inverse_word(a_rcoset_rep(data, g))));
    lemma_subgroup_to_k_word(p1, a_words(data),
        concat(g_prime, inverse_word(a_rcoset_rep(data, g_prime))));
    assert(a_words(data).len() == k_size(data));
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(g, inverse_word(a_rcoset_rep(data, g))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(g_prime, inverse_word(a_rcoset_rep(data, g_prime))));
    lemma_a_rcoset_h_equiv_invariant(data, g, g_prime, hw1, hw2);

    //  Merge case: if rep ≠ ε and first syl left, need full product equiv too
    if !(a_rcoset_rep(data, g) =~= empty_word()) && syls.len() > 0 && syls.first().is_left {
        let c1 = syls.first().rep;
        crate::word::lemma_concat_word_valid(g, c1, n1);
        crate::word::lemma_concat_word_valid(g_prime, c1, n1);
        crate::presentation_lemmas::lemma_equiv_concat_left(p1, g, g_prime, c1);
        lemma_same_a_rcoset_from_equiv(data, concat(g, c1), concat(g_prime, c1));
        lemma_a_rcoset_rep_invariant(data, concat(g, c1), concat(g_prime, c1));
        //  Full product h-part invariance (rep_props BEFORE inverse_word_valid)
        lemma_a_rcoset_rep_props(data, concat(g, c1));
        lemma_a_rcoset_rep_props(data, concat(g_prime, c1));
        crate::word::lemma_inverse_word_valid(a_rcoset_rep(data, concat(g, c1)), n1);
        crate::word::lemma_concat_word_valid(concat(g, c1),
            inverse_word(a_rcoset_rep(data, concat(g, c1))), n1);
        crate::word::lemma_concat_word_valid(concat(g_prime, c1),
            inverse_word(a_rcoset_rep(data, concat(g_prime, c1))), n1);
        lemma_subgroup_to_k_word(p1, a_words(data),
            concat(concat(g, c1), inverse_word(a_rcoset_rep(data, concat(g, c1)))));
        lemma_subgroup_to_k_word(p1, a_words(data),
            concat(concat(g_prime, c1), inverse_word(a_rcoset_rep(data, concat(g_prime, c1)))));
        let hw3: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
                concat(concat(g, c1), inverse_word(a_rcoset_rep(data, concat(g, c1)))));
        let hw4: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
                concat(concat(g_prime, c1), inverse_word(a_rcoset_rep(data, concat(g_prime, c1)))));
        lemma_a_rcoset_h_equiv_invariant(data, concat(g, c1), concat(g_prime, c1), hw3, hw4);
    }
}

///  One-shot step composition: one_shot of the full product equals one_shot applied after
///  the single-symbol step. Handles all three cases (subgroup, prepend, merge).
///  one_shot(concat(w, g_s), syls) = one_shot(concat(w, embed_a(h_s)), syls_s)
///  where (h_s, syls_s) = one_shot(g_s, syls) = act_left_sym(s, h, syls).
///  Helper: derive concat(w, embed_a(h_s)) ≡ concat(concat(w, g_s), inv(rep_s))
///  from the rcoset decomposition embed_a(h_s) · rep_s ≡ g_s.
proof fn lemma_embed_hs_equiv_chain(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(w, data.p1.num_generators),
        word_valid(g_s, data.p1.num_generators),
        word_valid(h_s, k_size(data)),
        !(a_rcoset_rep(data, g_s) =~= empty_word()),
        a_rcoset_h(data, g_s) =~= h_s,
    ensures ({
        let n1 = data.p1.num_generators;
        let rep_s = a_rcoset_rep(data, g_s);
        let embed_hs = apply_embedding(a_words(data), h_s);
        &&& equiv_in_presentation(data.p1, concat(w, embed_hs),
                concat(concat(w, g_s), inverse_word(rep_s)))
        &&& word_valid(concat(w, embed_hs), n1)
        &&& word_valid(concat(concat(w, g_s), inverse_word(rep_s)), n1)
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let rep_s = a_rcoset_rep(data, g_s);
    let embed_hs = apply_embedding(a_words(data), h_s);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_s, n1);

    lemma_a_rcoset_rep_props(data, g_s);
    crate::word::lemma_inverse_word_valid(rep_s, n1);
    crate::word::lemma_concat_word_valid(g_s, inverse_word(rep_s), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(g_s, inverse_word(rep_s)));
    assert(a_words(data).len() == k_size(data));
    let hw_s: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(g_s, inverse_word(rep_s)));
    lemma_rcoset_decomposition(data, g_s, hw_s);

    //  embed_a(h_s) · rep_s ≡ g_s → embed_a(h_s) ≡ g_s · inv(rep_s)
    crate::word::lemma_concat_word_valid(embed_hs, rep_s, n1);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1,
        concat(embed_hs, rep_s), g_s, inverse_word(rep_s));
    crate::word::lemma_concat_word_valid(concat(embed_hs, rep_s), inverse_word(rep_s), n1);
    crate::presentation::lemma_equiv_symmetric(p1,
        concat(concat(embed_hs, rep_s), inverse_word(rep_s)),
        concat(g_s, inverse_word(rep_s)));
    lemma_right_cancel(p1, embed_hs, rep_s);
    crate::presentation::lemma_equiv_transitive(p1,
        concat(g_s, inverse_word(rep_s)),
        concat(concat(embed_hs, rep_s), inverse_word(rep_s)),
        embed_hs);
    crate::presentation::lemma_equiv_symmetric(p1,
        concat(g_s, inverse_word(rep_s)), embed_hs);
    //  embed_hs ≡ concat(g_s, inv(rep_s))

    crate::presentation_lemmas::lemma_equiv_concat_right(p1, w, embed_hs,
        concat(g_s, inverse_word(rep_s)));
    crate::word::lemma_concat_word_valid(w, embed_hs, n1);
    crate::word::lemma_concat_word_valid(w, g_s, n1);
    crate::word::lemma_concat_word_valid(concat(w, g_s), inverse_word(rep_s), n1);
    assert(concat(w, concat(g_s, inverse_word(rep_s))) =~=
           concat(concat(w, g_s), inverse_word(rep_s))) by {
        let lhs = concat(w, concat(g_s, inverse_word(rep_s)));
        let rhs = concat(concat(w, g_s), inverse_word(rep_s));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w.len() as int {} else {
                let j = k - w.len() as int;
                if j < g_s.len() as int {} else {}
            }
        }
    }
}

///  Step case 2 (prepend): uses equiv chain helper + prepend/subgroup dispatch.
#[verifier::rlimit(50)]
proof fn lemma_one_shot_step_prepend(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
    syls: Seq<Syllable>, syls_s: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(w, data.p1.num_generators),
        word_valid(g_s, data.p1.num_generators),
        word_valid(h_s, k_size(data)),
        g1_one_shot_action(data, g_s, syls) == (h_s, syls_s),
        !(a_rcoset_rep(data, g_s) =~= empty_word()),
        syls.len() == 0 || !syls.first().is_left,
    ensures
        g1_one_shot_action(data, concat(w, g_s), syls)
            == g1_one_shot_action(data, concat(w, apply_embedding(a_words(data), h_s)), syls_s),
{
    let rep_s = a_rcoset_rep(data, g_s);
    let n1 = data.p1.num_generators;
    reveal(presentation_valid);
    lemma_embed_hs_equiv_chain(data, w, g_s, h_s);
    lemma_a_rcoset_rep_idempotent(data, g_s);
    lemma_a_rcoset_rep_props(data, g_s);
    crate::word::lemma_inverse_word_valid(rep_s, n1);
    crate::word::lemma_concat_word_valid(w, g_s, n1);
    crate::word::lemma_concat_word_valid(concat(w, g_s), inverse_word(rep_s), n1);
    let peeled = concat(concat(w, g_s), inverse_word(rep_s));
    //  syls_s is the prepend result: [Syl(left, rep_s)] + syls. Help Z3 see this.
    let prepend_syls = Seq::new(1, |_i: int| Syllable { is_left: true, rep: rep_s }) + syls;
    assert(syls_s =~= prepend_syls);
    assert(syls_s.first().is_left);
    assert(word_valid(rep_s, n1));
    //  Step 1: one_shot(concat(w, embed_hs), syls_s) = one_shot(peeled, syls_s)
    lemma_one_shot_g1_invariant(data,
        concat(w, apply_embedding(a_words(data), h_s)), peeled, syls_s);
    //  Step 2a: congruence — one_shot(peeled, syls_s) = one_shot(peeled, prepend_syls)
    assert(g1_one_shot_action(data, peeled, syls_s)
        == g1_one_shot_action(data, peeled, prepend_syls));
    //  Step 2b: cancel — one_shot(peeled, prepend_syls) = one_shot(concat(w, g_s), syls)
    //  Use g1_invariant to bridge: one_shot(peeled, prepend_syls) = one_shot(concat(w, g_s), syls)
    //  via prepend_cancel/subgroup_prepend, then combine with step 1 + 2a.
    //  Now pass syls_s directly (avoids lambda closure mismatch):
    if a_rcoset_rep(data, peeled) =~= empty_word() {
        lemma_one_shot_subgroup_prepend(data, peeled, rep_s, syls, syls_s);
        //  subgroup_prepend gives: one_shot(peeled, syls_s) == one_shot(concat(peeled, rep_s), syls)
        //  Need: concat(peeled, rep_s) ≡ concat(w, g_s) → g1_invariant
        crate::word::lemma_concat_word_valid(peeled, rep_s, n1);
        //  concat(peeled, rep_s) = concat(concat(w, g_s), inv(rep_s), rep_s) ≡ concat(w, g_s)
        crate::presentation_lemmas::lemma_word_inverse_left(data.p1, rep_s);
        crate::word::lemma_concat_word_valid(inverse_word(rep_s), rep_s, n1);
        crate::presentation_lemmas::lemma_equiv_concat_right(data.p1, concat(w, g_s),
            concat(inverse_word(rep_s), rep_s), empty_word());
        assert(concat(concat(w, g_s), empty_word()) =~= concat(w, g_s)) by {
            assert(concat(concat(w, g_s), empty_word()).len() == concat(w, g_s).len());
            assert forall|k: int| 0 <= k < concat(w, g_s).len()
                implies concat(concat(w, g_s), empty_word())[k] == concat(w, g_s)[k] by {}
        }
        assert(concat(peeled, rep_s) =~= concat(concat(w, g_s), concat(inverse_word(rep_s), rep_s))) by {
            let lhs = concat(peeled, rep_s);
            let rhs = concat(concat(w, g_s), concat(inverse_word(rep_s), rep_s));
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                if k < concat(w, g_s).len() as int {} else {
                    let j = k - concat(w, g_s).len() as int;
                    if j < inverse_word(rep_s).len() as int {} else {}
                }
            }
        }
        crate::presentation::lemma_equiv_refl(data.p1, concat(concat(w, g_s), empty_word()));
        lemma_one_shot_g1_invariant(data, concat(peeled, rep_s), concat(w, g_s), syls);
    } else {
        lemma_one_shot_prepend_cancel(data, concat(w, g_s), rep_s, syls, syls_s);
    }
}

///  Step case 3 (merge): first syl is left, full = g_s · c1.
///  Bridge helper: concat(peeled, rep) ≡ concat(w, full) when peeled = concat(concat(w, full), inv(rep)).
proof fn lemma_peeled_concat_bridge(
    data: AmalgamatedData, w_full: Word, rep: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(w_full, data.p1.num_generators),
        word_valid(rep, data.p1.num_generators),
    ensures
        equiv_in_presentation(data.p1,
            concat(concat(w_full, inverse_word(rep)), rep), w_full),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let peeled = concat(w_full, inverse_word(rep));
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(rep, n1);
    crate::word::lemma_concat_word_valid(w_full, inverse_word(rep), n1);
    crate::word::lemma_concat_word_valid(peeled, rep, n1);

    //  concat(peeled, rep) =~= concat(w_full, concat(inv(rep), rep))
    assert(concat(peeled, rep) =~= concat(w_full, concat(inverse_word(rep), rep))) by {
        let lhs = concat(peeled, rep);
        let rhs = concat(w_full, concat(inverse_word(rep), rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w_full.len() as int {} else {
                let j = k - w_full.len() as int;
                if j < inverse_word(rep).len() as int {} else {}
            }
        }
    }
    //  inv(rep) · rep ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_left(p1, rep);
    crate::word::lemma_concat_word_valid(inverse_word(rep), rep, n1);
    crate::presentation_lemmas::lemma_equiv_concat_right(p1, w_full,
        concat(inverse_word(rep), rep), empty_word());
    assert(concat(w_full, empty_word()) =~= w_full) by {
        assert(concat(w_full, empty_word()).len() == w_full.len());
        assert forall|k: int| 0 <= k < w_full.len()
            implies concat(w_full, empty_word())[k] == w_full[k] by {}
    }
    crate::presentation::lemma_equiv_refl(p1, concat(w_full, empty_word()));
}

///  Step merge replaced sub-case: merged_rep ≠ ε → uses prepend cancel.
#[verifier::rlimit(100)]
proof fn lemma_one_shot_step_merge_replaced(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
    syls: Seq<Syllable>, syls_s: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(w, data.p1.num_generators),
        word_valid(g_s, data.p1.num_generators),
        word_valid(h_s, k_size(data)),
        g1_one_shot_action(data, g_s, syls) == (h_s, syls_s),
        !(a_rcoset_rep(data, g_s) =~= empty_word()),
        syls.len() > 0 && syls.first().is_left,
        word_valid(syls.first().rep, data.p1.num_generators),
        syls.drop_first().len() == 0 || !syls.drop_first().first().is_left,
        a_rcoset_rep(data, syls.first().rep) =~= syls.first().rep,
        !(syls.first().rep =~= empty_word()),
        !({
            let full = concat(g_s, syls.first().rep);
            a_rcoset_rep(data, full) =~= empty_word()
        }),
    ensures
        g1_one_shot_action(data, concat(w, g_s), syls)
            == g1_one_shot_action(data, concat(w, apply_embedding(a_words(data), h_s)), syls_s),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_hs = apply_embedding(a_words(data), h_s);
    let c1 = syls.first().rep;
    let full = concat(g_s, c1);
    let merged_rep = a_rcoset_rep(data, full);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_s, n1);
    crate::word::lemma_concat_word_valid(g_s, c1, n1);
    crate::word::lemma_concat_word_valid(w, g_s, n1);
    crate::word::lemma_concat_word_valid(w, embed_hs, n1);
    crate::word::lemma_concat_word_valid(w, full, n1);
    lemma_a_rcoset_rep_props(data, full);
    crate::word::lemma_inverse_word_valid(merged_rep, n1);
    crate::word::lemma_concat_word_valid(full, inverse_word(merged_rep), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(full, inverse_word(merged_rep)));
    assert(a_words(data).len() == k_size(data));
    let hw_f: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(full, inverse_word(merged_rep)));
    lemma_a_rcoset_h_satisfiable(data, full, hw_f);
    lemma_rcoset_decomposition(data, full, hw_f);

    crate::presentation_lemmas::lemma_equiv_concat_right(p1, w, embed_hs,
        concat(full, inverse_word(merged_rep)));
    assert(concat(w, concat(full, inverse_word(merged_rep))) =~=
           concat(concat(w, full), inverse_word(merged_rep))) by {
        let lhs = concat(w, concat(full, inverse_word(merged_rep)));
        let rhs = concat(concat(w, full), inverse_word(merged_rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w.len() as int {} else {
                let j = k - w.len() as int;
                if j < full.len() as int {} else {}
            }
        }
    }
    lemma_a_rcoset_rep_idempotent(data, full);
    crate::word::lemma_concat_word_valid(concat(w, full), inverse_word(merged_rep), n1);
    let peeled_mr = concat(concat(w, full), inverse_word(merged_rep));
    lemma_one_shot_g1_invariant(data, concat(w, embed_hs), peeled_mr, syls_s);
    //  Help Z3: the merge product concat(concat(w, g_s), c1) =~= concat(w, full)
    assert(concat(concat(w, g_s), c1) =~= concat(w, full)) by {
        let lhs = concat(concat(w, g_s), c1);
        let rhs = concat(w, full);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w.len() as int {} else {
                let j = k - w.len() as int;
                if j < g_s.len() as int {} else {}
            }
        }
    }

    //  Sub-split: concat(w, g_s) could be in subgroup
    if a_rcoset_rep(data, concat(w, g_s)) =~= empty_word() {
        lemma_one_shot_subgroup_prepend(data, concat(w, g_s), c1, syls.drop_first(), syls);
    }

    if a_rcoset_rep(data, peeled_mr) =~= empty_word() {
        lemma_one_shot_subgroup_prepend(data, peeled_mr, merged_rep, syls.drop_first(), syls_s);
        //  Bridge: concat(peeled_mr, merged_rep) ≡ concat(w, full) via helper
        crate::word::lemma_concat_word_valid(peeled_mr, merged_rep, n1);
        lemma_peeled_concat_bridge(data, concat(w, full), merged_rep);
        lemma_one_shot_g1_invariant(data, concat(peeled_mr, merged_rep), concat(w, full), syls.drop_first());
    } else {
        lemma_one_shot_prepend_cancel(data, concat(w, full), merged_rep, syls.drop_first(), syls_s);
    }
}

///  Step case 3 (merge): dispatches to absorbed/replaced.
#[verifier::rlimit(150)]
proof fn lemma_one_shot_step_merge(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
    syls: Seq<Syllable>, syls_s: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(w, data.p1.num_generators),
        word_valid(g_s, data.p1.num_generators),
        word_valid(h_s, k_size(data)),
        g1_one_shot_action(data, g_s, syls) == (h_s, syls_s),
        !(a_rcoset_rep(data, g_s) =~= empty_word()),
        syls.len() > 0 && syls.first().is_left,
        word_valid(syls.first().rep, data.p1.num_generators),
        a_rcoset_rep(data, syls.first().rep) =~= syls.first().rep,
        !(syls.first().rep =~= empty_word()),
        syls.drop_first().len() == 0 || !syls.drop_first().first().is_left,
    ensures
        g1_one_shot_action(data, concat(w, g_s), syls)
            == g1_one_shot_action(data, concat(w, apply_embedding(a_words(data), h_s)), syls_s),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_hs = apply_embedding(a_words(data), h_s);
    let c1 = syls.first().rep;
    let full = concat(g_s, c1);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_s, n1);
    crate::word::lemma_concat_word_valid(g_s, c1, n1);
    crate::word::lemma_concat_word_valid(w, g_s, n1);
    crate::word::lemma_concat_word_valid(w, embed_hs, n1);
    crate::word::lemma_concat_word_valid(w, full, n1);

    //  h_s = a_rcoset_h(full). Get decomposition.
    lemma_a_rcoset_rep_props(data, full);
    let merged_rep = a_rcoset_rep(data, full);
    crate::word::lemma_inverse_word_valid(merged_rep, n1);
    crate::word::lemma_concat_word_valid(full, inverse_word(merged_rep), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(full, inverse_word(merged_rep)));
    assert(a_words(data).len() == k_size(data));
    let hw_f: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(full, inverse_word(merged_rep)));
    lemma_a_rcoset_h_satisfiable(data, full, hw_f);
    lemma_rcoset_decomposition(data, full, hw_f);
    //  embed_a(h_s) · merged_rep ≡ full

    //  concat(w, g_s, c1) =~= concat(w, full)
    assert(concat(concat(w, g_s), c1) =~= concat(w, full)) by {
        let lhs = concat(concat(w, g_s), c1);
        let rhs = concat(w, full);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w.len() as int {} else {
                let j = k - w.len() as int;
                if j < g_s.len() as int {} else {}
            }
        }
    }

    if merged_rep =~= empty_word() {
        //  Merge absorbed: embed_a(h_s) ≡ full
        crate::presentation_lemmas::lemma_equiv_concat_right(p1, w, embed_hs, full);
        crate::presentation::lemma_equiv_symmetric(p1, concat(w, embed_hs), concat(w, full));
        //  RHS = one_shot(concat(w, embed_hs), syls_s) = one_shot(concat(w, full), syls_s)
        lemma_one_shot_g1_invariant(data, concat(w, embed_hs), concat(w, full), syls_s);
        //  LHS = one_shot(concat(w, g_s), syls). Sub-split on rep(concat(w, g_s)):
        if a_rcoset_rep(data, concat(w, g_s)) =~= empty_word() {
            //  concat(w, g_s) ∈ A → use subgroup_prepend:
            //  one_shot(concat(w, g_s), syls) = one_shot(concat(concat(w, g_s), c1), syls.drop_first())
            //                                 = one_shot(concat(w, full), syls.drop_first())
            lemma_one_shot_subgroup_prepend(data, concat(w, g_s), c1, syls.drop_first(), syls);
        }
        //  If rep ≠ ε: Z3 should see the merge branch and compute the result directly
        return;
    } else {
        lemma_one_shot_step_merge_replaced(data, w, g_s, h_s, syls, syls_s);
    }
}

///  One-shot step composition: dispatches to subgroup/prepend/merge case helpers.
proof fn lemma_one_shot_step(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
    syls: Seq<Syllable>, syls_s: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(w, data.p1.num_generators),
        word_valid(g_s, data.p1.num_generators),
        word_valid(h_s, k_size(data)),
        g1_one_shot_action(data, g_s, syls) == (h_s, syls_s),
        is_canonical_state(data, h_s, syls_s),
        (syls.len() > 0 && syls.first().is_left ==> word_valid(syls.first().rep, data.p1.num_generators)),
        (syls.len() > 0 && syls.first().is_left ==> a_rcoset_rep(data, syls.first().rep) =~= syls.first().rep),
        (syls.len() > 0 && syls.first().is_left ==> !(syls.first().rep =~= empty_word())),
        (syls.len() > 0 && syls.first().is_left ==>
            (syls.drop_first().len() == 0 || !syls.drop_first().first().is_left)),
    ensures
        g1_one_shot_action(data, concat(w, g_s), syls)
            == g1_one_shot_action(data, concat(w, apply_embedding(a_words(data), h_s)), syls_s),
{
    let rep_s = a_rcoset_rep(data, g_s);
    reveal(presentation_valid);

    if rep_s =~= empty_word() {
        //  Case 1 (subgroup): embed_a(h_s) ≡ g_s → g1_invariant
        let n1 = data.p1.num_generators;
        let p1 = data.p1;
        assert forall|i: int| 0 <= i < a_words(data).len()
            implies word_valid(#[trigger] a_words(data)[i], n1)
        by { assert(word_valid(data.identifications[i].0, n1)); }
        crate::benign::lemma_apply_embedding_valid(a_words(data), h_s, n1);
        crate::word::lemma_concat_word_valid(w, g_s, n1);
        crate::word::lemma_concat_word_valid(w, apply_embedding(a_words(data), h_s), n1);
        lemma_a_rcoset_rep_props(data, g_s);
        crate::word::lemma_inverse_word_valid(rep_s, n1);
        crate::word::lemma_concat_word_valid(g_s, inverse_word(rep_s), n1);
        lemma_subgroup_to_k_word(p1, a_words(data), concat(g_s, inverse_word(rep_s)));
        assert(a_words(data).len() == k_size(data));
        let hw_s: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
                concat(g_s, inverse_word(rep_s)));
        lemma_rcoset_decomposition(data, g_s, hw_s);
        crate::presentation_lemmas::lemma_equiv_concat_right(p1, w,
            apply_embedding(a_words(data), h_s), g_s);
        crate::presentation::lemma_equiv_symmetric(p1,
            concat(w, apply_embedding(a_words(data), h_s)), concat(w, g_s));
        lemma_one_shot_g1_invariant(data,
            concat(w, apply_embedding(a_words(data), h_s)), concat(w, g_s), syls_s);
        return;
    }

    if syls.len() == 0 || !syls.first().is_left {
        lemma_one_shot_step_prepend(data, w, g_s, h_s, syls, syls_s);
    } else {
        lemma_one_shot_step_merge(data, w, g_s, h_s, syls, syls_s);
    }
}

///  Main theorem: act_word of a G₁-only word equals the one-shot action.
///  Proof by induction on w.len(), using the step composition.
#[verifier::rlimit(50)]
proof fn lemma_act_word_eq_one_shot(
    data: AmalgamatedData, w: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        word_valid(w, data.p1.num_generators),
        action_preserves_canonical(data),
    ensures
        act_word(data, w, h, syls)
            == g1_one_shot_action(data,
                concat(w, apply_embedding(a_words(data), h)), syls),
    decreases w.len(),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_h = apply_embedding(a_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    if w.len() == 0 {
        //  act_word(ε, h, syls) = (h, syls). one_shot(embed_a(h), syls) = (h, syls).
        assert(concat(w, embed_h) =~= embed_h) by {
            assert(w.len() == 0);
            assert(concat(w, embed_h).len() == embed_h.len());
            assert forall|k: int| 0 <= k < embed_h.len()
                implies concat(w, embed_h)[k] == embed_h[k] by {}
        }
        lemma_one_shot_identity(data, h, syls);
    } else {
        //  w = concat(w.drop_last(), [w.last()]). Right-to-left: process w.last() first.
        let s = w.last();
        let w_prime = w.drop_last();
        let g_s = concat(Seq::new(1, |_i: int| s), embed_h);

        //  act_word(w, h, syls) = act_word(w', h_s, syls_s)
        let (h_s, syls_s) = act_sym(data, s, h, syls);

        //  (h_s, syls_s) is canonical: act_sym(s, h, syls) = act_word([s], h, syls)
        let s_word = Seq::new(1, |_i: int| s);
        lemma_act_word_single(data, s, h, syls);
        //  action_preserves_canonical with w = [s]
        assert(is_canonical_state(data, h_s, syls_s)) by {
            assert(is_canonical_state(data,
                act_word(data, s_word, h, syls).0,
                act_word(data, s_word, h, syls).1));
        }

        //  w' is word_valid (drop_last preserves word_valid)
        assert(word_valid(w_prime, n1)) by {
            assert forall|k: int| 0 <= k < w_prime.len()
                implies symbol_valid(#[trigger] w_prime[k], n1) by {
                    assert(w_prime[k] == w[k]);
                }
        }

        //  IH: act_word(w', h_s, syls_s) = one_shot(concat(w', embed_a(h_s)), syls_s)
        lemma_act_word_eq_one_shot(data, w_prime, h_s, syls_s);

        //  Now connect: one_shot(concat(w', embed_a(h_s)), syls_s) = one_shot(concat(w, embed_a(h)), syls)
        //  w = concat(w', [s]) so concat(w, embed_a(h)) = concat(w', concat([s], embed_a(h))) = concat(w', g_s)
        assert(concat(w, embed_h) =~= concat(w_prime, g_s)) by {
            let lhs = concat(w, embed_h);
            let rhs = concat(w_prime, g_s);
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                if k < w_prime.len() as int {
                    assert(lhs[k] == w[k]);
                    assert(rhs[k] == w_prime[k]);
                } else if k == w_prime.len() as int {
                    assert(lhs[k] == w[k]);
                    assert(rhs[k] == g_s[0]);
                } else {
                    let j = k - w_prime.len() as int - 1;
                    assert(lhs[k] == embed_h[j]);
                    assert(rhs[k] == g_s[(k - w_prime.len() as int)]);
                }
            }
        }

        //  Step composition: one_shot(concat(w', g_s), syls) = one_shot(concat(w', embed_a(h_s)), syls_s)
        //  Left syls word_valid in G₁ (from canonical state)
        lemma_one_shot_step(data, w_prime, g_s, h_s, syls, syls_s);
    }
}

///  G₁ relator triviality: if w ≡ ε in G₁, then act_word(w, h, syls) = (h, syls).
pub proof fn lemma_g1_relator_acts_trivially(
    data: AmalgamatedData, w: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        word_valid(w, data.p1.num_generators),
        equiv_in_presentation(data.p1, w, empty_word()),
        action_preserves_canonical(data),
    ensures
        act_word(data, w, h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let embed_h = apply_embedding(a_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  act_word = one_shot
    lemma_act_word_eq_one_shot(data, w, h, syls);

    //  concat(w, embed_a(h)) ≡ concat(ε, embed_a(h)) = embed_a(h) (since w ≡ ε)
    crate::presentation_lemmas::lemma_equiv_concat_left(data.p1, w, empty_word(), embed_h);
    assert(concat(empty_word(), embed_h) =~= embed_h) by {
        assert(concat(empty_word(), embed_h).len() == embed_h.len());
        assert forall|k: int| 0 <= k < embed_h.len()
            implies concat(empty_word(), embed_h)[k] == embed_h[k] by {}
    }
    crate::word::lemma_concat_word_valid(w, embed_h, n1);

    //  one_shot(embed_a(h), syls) = (h, syls)
    lemma_one_shot_subgroup_restore(data, concat(w, embed_h), h, syls);
}

//  ============================================================
//  Part I1c: G₂ one-shot action and relator triviality
//  Mirrors G₁ approach with b_rcoset instead of a_rcoset.
//  ============================================================

///  One-shot G₂ action: mirrors g1_one_shot_action with b_rcoset.
///  Syllable prepend/merge uses is_left=false (right syllables) instead of true.
pub open spec fn g2_one_shot_action(
    data: AmalgamatedData,
    g: Word,       //  full G₂-local product (e.g., concat(w_local, embed_b(h)))
    syls: Seq<Syllable>,
) -> (Word, Seq<Syllable>) {
    let rep = b_rcoset_rep(data, g);
    let h_new = b_rcoset_h(data, g);

    if rep =~= empty_word() {
        (h_new, syls)
    } else if syls.len() == 0 || syls.first().is_left {
        (h_new, Seq::new(1, |_i: int| Syllable { is_left: false, rep: rep }) + syls)
    } else {
        let full = concat(g, syls.first().rep);
        let merged_rep = b_rcoset_rep(data, full);
        let merged_h = b_rcoset_h(data, full);
        if merged_rep =~= empty_word() {
            (merged_h, syls.drop_first())
        } else {
            (merged_h, Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
                + syls.drop_first())
        }
    }
}

///  G₂ one-shot on g ≡ embed_b(h) returns (h, syls) for canonical h.
proof fn lemma_g2_one_shot_subgroup_restore(
    data: AmalgamatedData, g: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        is_canonical_state(data, h, syls),
        equiv_in_presentation(data.p2, g, apply_embedding(b_words(data), h)),
    ensures
        g2_one_shot_action(data, g, syls) == (h, syls),
{
    let embed_h = apply_embedding(b_words(data), h);
    let n2 = data.p2.num_generators;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    //  g ≡ embed_b(h) ∈ B-subgroup → b_rcoset_rep(g) = ε
    lemma_apply_embedding_in_subgroup_g2(data.p2, b_words(data), h);
    crate::presentation::lemma_equiv_symmetric(data.p2, g, embed_h);
    lemma_in_subgroup_equiv(data.p2, b_words(data), embed_h, g);
    lemma_b_rcoset_in_subgroup(data, g);

    //  b_rcoset_h(g) =~= h
    assert(is_canonical_state(data, h, Seq::<Syllable>::empty())) by {
        assert(Seq::<Syllable>::empty().len() == 0int);
    }
    crate::presentation::lemma_equiv_symmetric(data.p2, g, embed_h);
    lemma_subgroup_rcoset_restore_g2(data, g, h);
}

///  B-coset h-part min-len equiv for GENERAL reps (mirrors A-coset version).
proof fn lemma_b_rcoset_h_min_len_equiv_general(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        equiv_in_presentation(data.p2, g1, g2),
        b_rcoset_rep(data, g1) =~= b_rcoset_rep(data, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness1),
            concat(g1, inverse_word(b_rcoset_rep(data, g1)))),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness2),
            concat(g2, inverse_word(b_rcoset_rep(data, g2)))),
    ensures
        b_rcoset_h_min_len(data, g1) == b_rcoset_h_min_len(data, g2),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let rep1 = b_rcoset_rep(data, g1);
    let target1 = concat(g1, inverse_word(rep1));
    let target2 = concat(g2, inverse_word(b_rcoset_rep(data, g2)));
    reveal(presentation_valid);

    lemma_b_rcoset_rep_props(data, g1);
    lemma_b_rcoset_rep_props(data, g2);
    crate::word::lemma_inverse_word_valid(rep1, n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(rep1), n2);
    crate::word::lemma_concat_word_valid(g2, inverse_word(b_rcoset_rep(data, g2)), n2);
    crate::presentation_lemmas::lemma_equiv_concat_left(p2, g1, g2, inverse_word(rep1));

    let l1 = b_rcoset_h_min_len(data, g1);
    let l2 = b_rcoset_h_min_len(data, g2);

    assert(has_right_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_right_h_witness_of_len(data, target2, h_witness2.len() as nat));
    let pred1 = |l: nat| has_right_h_witness_of_len(data, target1, l);
    let pred2 = |l: nat| has_right_h_witness_of_len(data, target2, l);
    lemma_nat_well_ordering(pred1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred2, h_witness2.len() as nat);

    assert(has_right_h_witness_of_len(data, target1, l1));
    lemma_h_witness_transfer_g2(data, target1, target2, l1);
    crate::presentation::lemma_equiv_symmetric(p2, target1, target2);
    lemma_h_witness_transfer_g2(data, target2, target1, l2);
    lemma_no_pred_below_implies_ge(pred2, l2, l1);
    lemma_no_pred_below_implies_ge(pred1, l1, l2);
}

///  B-coset h-part equiv invariant for GENERAL reps (mirrors A-coset version).
#[verifier::rlimit(60)]
proof fn lemma_b_rcoset_h_equiv_invariant_general(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        equiv_in_presentation(data.p2, g1, g2),
        b_rcoset_rep(data, g1) =~= b_rcoset_rep(data, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness1),
            concat(g1, inverse_word(b_rcoset_rep(data, g1)))),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness2),
            concat(g2, inverse_word(b_rcoset_rep(data, g2)))),
    ensures
        b_rcoset_h(data, g1) =~= b_rcoset_h(data, g2),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let target1 = concat(g1, inverse_word(b_rcoset_rep(data, g1)));
    let target2 = concat(g2, inverse_word(b_rcoset_rep(data, g2)));
    reveal(presentation_valid);

    lemma_b_rcoset_h_min_len_equiv_general(data, g1, g2, h_witness1, h_witness2);
    let l = b_rcoset_h_min_len(data, g1);

    lemma_b_rcoset_rep_props(data, g1);
    lemma_b_rcoset_rep_props(data, g2);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, g1), n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(b_rcoset_rep(data, g1)), n2);
    crate::word::lemma_concat_word_valid(g2, inverse_word(b_rcoset_rep(data, g2)), n2);
    crate::presentation_lemmas::lemma_equiv_concat_left(p2, g1, g2,
        inverse_word(b_rcoset_rep(data, g1)));

    //  Establish h-witness satisfiability for min-len
    assert(has_right_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_right_h_witness_of_len(data, target2, h_witness2.len() as nat));
    let pred1 = |l: nat| has_right_h_witness_of_len(data, target1, l);
    let pred2 = |l: nat| has_right_h_witness_of_len(data, target2, l);
    lemma_nat_well_ordering(pred1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred2, h_witness2.len() as nat);
    assert(has_right_h_witness_of_len(data, target1, l));
    assert(has_right_h_witness_of_len(data, target2, l));

    //  Lex scan
    let w1: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target1);
    let w2: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target2);
    let wr1 = word_lex_rank_base(w1, h_lex_base(data));
    let wr2 = word_lex_rank_base(w2, h_lex_base(data));
    assert(has_right_h_witness_of_len_rank(data, target1, l, wr1));
    assert(has_right_h_witness_of_len_rank(data, target2, l, wr2));
    assert(no_smaller_h_lex_g2(data, target1, l, 0nat));
    assert(no_smaller_h_lex_g2(data, target2, l, 0nat));
    lemma_scan_min_h_lex_g2(data, target1, l, 0, wr1);
    lemma_scan_min_h_lex_g2(data, target2, l, 0, wr2);

    let rw1 = b_rcoset_h(data, g1);
    let rw2 = b_rcoset_h(data, g2);
    let r1 = b_rcoset_h_min_lex(data, g1);
    let r2 = b_rcoset_h_min_lex(data, g2);

    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), rw1), target1, target2);
    crate::presentation::lemma_equiv_symmetric(p2, target1, target2);
    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), rw2), target2, target1);
    lemma_no_smaller_h_lex_g2_implies_ge(data, target2, l, r2, r1);
    lemma_no_smaller_h_lex_g2_implies_ge(data, target1, l, r1, r2);

    let base = h_lex_base(data);
    assert forall|k: int| 0 <= k < rw1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw1[k]) < base
    by { assert(symbol_valid(rw1[k], k_size(data))); match rw1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert forall|k: int| 0 <= k < rw2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw2[k]) < base
    by { assert(symbol_valid(rw2[k], k_size(data))); match rw2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert(base > 0) by { assert(h_lex_base(data) == 2 * k_size(data) + 1); }
    lemma_word_lex_rank_base_injective(rw1, rw2, base);
}

///  G₂ one-shot G₂-invariance: if g ≡ g' in G₂, same one-shot result.
#[verifier::rlimit(60)]
proof fn lemma_g2_one_shot_g2_invariant(
    data: AmalgamatedData, g: Word, g_prime: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        word_valid(g_prime, data.p2.num_generators),
        equiv_in_presentation(data.p2, g, g_prime),
        (syls.len() > 0 && !syls.first().is_left
            ==> word_valid(syls.first().rep, data.p2.num_generators)),
    ensures
        g2_one_shot_action(data, g, syls) == g2_one_shot_action(data, g_prime, syls),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    reveal(presentation_valid);

    lemma_same_b_rcoset_from_equiv(data, g, g_prime);
    lemma_b_rcoset_rep_invariant(data, g, g_prime);

    lemma_b_rcoset_rep_props(data, g);
    lemma_b_rcoset_rep_props(data, g_prime);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, g), n2);
    crate::word::lemma_concat_word_valid(g, inverse_word(b_rcoset_rep(data, g)), n2);
    crate::word::lemma_concat_word_valid(g_prime, inverse_word(b_rcoset_rep(data, g_prime)), n2);
    lemma_subgroup_to_k_word(p2, b_words(data),
        concat(g, inverse_word(b_rcoset_rep(data, g))));
    lemma_subgroup_to_k_word(p2, b_words(data),
        concat(g_prime, inverse_word(b_rcoset_rep(data, g_prime))));
    assert(b_words(data).len() == k_size(data));
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(g, inverse_word(b_rcoset_rep(data, g))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(g_prime, inverse_word(b_rcoset_rep(data, g_prime))));
    lemma_b_rcoset_h_equiv_invariant_general(data, g, g_prime, hw1, hw2);

    if !(b_rcoset_rep(data, g) =~= empty_word()) && syls.len() > 0 && !syls.first().is_left {
        let c1 = syls.first().rep;
        crate::word::lemma_concat_word_valid(g, c1, n2);
        crate::word::lemma_concat_word_valid(g_prime, c1, n2);
        crate::presentation_lemmas::lemma_equiv_concat_left(p2, g, g_prime, c1);
        lemma_same_b_rcoset_from_equiv(data, concat(g, c1), concat(g_prime, c1));
        lemma_b_rcoset_rep_invariant(data, concat(g, c1), concat(g_prime, c1));
        lemma_b_rcoset_rep_props(data, concat(g, c1));
        lemma_b_rcoset_rep_props(data, concat(g_prime, c1));
        crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, concat(g, c1)), n2);
        crate::word::lemma_concat_word_valid(concat(g, c1),
            inverse_word(b_rcoset_rep(data, concat(g, c1))), n2);
        crate::word::lemma_concat_word_valid(concat(g_prime, c1),
            inverse_word(b_rcoset_rep(data, concat(g_prime, c1))), n2);
        lemma_subgroup_to_k_word(p2, b_words(data),
            concat(concat(g, c1), inverse_word(b_rcoset_rep(data, concat(g, c1)))));
        lemma_subgroup_to_k_word(p2, b_words(data),
            concat(concat(g_prime, c1), inverse_word(b_rcoset_rep(data, concat(g_prime, c1)))));
        let hw3: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                concat(concat(g, c1), inverse_word(b_rcoset_rep(data, concat(g, c1)))));
        let hw4: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                concat(concat(g_prime, c1), inverse_word(b_rcoset_rep(data, concat(g_prime, c1)))));
        lemma_b_rcoset_h_equiv_invariant_general(data, concat(g, c1), concat(g_prime, c1), hw3, hw4);
    }
}

///  G₂ prepend-cancel: mirrors lemma_one_shot_prepend_cancel with b_rcoset.
#[verifier::rlimit(60)]
proof fn lemma_g2_prepend_cancel(
    data: AmalgamatedData, p: Word, c: Word, syls: Seq<Syllable>, new_syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(p, data.p2.num_generators),
        word_valid(c, data.p2.num_generators),
        !(c =~= empty_word()),
        b_rcoset_rep(data, c) =~= c,
        !(b_rcoset_rep(data, concat(p, inverse_word(c))) =~= empty_word()),
        syls.len() == 0 || syls.first().is_left,
        new_syls.len() > 0,
        !new_syls.first().is_left,
        new_syls.first().rep == c,
        new_syls.drop_first() =~= syls,
    ensures
        g2_one_shot_action(data, concat(p, inverse_word(c)), new_syls)
            == g2_one_shot_action(data, p, syls),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let q = concat(p, inverse_word(c));
    reveal(presentation_valid);

    crate::word::lemma_inverse_word_valid(c, n2);
    crate::word::lemma_concat_word_valid(p, inverse_word(c), n2);
    crate::word::lemma_concat_word_valid(q, c, n2);
    assert(concat(q, c) =~= concat(p, concat(inverse_word(c), c))) by {
        let lhs = concat(q, c);
        let rhs = concat(p, concat(inverse_word(c), c));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < p.len() as int {} else {
                let j = k - p.len() as int;
                if j < inverse_word(c).len() as int {} else {}
            }
        }
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p2, c);
    crate::presentation_lemmas::lemma_equiv_concat_right(p2, p, concat(inverse_word(c), c), empty_word());
    assert(concat(p, empty_word()) =~= p) by {
        assert(concat(p, empty_word()).len() == p.len());
        assert forall|k: int| 0 <= k < p.len() implies concat(p, empty_word())[k] == p[k] by {}
    }
    crate::word::lemma_concat_word_valid(inverse_word(c), c, n2);
    crate::word::lemma_concat_word_valid(p, concat(inverse_word(c), c), n2);
    crate::presentation::lemma_equiv_refl(p2, concat(p, empty_word()));
    //  concat(q, c) ≡ p

    lemma_same_b_rcoset_from_equiv(data, concat(q, c), p);
    lemma_b_rcoset_rep_invariant(data, concat(q, c), p);

    lemma_b_rcoset_rep_props(data, concat(q, c));
    lemma_b_rcoset_rep_props(data, p);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, concat(q, c)), n2);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, p), n2);
    crate::word::lemma_concat_word_valid(concat(q, c), inverse_word(b_rcoset_rep(data, concat(q, c))), n2);
    crate::word::lemma_concat_word_valid(p, inverse_word(b_rcoset_rep(data, p)), n2);
    lemma_subgroup_to_k_word(p2, b_words(data), concat(concat(q, c), inverse_word(b_rcoset_rep(data, concat(q, c)))));
    lemma_subgroup_to_k_word(p2, b_words(data), concat(p, inverse_word(b_rcoset_rep(data, p))));
    assert(b_words(data).len() == k_size(data));
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(concat(q, c), inverse_word(b_rcoset_rep(data, concat(q, c)))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(p, inverse_word(b_rcoset_rep(data, p))));
    lemma_b_rcoset_h_equiv_invariant_general(data, concat(q, c), p, hw1, hw2);
}

///  G₂ subgroup-prepend: when q ∈ B, prepending c = one-shot of concat(q, c).
#[verifier::rlimit(200)]
proof fn lemma_g2_subgroup_prepend(
    data: AmalgamatedData, q: Word, c: Word, syls: Seq<Syllable>, new_syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(q, data.p2.num_generators),
        word_valid(c, data.p2.num_generators),
        !(c =~= empty_word()),
        b_rcoset_rep(data, c) =~= c,
        b_rcoset_rep(data, q) =~= empty_word(),
        syls.len() == 0 || syls.first().is_left,
        new_syls.len() > 0,
        !new_syls.first().is_left,
        new_syls.first().rep == c,
        new_syls.drop_first() =~= syls,
    ensures
        g2_one_shot_action(data, q, new_syls)
            == g2_one_shot_action(data, concat(q, c), syls),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let p = concat(q, c);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }

    lemma_b_rcoset_rep_props(data, q);
    crate::presentation::lemma_equiv_refl(p2, q);
    lemma_in_subgroup_equiv(p2, b_words(data),
        concat(q, inverse_word(b_rcoset_rep(data, q))), q);
    crate::word::lemma_inverse_word_valid(c, n2);
    crate::word::lemma_concat_word_valid(q, c, n2);
    crate::word::lemma_concat_word_valid(p, inverse_word(c), n2);
    lemma_right_cancel(p2, q, c);
    crate::presentation::lemma_equiv_symmetric(p2,
        concat(concat(q, c), inverse_word(c)), q);
    lemma_in_subgroup_equiv(p2, b_words(data), q, concat(p, inverse_word(c)));
    lemma_b_rcoset_rep_invariant(data, p, c);

    //  H-part: target(q) = q. target(p) ≡ q. Same h.
    lemma_b_rcoset_rep_props(data, p);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, p), n2);
    crate::word::lemma_concat_word_valid(p, inverse_word(b_rcoset_rep(data, p)), n2);
    crate::word::lemma_concat_word_valid(q, inverse_word(b_rcoset_rep(data, q)), n2);
    lemma_subgroup_to_k_word(p2, b_words(data), concat(q, inverse_word(b_rcoset_rep(data, q))));
    lemma_subgroup_to_k_word(p2, b_words(data), concat(p, inverse_word(b_rcoset_rep(data, p))));
    assert(b_words(data).len() == k_size(data));
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(q, inverse_word(b_rcoset_rep(data, q))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(p, inverse_word(b_rcoset_rep(data, p))));

    let target_q = concat(q, inverse_word(b_rcoset_rep(data, q)));
    let target_p = concat(p, inverse_word(b_rcoset_rep(data, p)));
    assert(target_q =~= q) by {
        assert(b_rcoset_rep(data, q) =~= empty_word());
        assert(inverse_word(empty_word()).len() == 0);
        assert(concat(q, inverse_word(b_rcoset_rep(data, q))).len() == q.len());
        assert forall|k: int| 0 <= k < q.len()
            implies concat(q, inverse_word(b_rcoset_rep(data, q)))[k] == q[k] by {}
    }
    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), hw2), target_p, target_q);

    assert(has_right_h_witness_of_len(data, target_q, hw1.len() as nat));
    assert(has_right_h_witness_of_len(data, target_p, hw2.len() as nat));
    let pred_q = |l: nat| has_right_h_witness_of_len(data, target_q, l);
    let pred_p = |l: nat| has_right_h_witness_of_len(data, target_p, l);
    lemma_nat_well_ordering(pred_q, hw1.len() as nat);
    lemma_nat_well_ordering(pred_p, hw2.len() as nat);
    let l_q = b_rcoset_h_min_len(data, q);
    let l_p = b_rcoset_h_min_len(data, p);
    assert(has_right_h_witness_of_len(data, target_q, l_q));
    crate::presentation::lemma_equiv_symmetric(p2, target_q, target_p);
    lemma_h_witness_transfer_g2(data, target_q, target_p, l_q);
    lemma_h_witness_transfer_g2(data, target_p, target_q, l_p);
    lemma_no_pred_below_implies_ge(pred_p, l_p, l_q);
    lemma_no_pred_below_implies_ge(pred_q, l_q, l_p);

    let rw_q = b_rcoset_h(data, q);
    let rw_p = b_rcoset_h(data, p);
    let r_q = b_rcoset_h_min_lex(data, q);
    let r_p = b_rcoset_h_min_lex(data, p);

    assert(has_right_h_witness_of_len(data, target_q, l_q));
    assert(has_right_h_witness_of_len(data, target_p, l_q));
    let wq: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l_q
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target_q);
    let wp: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l_q
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target_p);
    let wrq = word_lex_rank_base(wq, h_lex_base(data));
    let wrp = word_lex_rank_base(wp, h_lex_base(data));
    assert(has_right_h_witness_of_len_rank(data, target_q, l_q, wrq));
    assert(has_right_h_witness_of_len_rank(data, target_p, l_q, wrp));
    assert(no_smaller_h_lex_g2(data, target_q, l_q, 0nat));
    assert(no_smaller_h_lex_g2(data, target_p, l_q, 0nat));
    lemma_scan_min_h_lex_g2(data, target_q, l_q, 0, wrq);
    lemma_scan_min_h_lex_g2(data, target_p, l_q, 0, wrp);

    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), rw_q), target_q, target_p);
    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), rw_p), target_p, target_q);
    lemma_no_smaller_h_lex_g2_implies_ge(data, target_p, l_q, r_p, r_q);
    lemma_no_smaller_h_lex_g2_implies_ge(data, target_q, l_q, r_q, r_p);

    let base = h_lex_base(data);
    assert forall|k: int| 0 <= k < rw_q.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw_q[k]) < base
    by { assert(symbol_valid(rw_q[k], k_size(data))); match rw_q[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert forall|k: int| 0 <= k < rw_p.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rw_p[k]) < base
    by { assert(symbol_valid(rw_p[k], k_size(data))); match rw_p[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert(base > 0) by { assert(h_lex_base(data) == 2 * k_size(data) + 1); }
    lemma_word_lex_rank_base_injective(rw_q, rw_p, base);
}

///  G₂ embed equiv chain: derive concat(w, embed_b(h_s)) ≡ concat(concat(w, g_s), inv(rep_s)).
proof fn lemma_g2_embed_hs_equiv_chain(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(w, data.p2.num_generators),
        word_valid(g_s, data.p2.num_generators),
        word_valid(h_s, k_size(data)),
        !(b_rcoset_rep(data, g_s) =~= empty_word()),
        b_rcoset_h(data, g_s) =~= h_s,
    ensures ({
        let n2 = data.p2.num_generators;
        let rep_s = b_rcoset_rep(data, g_s);
        let embed_hs = apply_embedding(b_words(data), h_s);
        &&& equiv_in_presentation(data.p2, concat(w, embed_hs),
                concat(concat(w, g_s), inverse_word(rep_s)))
        &&& word_valid(concat(w, embed_hs), n2)
        &&& word_valid(concat(concat(w, g_s), inverse_word(rep_s)), n2)
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let rep_s = b_rcoset_rep(data, g_s);
    let embed_hs = apply_embedding(b_words(data), h_s);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_s, n2);

    lemma_b_rcoset_rep_props(data, g_s);
    crate::word::lemma_inverse_word_valid(rep_s, n2);
    crate::word::lemma_concat_word_valid(g_s, inverse_word(rep_s), n2);
    lemma_subgroup_to_k_word(p2, b_words(data), concat(g_s, inverse_word(rep_s)));
    assert(b_words(data).len() == k_size(data));
    let hw_s: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(g_s, inverse_word(rep_s)));
    lemma_b_rcoset_decomposition(data, g_s, hw_s);

    //  embed_b(h_s) · rep_s ≡ g_s → embed_b(h_s) ≡ g_s · inv(rep_s)
    crate::word::lemma_concat_word_valid(embed_hs, rep_s, n2);
    crate::presentation_lemmas::lemma_equiv_concat_left(p2,
        concat(embed_hs, rep_s), g_s, inverse_word(rep_s));
    crate::word::lemma_concat_word_valid(concat(embed_hs, rep_s), inverse_word(rep_s), n2);
    crate::presentation::lemma_equiv_symmetric(p2,
        concat(concat(embed_hs, rep_s), inverse_word(rep_s)),
        concat(g_s, inverse_word(rep_s)));
    lemma_right_cancel(p2, embed_hs, rep_s);
    crate::presentation::lemma_equiv_transitive(p2,
        concat(g_s, inverse_word(rep_s)),
        concat(concat(embed_hs, rep_s), inverse_word(rep_s)),
        embed_hs);
    crate::presentation::lemma_equiv_symmetric(p2,
        concat(g_s, inverse_word(rep_s)), embed_hs);
    crate::presentation_lemmas::lemma_equiv_concat_right(p2, w, embed_hs,
        concat(g_s, inverse_word(rep_s)));
    crate::word::lemma_concat_word_valid(w, embed_hs, n2);
    crate::word::lemma_concat_word_valid(w, g_s, n2);
    crate::word::lemma_concat_word_valid(concat(w, g_s), inverse_word(rep_s), n2);
    assert(concat(w, concat(g_s, inverse_word(rep_s))) =~=
           concat(concat(w, g_s), inverse_word(rep_s))) by {
        let lhs = concat(w, concat(g_s, inverse_word(rep_s)));
        let rhs = concat(concat(w, g_s), inverse_word(rep_s));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w.len() as int {} else {
                let j = k - w.len() as int;
                if j < g_s.len() as int {} else {}
            }
        }
    }
}

///  G₂ peeled bridge: concat(peeled, rep) ≡ w_full.
proof fn lemma_g2_peeled_bridge(
    data: AmalgamatedData, w_full: Word, rep: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(w_full, data.p2.num_generators),
        word_valid(rep, data.p2.num_generators),
    ensures
        equiv_in_presentation(data.p2,
            concat(concat(w_full, inverse_word(rep)), rep), w_full),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let peeled = concat(w_full, inverse_word(rep));
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(rep, n2);
    crate::word::lemma_concat_word_valid(w_full, inverse_word(rep), n2);
    crate::word::lemma_concat_word_valid(peeled, rep, n2);
    assert(concat(peeled, rep) =~= concat(w_full, concat(inverse_word(rep), rep))) by {
        let lhs = concat(peeled, rep);
        let rhs = concat(w_full, concat(inverse_word(rep), rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w_full.len() as int {} else {
                let j = k - w_full.len() as int;
                if j < inverse_word(rep).len() as int {} else {}
            }
        }
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p2, rep);
    crate::word::lemma_concat_word_valid(inverse_word(rep), rep, n2);
    crate::presentation_lemmas::lemma_equiv_concat_right(p2, w_full,
        concat(inverse_word(rep), rep), empty_word());
    assert(concat(w_full, empty_word()) =~= w_full) by {
        assert(concat(w_full, empty_word()).len() == w_full.len());
        assert forall|k: int| 0 <= k < w_full.len()
            implies concat(w_full, empty_word())[k] == w_full[k] by {}
    }
    crate::presentation::lemma_equiv_refl(p2, concat(w_full, empty_word()));
}

///  G₂ step composition: one_shot(concat(w, g_s), syls) = one_shot(concat(w, embed_b(h_s)), syls_s).
///  Handles subgroup/prepend/merge cases. Mirrors lemma_one_shot_step for G₂.
#[verifier::rlimit(200)]
proof fn lemma_g2_one_shot_step(
    data: AmalgamatedData, w: Word, g_s: Word, h_s: Word,
    syls: Seq<Syllable>, syls_s: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(w, data.p2.num_generators),
        word_valid(g_s, data.p2.num_generators),
        word_valid(h_s, k_size(data)),
        g2_one_shot_action(data, g_s, syls) == (h_s, syls_s),
        is_canonical_state(data, h_s, syls_s),
        (syls.len() > 0 && !syls.first().is_left ==> word_valid(syls.first().rep, data.p2.num_generators)),
        (syls.len() > 0 && !syls.first().is_left ==> b_rcoset_rep(data, syls.first().rep) =~= syls.first().rep),
        (syls.len() > 0 && !syls.first().is_left ==> !(syls.first().rep =~= empty_word())),
        (syls.len() > 0 && !syls.first().is_left ==>
            (syls.drop_first().len() == 0 || syls.drop_first().first().is_left)),
    ensures
        g2_one_shot_action(data, concat(w, g_s), syls)
            == g2_one_shot_action(data, concat(w, apply_embedding(b_words(data), h_s)), syls_s),
{
    let rep_s = b_rcoset_rep(data, g_s);
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_s, n2);
    crate::word::lemma_concat_word_valid(w, g_s, n2);
    crate::word::lemma_concat_word_valid(w, apply_embedding(b_words(data), h_s), n2);

    if rep_s =~= empty_word() {
        //  Case 1 (subgroup): embed_b(h_s) ≡ g_s → g2_invariant
        lemma_b_rcoset_rep_props(data, g_s);
        crate::word::lemma_inverse_word_valid(rep_s, n2);
        crate::word::lemma_concat_word_valid(g_s, inverse_word(rep_s), n2);
        lemma_subgroup_to_k_word(p2, b_words(data), concat(g_s, inverse_word(rep_s)));
        assert(b_words(data).len() == k_size(data));
        let hw_s: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                concat(g_s, inverse_word(rep_s)));
        lemma_b_rcoset_decomposition(data, g_s, hw_s);
        crate::presentation_lemmas::lemma_equiv_concat_right(p2, w,
            apply_embedding(b_words(data), h_s), g_s);
        crate::presentation::lemma_equiv_symmetric(p2,
            concat(w, apply_embedding(b_words(data), h_s)), concat(w, g_s));
        lemma_g2_one_shot_g2_invariant(data,
            concat(w, apply_embedding(b_words(data), h_s)), concat(w, g_s), syls_s);
        return;
    }

    //  rep_s ≠ ε. Need b_rcoset_h(g_s) =~= h_s for the equiv chain.
    //  This follows from the precondition g2_one_shot_action(g_s, syls) == (h_s, syls_s)
    //  and the fact that in the prepend branch, h_s = b_rcoset_h(g_s).
    //  In the merge branch, h_s = b_rcoset_h(full). Either way, the chain needs h_s.
    //  For prepend: b_rcoset_h(g_s) is the h-component.
    //  For merge: b_rcoset_h(concat(g_s, c1)) is the h-component.
    //  The embed_hs_equiv_chain only works for the prepend case where h_s = b_rcoset_h(g_s).
    //  For the merge case, we need a different equiv chain.
    //  Let me dispatch based on whether we're in prepend or merge.
    if syls.len() == 0 || syls.first().is_left {
        //  Prepend case: h_s = b_rcoset_h(g_s)
        lemma_g2_embed_hs_equiv_chain(data, w, g_s, h_s);
    }
    lemma_b_rcoset_rep_idempotent(data, g_s);
    lemma_b_rcoset_rep_props(data, g_s);
    crate::word::lemma_inverse_word_valid(rep_s, n2);
    crate::word::lemma_concat_word_valid(concat(w, g_s), inverse_word(rep_s), n2);
    let peeled = concat(concat(w, g_s), inverse_word(rep_s));

    if syls.len() == 0 || syls.first().is_left {
        //  Case 2 (prepend): syls_s = [Syl(false, rep_s)] + syls
        assert(!syls_s.first().is_left);
        assert(word_valid(rep_s, n2));
        lemma_g2_one_shot_g2_invariant(data,
            concat(w, apply_embedding(b_words(data), h_s)), peeled, syls_s);
        if b_rcoset_rep(data, peeled) =~= empty_word() {
            lemma_g2_subgroup_prepend(data, peeled, rep_s, syls, syls_s);
            //  Bridge: concat(peeled, rep_s) ≡ concat(w, g_s)
            crate::word::lemma_concat_word_valid(peeled, rep_s, n2);
            lemma_g2_peeled_bridge(data, concat(w, g_s), rep_s);
            lemma_g2_one_shot_g2_invariant(data, concat(peeled, rep_s), concat(w, g_s), syls);
        } else {
            lemma_g2_prepend_cancel(data, concat(w, g_s), rep_s, syls, syls_s);
        }
        return;
    } else {
        //  Case 3 (merge): first syl is right, !is_left
        let c1 = syls.first().rep;
        let full = concat(g_s, c1);
        crate::word::lemma_concat_word_valid(g_s, c1, n2);
        crate::word::lemma_concat_word_valid(w, full, n2);

        lemma_b_rcoset_rep_props(data, full);
        let merged_rep = b_rcoset_rep(data, full);
        crate::word::lemma_inverse_word_valid(merged_rep, n2);
        crate::word::lemma_concat_word_valid(full, inverse_word(merged_rep), n2);
        lemma_subgroup_to_k_word(p2, b_words(data), concat(full, inverse_word(merged_rep)));
        assert(b_words(data).len() == k_size(data));
        let hw_f: Word = choose|hw: Word| word_valid(hw, k_size(data))
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                concat(full, inverse_word(merged_rep)));
        lemma_b_rcoset_decomposition(data, full, hw_f);

        assert(concat(concat(w, g_s), c1) =~= concat(w, full)) by {
            let lhs = concat(concat(w, g_s), c1);
            let rhs = concat(w, full);
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                if k < w.len() as int {} else {
                    let j = k - w.len() as int;
                    if j < g_s.len() as int {} else {}
                }
            }
        }

        let embed_hs = apply_embedding(b_words(data), h_s);

        if merged_rep =~= empty_word() {
            //  Merge absorbed
            crate::presentation_lemmas::lemma_equiv_concat_right(p2, w, embed_hs, full);
            crate::presentation::lemma_equiv_symmetric(p2, concat(w, embed_hs), concat(w, full));
            lemma_g2_one_shot_g2_invariant(data, concat(w, embed_hs), concat(w, full), syls_s);
            if b_rcoset_rep(data, concat(w, g_s)) =~= empty_word() {
                lemma_g2_subgroup_prepend(data, concat(w, g_s), c1, syls.drop_first(), syls);
            }
        } else {
            //  Merge replaced: embed_hs · merged_rep ≡ full → embed_hs ≡ full · inv(mr)
            crate::word::lemma_concat_word_valid(full, inverse_word(merged_rep), n2);
            crate::word::lemma_concat_word_valid(embed_hs, merged_rep, n2);
            crate::presentation_lemmas::lemma_equiv_concat_left(p2,
                concat(embed_hs, merged_rep), full, inverse_word(merged_rep));
            crate::word::lemma_concat_word_valid(concat(embed_hs, merged_rep), inverse_word(merged_rep), n2);
            crate::presentation::lemma_equiv_symmetric(p2,
                concat(concat(embed_hs, merged_rep), inverse_word(merged_rep)),
                concat(full, inverse_word(merged_rep)));
            lemma_right_cancel(p2, embed_hs, merged_rep);
            crate::presentation::lemma_equiv_transitive(p2,
                concat(full, inverse_word(merged_rep)),
                concat(concat(embed_hs, merged_rep), inverse_word(merged_rep)),
                embed_hs);
            crate::presentation::lemma_equiv_symmetric(p2,
                concat(full, inverse_word(merged_rep)), embed_hs);
            //  Now: embed_hs ≡ concat(full, inv(mr))
            crate::presentation_lemmas::lemma_equiv_concat_right(p2, w, embed_hs,
                concat(full, inverse_word(merged_rep)));
            assert(concat(w, concat(full, inverse_word(merged_rep))) =~=
                   concat(concat(w, full), inverse_word(merged_rep))) by {
                let lhs = concat(w, concat(full, inverse_word(merged_rep)));
                let rhs = concat(concat(w, full), inverse_word(merged_rep));
                assert(lhs.len() == rhs.len());
                assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                    if k < w.len() as int {} else {
                        let j = k - w.len() as int;
                        if j < full.len() as int {} else {}
                    }
                }
            }
            lemma_b_rcoset_rep_idempotent(data, full);
            crate::word::lemma_concat_word_valid(concat(w, full), inverse_word(merged_rep), n2);
            let peeled_mr = concat(concat(w, full), inverse_word(merged_rep));
            lemma_g2_one_shot_g2_invariant(data, concat(w, embed_hs), peeled_mr, syls_s);
            if b_rcoset_rep(data, concat(w, g_s)) =~= empty_word() {
                lemma_g2_subgroup_prepend(data, concat(w, g_s), c1, syls.drop_first(), syls);
            }
            if b_rcoset_rep(data, peeled_mr) =~= empty_word() {
                lemma_g2_subgroup_prepend(data, peeled_mr, merged_rep, syls.drop_first(), syls_s);
                crate::word::lemma_concat_word_valid(peeled_mr, merged_rep, n2);
                lemma_g2_peeled_bridge(data, concat(w, full), merged_rep);
                lemma_g2_one_shot_g2_invariant(data, concat(peeled_mr, merged_rep), concat(w, full), syls.drop_first());
            } else {
                lemma_g2_prepend_cancel(data, concat(w, full), merged_rep, syls.drop_first(), syls_s);
            }
        }
    }
}

///  G₂ act_word = one-shot: for G₂-local word w, act_word(shift(w), h, syls) = g2_one_shot(concat(w, embed_b(h)), syls).
#[verifier::rlimit(150)]
proof fn lemma_act_word_eq_g2_one_shot(
    data: AmalgamatedData, w: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        word_valid(w, data.p2.num_generators),
        action_preserves_canonical(data),
    ensures
        act_word(data, shift_word(w, data.p1.num_generators), h, syls)
            == g2_one_shot_action(data,
                concat(w, apply_embedding(b_words(data), h)), syls),
    decreases w.len(),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let w_shifted = shift_word(w, n1);
    let embed_h = apply_embedding(b_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    if w.len() == 0 {
        assert(w_shifted =~= empty_word()) by {
            assert(w_shifted.len() == 0);
        }
        assert(concat(w, embed_h) =~= embed_h) by {
            assert(w.len() == 0);
            assert(concat(w, embed_h).len() == embed_h.len());
            assert forall|k: int| 0 <= k < embed_h.len()
                implies concat(w, embed_h)[k] == embed_h[k] by {}
        }
        crate::presentation::lemma_equiv_refl(data.p2, embed_h);
        lemma_g2_one_shot_subgroup_restore(data, embed_h, h, syls);
        return;
    }

    let s = w.last();
    let w_prime = w.drop_last();
    let s_shifted = crate::free_product::shift_symbol(s, n1);
    let s_word_shifted = Seq::new(1, |_i: int| s_shifted);

    assert(w_shifted =~= concat(shift_word(w_prime, n1), s_word_shifted)) by {
        let lhs = w_shifted;
        let rhs = concat(shift_word(w_prime, n1), s_word_shifted);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w_prime.len() as int {} else {}
        }
    }

    let (h_s, syls_s) = act_sym(data, s_shifted, h, syls);
    lemma_act_word_single(data, s_shifted, h, syls);
    assert(is_canonical_state(data, h_s, syls_s)) by {
        assert(is_canonical_state(data,
            act_word(data, s_word_shifted, h, syls).0,
            act_word(data, s_word_shifted, h, syls).1));
    }

    assert(word_valid(w_prime, n2)) by {
        assert forall|k: int| 0 <= k < w_prime.len()
            implies symbol_valid(#[trigger] w_prime[k], n2) by {
                assert(w_prime[k] == w[k]);
            }
    }

    lemma_act_word_concat(data, shift_word(w_prime, n1), s_word_shifted, h, syls);
    lemma_act_word_eq_g2_one_shot(data, w_prime, h_s, syls_s);

    //  Connect: one_shot(concat(w', embed_b(h_s)), syls_s) = one_shot(concat(w, embed_b(h)), syls)
    let g_s = concat(Seq::new(1, |_i: int| s), embed_h);
    assert(concat(w, embed_h) =~= concat(w_prime, g_s)) by {
        let lhs = concat(w, embed_h);
        let rhs = concat(w_prime, g_s);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < w_prime.len() as int {} else if k == w_prime.len() as int {} else {
                let j = k - w_prime.len() as int - 1;
            }
        }
    }

    //  Step composition
    crate::word::lemma_concat_word_valid(Seq::new(1, |_i: int| s), embed_h, n2);
    lemma_g2_one_shot_step(data, w_prime, g_s, h_s, syls, syls_s);
}

///  G₂ relator triviality: if w ≡ ε in G₂, act_word(shift(w), h, syls) = (h, syls).
pub proof fn lemma_g2_relator_acts_trivially(
    data: AmalgamatedData, w: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        word_valid(w, data.p2.num_generators),
        equiv_in_presentation(data.p2, w, empty_word()),
        action_preserves_canonical(data),
    ensures
        act_word(data, shift_word(w, data.p1.num_generators), h, syls) == (h, syls),
{
    let n2 = data.p2.num_generators;
    let embed_h = apply_embedding(b_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    lemma_act_word_eq_g2_one_shot(data, w, h, syls);

    crate::word::lemma_concat_word_valid(w, embed_h, n2);
    crate::presentation_lemmas::lemma_equiv_concat_left(data.p2, w, empty_word(), embed_h);
    assert(concat(empty_word(), embed_h) =~= embed_h) by {
        assert(concat(empty_word(), embed_h).len() == embed_h.len());
        assert forall|k: int| 0 <= k < embed_h.len()
            implies concat(empty_word(), embed_h)[k] == embed_h[k] by {}
    }

    lemma_g2_one_shot_subgroup_restore(data, concat(w, embed_h), h, syls);
}

//  ============================================================
//  Part I1d: Identification relator triviality
//  ============================================================

///  If concat(a, inv(b)) ≡ ε in G, then a ≡ b.
///  Proof: right-multiply by b → a·(inv(b)·b) ≡ a, and (a·inv(b))·b ≡ b.
///  Symmetry + transitivity gives a ≡ b.
proof fn lemma_diff_trivial_implies_equiv(
    p: Presentation, a: Word, b: Word,
)
    requires
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        equiv_in_presentation(p, concat(a, inverse_word(b)), empty_word()),
    ensures
        equiv_in_presentation(p, a, b),
{
    let n = p.num_generators;
    let inv_b = inverse_word(b);
    crate::word::lemma_inverse_word_valid(b, n);
    crate::word::lemma_concat_word_valid(a, inv_b, n);
    //  Chain 1: (a · inv(b)) · b ≡ ε · b = b
    crate::presentation_lemmas::lemma_equiv_concat_left(p,
        concat(a, inv_b), empty_word(), b);
    //  Chain 2: inv(b) · b ≡ ε → a · (inv(b) · b) ≡ a · ε = a
    crate::presentation_lemmas::lemma_word_inverse_left(p, b);
    crate::presentation_lemmas::lemma_equiv_concat_right(p,
        a, concat(inv_b, b), empty_word());
    //  Both converge on m = concat(concat(a, inv(b)), b):
    //    ≡ b (chain 1) and ≡ a (chain 2, via assoc =~=)
    //  Symmetry + transitivity: a ≡ b
    crate::word::lemma_concat_word_valid(inv_b, b, n);
    crate::word::lemma_concat_word_valid(a, concat(inv_b, b), n);
    //  Z3 needs explicit associativity for Seq concat
    assert(concat(a, concat(inv_b, b)) =~= concat(concat(a, inv_b), b));
    crate::presentation::lemma_equiv_symmetric(p,
        concat(a, concat(inv_b, b)), a);
    crate::presentation::lemma_equiv_transitive(p,
        a, concat(a, concat(inv_b, b)), b);
}

///  Helper: establish embed_b(k_diff) ≡ ε in G₂ from the one-shot decomposition.
proof fn lemma_ident_g2_diff_trivial(
    data: AmalgamatedData, h_prime: Word, k_combined: Word, k_diff: Word, g2_product: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h_prime, k_size(data)),
        word_valid(k_combined, k_size(data)),
        word_valid(k_diff, k_size(data)),
        word_valid(g2_product, data.p2.num_generators),
        k_diff =~= concat(h_prime, inverse_word(k_combined)),
        apply_embedding(b_words(data), k_combined) =~= g2_product,
        b_rcoset_rep(data, g2_product) =~= empty_word(),
        b_rcoset_h(data, g2_product) =~= h_prime,
    ensures
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), k_diff), empty_word()),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    reveal(presentation_valid);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    crate::benign::lemma_apply_embedding_concat(b_words(data), h_prime, inverse_word(k_combined));
    crate::benign::lemma_apply_embedding_valid(b_words(data), k_combined, n2);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    crate::benign::lemma_apply_embedding_inverse(b_words(data), k_combined);

    let embed_b_kcomb = apply_embedding(b_words(data), k_combined);
    let embed_b_hprime = apply_embedding(b_words(data), h_prime);
    crate::word::lemma_inverse_word_valid(embed_b_kcomb, n2);
    crate::word::lemma_concat_word_valid(embed_b_hprime, inverse_word(embed_b_kcomb), n2);

    //  Use k_combined directly as h_witness for decomposition (no need for subgroup_to_k_word)
    lemma_b_rcoset_rep_props(data, g2_product);

    //  Precondition for b_rcoset_decomposition: equiv(embed_b(k_combined), concat(g2_product, inv(rep)))
    //  Since rep =~= ε: concat(g2_product, inv(ε)) =~= g2_product =~= embed_b(k_combined)
    assert(inverse_word(b_rcoset_rep(data, g2_product)) =~= empty_word());
    assert(concat(g2_product, inverse_word(b_rcoset_rep(data, g2_product))) =~= g2_product);
    crate::presentation::lemma_equiv_refl(p2, apply_embedding(b_words(data), k_combined));
    lemma_b_rcoset_decomposition(data, g2_product, k_combined);
    //  gives: equiv(concat(embed_b(b_rcoset_h(g2_product)), b_rcoset_rep(g2_product)), g2_product)
    //  Since b_rcoset_h =~= h_prime and rep =~= ε: equiv(embed_b_hprime, embed_b_kcomb)

    //  embed_b(h') · inv(embed_b(k_combined)) ≡ embed_b(k_combined) · inv(embed_b(k_combined)) ≡ ε
    crate::presentation_lemmas::lemma_equiv_concat_left(p2,
        embed_b_hprime, embed_b_kcomb, inverse_word(embed_b_kcomb));
    crate::presentation_lemmas::lemma_word_inverse_right(p2, embed_b_kcomb);
    crate::presentation::lemma_equiv_transitive(p2,
        concat(embed_b_hprime, inverse_word(embed_b_kcomb)),
        concat(embed_b_kcomb, inverse_word(embed_b_kcomb)),
        empty_word());
    //  embed_b(k_diff) =~= concat(embed_b_hprime, inv(embed_b_kcomb)) ≡ ε
    crate::benign::lemma_apply_embedding_valid(b_words(data), k_diff, n2);
}

///  Helper: transfer identification isomorphism → g1_product ≡ embed_a(h).
proof fn lemma_ident_g1_product_equiv(
    data: AmalgamatedData, i: int, h: Word, h_prime: Word,
    k_combined: Word, k_diff: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(h_prime, k_size(data)),
        word_valid(k_combined, k_size(data)),
        word_valid(k_diff, k_size(data)),
        0 <= i < data.identifications.len() as int,
        identifications_isomorphic(data),
        k_diff =~= concat(h_prime, inverse_word(k_combined)),
        k_combined =~= concat(Seq::new(1, |_j: int| Symbol::Inv(i as nat)), h),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), k_diff), empty_word()),
    ensures ({
        let u_i = data.identifications[i].0;
        let embed_a_h = apply_embedding(a_words(data), h);
        let embed_a_hprime = apply_embedding(a_words(data), h_prime);
        equiv_in_presentation(data.p1,
            concat(u_i, embed_a_hprime), embed_a_h)
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let u_i = data.identifications[i].0;
    reveal(presentation_valid);

    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }

    //  Step A: Transfer embed_b(k_diff) ≡ ε in G₂ → embed_a(k_diff) ≡ ε in G₁
    //  identifications_isomorphic gives the biconditional for any K-word
    //  Z3 should fire the forall with w = k_diff (word_valid(k_diff, k_size(data)) is a precondition)

    //  Step B: embed_a(k_diff) =~= concat(embed_a(h'), inv(embed_a(k_combined)))
    crate::benign::lemma_apply_embedding_concat(a_words(data), h_prime, inverse_word(k_combined));
    crate::benign::lemma_apply_embedding_inverse(a_words(data), k_combined);
    crate::benign::lemma_apply_embedding_valid(a_words(data), k_combined, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    let embed_a_h = apply_embedding(a_words(data), h);
    let embed_a_hprime = apply_embedding(a_words(data), h_prime);
    let embed_a_kcomb = apply_embedding(a_words(data), k_combined);
    crate::word::lemma_inverse_word_valid(embed_a_kcomb, n1);

    //  Step C: embed_a(h') ≡ embed_a(k_combined) (from a·inv(b) ≡ ε → a ≡ b)
    //  embed_a(k_diff) =~= concat(embed_a(h'), inv(embed_a(k_combined))) ≡ ε (from step A+B)
    crate::word::lemma_concat_word_valid(embed_a_hprime, inverse_word(embed_a_kcomb), n1);
    lemma_diff_trivial_implies_equiv(p1, embed_a_hprime, embed_a_kcomb);

    //  Step D: embed_a(k_combined) =~= concat(inv(u_i), embed_a(h))
    let k_inv_i = Seq::new(1, |_j: int| Symbol::Inv(i as nat));
    crate::benign::lemma_apply_embedding_concat(a_words(data), k_inv_i, h);
    assert(apply_embedding(a_words(data), k_inv_i) =~= inverse_word(u_i)) by {
        reveal_with_fuel(crate::benign::apply_embedding, 2);
        assert(a_words(data)[i] == u_i);
    }
    //  So embed_a(k_combined) =~= concat(inv(u_i), embed_a(h))
    //  And from step C: embed_a(h') ≡ embed_a(k_combined) =~= concat(inv(u_i), embed_a(h))

    //  Step E: concat(u_i, embed_a(h')) ≡ embed_a(h)
    crate::word::lemma_inverse_word_valid(u_i, n1);
    crate::word::lemma_concat_word_valid(u_i, embed_a_hprime, n1);
    crate::word::lemma_concat_word_valid(inverse_word(u_i), embed_a_h, n1);
    crate::word::lemma_concat_word_valid(u_i, concat(inverse_word(u_i), embed_a_h), n1);

    //  u_i · embed_a(h') ≡ u_i · embed_a(k_combined) =~= u_i · concat(inv(u_i), embed_a(h))
    crate::presentation_lemmas::lemma_equiv_concat_right(p1,
        u_i, embed_a_hprime, embed_a_kcomb);

    //  u_i · inv(u_i) ≡ ε → (u_i · inv(u_i)) · embed_a(h) ≡ ε · embed_a(h) = embed_a(h)
    crate::presentation_lemmas::lemma_word_inverse_right(p1, u_i);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1,
        concat(u_i, inverse_word(u_i)), empty_word(), embed_a_h);
    //  Z3 needs explicit associativity for Seq concat
    assert(concat(u_i, concat(inverse_word(u_i), embed_a_h))
        =~= concat(concat(u_i, inverse_word(u_i)), embed_a_h));

    //  Chain: concat(u_i, embed_a(h')) ≡ concat(u_i, concat(inv(u_i), embed_a(h))) ≡ embed_a(h)
    crate::presentation::lemma_equiv_transitive(p1,
        concat(u_i, embed_a_hprime),
        concat(u_i, concat(inverse_word(u_i), embed_a_h)),
        embed_a_h);
}

///  Helper: build the K-word difference and prove g1_product ≡ embed_a(h) via isomorphism.
///  Extracted from the main identification relator proof to reduce rlimit pressure.
proof fn lemma_ident_isomorphism_transfer(
    data: AmalgamatedData, i: int, h: Word, h_prime: Word, g2_product: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(h_prime, k_size(data)),
        word_valid(g2_product, data.p2.num_generators),
        0 <= i < data.identifications.len() as int,
        identifications_isomorphic(data),
        b_rcoset_rep(data, g2_product) =~= empty_word(),
        b_rcoset_h(data, g2_product) =~= h_prime,
        apply_embedding(b_words(data),
            concat(Seq::new(1, |_j: int| Symbol::Inv(i as nat)), h)) =~= g2_product,
    ensures ({
        let u_i = data.identifications[i].0;
        let embed_a_h = apply_embedding(a_words(data), h);
        let embed_a_hprime = apply_embedding(a_words(data), h_prime);
        equiv_in_presentation(data.p1, concat(u_i, embed_a_hprime), embed_a_h)
    }),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let v_i = data.identifications[i].1;
    let inv_vi = inverse_word(v_i);
    reveal(presentation_valid);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    let k_inv_i = Seq::new(1, |_j: int| Symbol::Inv(i as nat));
    let k_combined = concat(k_inv_i, h);
    assert(word_valid(k_combined, k_size(data))) by {
        assert(word_valid(k_inv_i, k_size(data))) by {
            assert forall|k: int| 0 <= k < k_inv_i.len()
                implies symbol_valid(#[trigger] k_inv_i[k], k_size(data)) by {}
        }
        assert forall|k: int| 0 <= k < k_combined.len()
            implies symbol_valid(#[trigger] k_combined[k], k_size(data)) by {
                if k < 1 {} else {}
            }
    }

    let k_diff = concat(h_prime, inverse_word(k_combined));
    crate::word::lemma_inverse_word_valid(k_combined, k_size(data));
    assert(word_valid(k_diff, k_size(data))) by {
        assert forall|k: int| 0 <= k < k_diff.len()
            implies symbol_valid(#[trigger] k_diff[k], k_size(data)) by {
                if k < h_prime.len() as int {} else {}
            }
    }

    lemma_ident_g2_diff_trivial(data, h_prime, k_combined, k_diff, g2_product);
    lemma_ident_g1_product_equiv(data, i, h, h_prime, k_combined, k_diff);
}

///  Identification relator triviality: u_i · inv(shift(v_i)) acts trivially.
///  This is the mathematical heart — uses identifications_isomorphic.
///
///  Proof sketch:
///  1. inv(shift(v_i)) acts via G₂: product inv(v_i)·embed_b(h) ∈ B → (h', syls)
///  2. u_i acts via G₁: product u_i·embed_a(h') ∈ A → (h'', syls)
///  3. By identification isomorphism: embed_a(h') ≡ inv(u_i)·embed_a(h) in G₁
///  4. So u_i·embed_a(h') ≡ embed_a(h) → h'' = h
#[verifier::rlimit(300)]
pub proof fn lemma_identification_relator_acts_trivially(
    data: AmalgamatedData, i: int, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        0 <= i < data.identifications.len() as int,
        identifications_isomorphic(data),
        action_preserves_canonical(data),
    ensures
        act_word(data, amalgamation_relator(data, i), h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    let (u_i, v_i) = (data.identifications[i].0, data.identifications[i].1);
    let shifted_v = shift_word(v_i, n1);
    let relator = amalgamation_relator(data, i);
    //  relator = concat(u_i, inverse_word(shifted_v))
    reveal(presentation_valid);

    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }
    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    //  Step 1: process inv(shift(v_i)) via G₂ one-shot
    //  inv(shift(v_i)) = shift(inv(v_i)) (shift commutes with inverse)
    //  shift(inv(v_i)) =~= inv(shift(v_i)): shift commutes with inverse
    crate::free_product::lemma_shift_inverse_word(v_i, n1);

    //  Decompose relator: u_i · shift(inv(v_i))
    //  Right-to-left: process shift(inv(v_i)) first, then u_i
    lemma_act_word_concat(data, u_i, inverse_word(shifted_v), h, syls);

    //  inv(v_i) ≡ ε in G₂? No — but inv(v_i) IS in the B-subgroup.
    //  The act_word of shift(inv(v_i)) uses the G₂ one-shot.
    crate::word::lemma_inverse_word_valid(v_i, n2);
    lemma_act_word_eq_g2_one_shot(data, inverse_word(v_i), h, syls);
    //  act_word(shift(inv(v_i)), h, syls) = g2_one_shot(concat(inv(v_i), embed_b(h)), syls)

    let embed_h_b = apply_embedding(b_words(data), h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    let inv_vi = inverse_word(v_i);
    let g2_product = concat(inv_vi, embed_h_b);
    crate::word::lemma_concat_word_valid(inv_vi, embed_h_b, n2);

    //  g2_product ∈ B → b_rcoset_rep = ε
    lemma_generator_in_generated_subgroup(p2, b_words(data), i);
    lemma_subgroup_inverse(p2, b_words(data), v_i);
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    lemma_subgroup_concat(p2, b_words(data), inv_vi, embed_h_b);
    lemma_b_rcoset_in_subgroup(data, g2_product);

    //  g2_one_shot gives (h', syls) where h' = b_rcoset_h(g2_product)
    let (h_prime, syls_prime) = g2_one_shot_action(data, g2_product, syls);
    //  h_prime = b_rcoset_h(g2_product) since rep = ε (subgroup case)
    assert(h_prime == b_rcoset_h(data, g2_product));
    assert(syls_prime == syls);

    //  Establish h_prime is canonical via action_preserves_canonical
    lemma_action_preserves_canonical(data, shift_word(inverse_word(v_i), n1), h, syls);
    //  gives is_canonical_state(data, h_prime, syls_prime) → word_valid(h_prime, k_size(data))

    //  Step 2: u_i via G₁ one-shot on (h', syls')
    assert(word_valid(u_i, n1));
    lemma_act_word_eq_one_shot(data, u_i, h_prime, syls_prime);
    //  act_word(u_i, h', syls') = g1_one_shot(concat(u_i, embed_a(h')), syls')

    //  Key: show concat(u_i, embed_a(h')) ≡ embed_a(h) via K-word isomorphism transfer
    //  embed_b(k_combined) =~= g2_product needs the Seq::new embedding fact
    assert(apply_embedding(b_words(data),
        concat(Seq::new(1, |_j: int| Symbol::Inv(i as nat)), h)) =~= g2_product) by {
        let k_inv_i = Seq::new(1, |_j: int| Symbol::Inv(i as nat));
        crate::benign::lemma_apply_embedding_concat(b_words(data), k_inv_i, h);
        assert(apply_embedding(b_words(data), k_inv_i) =~= inv_vi) by {
            reveal_with_fuel(crate::benign::apply_embedding, 2);
            assert(b_words(data)[i] == v_i);
        }
    }
    lemma_ident_isomorphism_transfer(data, i, h, h_prime, g2_product);

    //  g1_product ≡ embed_a(h) → one_shot_subgroup_restore gives (h, syls)
    let embed_h_prime_a = apply_embedding(a_words(data), h_prime);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    let g1_product = concat(u_i, embed_h_prime_a);
    crate::word::lemma_concat_word_valid(u_i, embed_h_prime_a, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    lemma_one_shot_subgroup_restore(data, g1_product, h, syls_prime);
}

//  ============================================================
//  Part I1e: Assembly — action_well_defined proof
//  ============================================================

///  concat(inv(r), r) acts trivially via inverse pair decomposition.
///  Induction: r = [s] + r_rest → concat(inv(r), r) =~= concat(inv(r_rest), concat(inv_pair(s), r_rest))
///  → remove inv_pair(s) (trivially-acting) → concat(inv(r_rest), r_rest) → IH.
#[verifier::rlimit(200)]
proof fn lemma_inv_r_concat_r_trivial(
    data: AmalgamatedData, r: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        action_preserves_canonical(data),
        word_valid(r, amalgamated_free_product(data).num_generators),
    ensures
        act_word(data, concat(inverse_word(r), r), h, syls) == (h, syls),
    decreases r.len(),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let fp = crate::free_product::free_product(data.p1, data.p2);
    crate::amalgamated_free_product::lemma_add_relators_num_generators(fp,
        crate::amalgamated_free_product::amalgamation_relators(data));
    assert(amalgamated_free_product(data).num_generators == n1 + n2);

    if r.len() == 0 {
        assert(concat(inverse_word(r), r) =~= empty_word());
        lemma_act_word_empty(data, h, syls);
    } else {
        let s = r.first();
        let r_rest = r.drop_first();
        let s_word = Seq::new(1, |_i: int| s);

        //  inv(r) =~= concat(inv(r_rest), [inv(s)]) (from lemma_inverse_concat)
        crate::word::lemma_inverse_concat(s_word, r_rest);

        //  Key =~=: concat(inv(r), r) =~= concat(inv(r_rest), concat(inv_pair(s), r_rest))
        let inv_pair = inverse_pair_word(s);
        assert(concat(inverse_word(r), r)
            =~= concat(inverse_word(r_rest), concat(inv_pair, r_rest)));

        //  The intermediate state after processing r_rest is canonical
        let (sh, ss) = act_word(data, r_rest, h, syls);
        lemma_action_preserves_canonical(data, r_rest, h, syls);

        //  inv_pair(s) acts trivially on the canonical intermediate state
        assert(symbol_valid(s, n1 + n2));
        assert(generator_index(s) < n1 + n2);
        if generator_index(s) < n1 {
            lemma_inverse_pair_g1(data, s, sh, ss);
        } else {
            lemma_inverse_pair_g2(data, s, sh, ss);
        }

        //  Remove the inverse pair
        lemma_insert_trivial_at_state(data,
            inverse_word(r_rest), inv_pair, r_rest, h, syls);

        //  IH: concat(inv(r_rest), r_rest) acts trivially
        assert(word_valid(r_rest, n1 + n2));
        lemma_inv_r_concat_r_trivial(data, r_rest, h, syls);
    }
}

///  If r acts trivially on a specific canonical state, then inv(r) acts trivially on that state too.
///  Proof: concat(inv(r), r) acts trivially (inverse pairs).
///  act_word(concat(inv(r), r), h, syls) = act_word(inv(r), act_word(r, h, syls)) = act_word(inv(r), (h, syls)) = (h, syls).
proof fn lemma_trivial_action_inverse(
    data: AmalgamatedData, r: Word, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        action_preserves_canonical(data),
        word_valid(r, amalgamated_free_product(data).num_generators),
        act_word(data, r, h, syls) == (h, syls),
    ensures
        act_word(data, inverse_word(r), h, syls) == (h, syls),
{
    lemma_inv_r_concat_r_trivial(data, r, h, syls);
    lemma_act_word_concat(data, inverse_word(r), r, h, syls);
}

///  The action is well-defined: all AFP relators and inverse pairs act trivially.
///  The output of a_rcoset_h satisfies the left_h_part fixed-point condition.
///  Uses equiv invariance: embed_a(h) ≡ target_r, and left_h_part is equiv-invariant.
proof fn lemma_a_rcoset_h_left_canonical(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(g, inverse_word(a_rcoset_rep(data, g)))),
    ensures ({
        let h = a_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& left_h_part(data, apply_embedding(a_words(data), h)) =~= h
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    reveal(presentation_valid);

    lemma_a_rcoset_h_satisfiable(data, g, h_witness);
    let h = a_rcoset_h(data, g);
    let rep = a_rcoset_rep(data, g);
    let target_r = concat(g, inverse_word(rep));
    let embed_h = apply_embedding(a_words(data), h);

    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  target_r ∈ A and word_valid
    lemma_a_rcoset_rep_props(data, g);
    crate::word::lemma_inverse_word_valid(rep, n1);
    crate::word::lemma_concat_word_valid(g, inverse_word(rep), n1);

    //  embed_a(h) ∈ A → both reps = ε
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    lemma_in_subgroup_both_reps_eps(data, embed_h);
    //  target_r ∈ A → both reps = ε
    lemma_in_subgroup_both_reps_eps(data, target_r);

    //  Use left_h_part equiv invariance: embed_a(h) ≡ target_r → left_h_part equal
    //  h_witness for embed_a(h): h (reflexive)
    crate::presentation::lemma_equiv_refl(p1, embed_h);
    //  h_witness for target_r: h (embed_a(h) ≡ target_r)
    //  Need equiv(embed_a(h), concat(inv(left_canonical_rep(embed_h)), embed_h)) = equiv(embed_a(h), embed_h) [since rep=ε]
    //  And equiv(embed_a(h), concat(inv(left_canonical_rep(target_r)), target_r)) = equiv(embed_a(h), target_r) [since rep=ε]
    lemma_left_h_part_equiv_invariant(data, embed_h, target_r, h, h);
    //  left_h_part(embed_a(h)) =~= left_h_part(target_r)

    //  Now: left_h_part(target_r) uses target = target_r (since rep=ε)
    //  And: a_rcoset_h(g) uses target = target_r (by definition)
    //  BOTH left_h_min_len and a_rcoset_h_min_len compute on has_left_h_witness_of_len(data, target_r, l)
    //  (since concat(inv(ε), target_r) =~= target_r =~= concat(g, inv(rep)))
    //  So left_h_part(target_r) and a_rcoset_h(g) pick the same h.
    //  Z3 needs help seeing the internal targets are =~=:
    assert(concat(inverse_word(left_canonical_rep(data, target_r)), target_r) =~= target_r);
    assert(concat(g, inverse_word(a_rcoset_rep(data, g))) =~= target_r);
    //  Therefore: left_h_part(target_r) =~= a_rcoset_h(g) = h
    assert(left_h_part(data, target_r) =~= h);
    //  And from equiv invariance: left_h_part(embed_a(h)) =~= left_h_part(target_r) =~= h
}

///  A-witness transfer: if there's an A-side h-witness of length l for embed_a(h0),
///  then there's a B-side h-witness of length l for embed_b(h0).
///  Uses identifications_isomorphic to transfer between G₁ and G₂ equiv classes.
proof fn lemma_a_witness_to_b_witness(
    data: AmalgamatedData, h0: Word, l: nat,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        word_valid(h0, k_size(data)),
        has_left_h_witness_of_len(data, apply_embedding(a_words(data), h0), l),
    ensures
        has_right_h_witness_of_len(data, apply_embedding(b_words(data), h0), l),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    let k = k_size(data);
    reveal(presentation_valid);

    //  Extract A-witness: h' with embed_a(h') ≡ embed_a(h0) in G₁, h'.len() == l
    let h_prime: Word = choose|h: Word| word_valid(h, k) && h.len() == l
        && equiv_in_presentation(p1, apply_embedding(a_words(data), h),
            apply_embedding(a_words(data), h0));

    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }
    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    //  embed_a(h') ≡ embed_a(h0) → embed_a(concat(h', inv(h0))) ≡ ε in G₁
    //  Step: a ≡ b → a·b⁻¹ ≡ ε
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h0, n1);
    crate::word::lemma_inverse_word_valid(apply_embedding(a_words(data), h0), n1);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1,
        apply_embedding(a_words(data), h_prime),
        apply_embedding(a_words(data), h0),
        inverse_word(apply_embedding(a_words(data), h0)));
    crate::presentation_lemmas::lemma_word_inverse_right(p1,
        apply_embedding(a_words(data), h0));
    crate::presentation::lemma_equiv_transitive(p1,
        concat(apply_embedding(a_words(data), h_prime),
               inverse_word(apply_embedding(a_words(data), h0))),
        concat(apply_embedding(a_words(data), h0),
               inverse_word(apply_embedding(a_words(data), h0))),
        empty_word());

    //  embed_a(concat(h', inv(h0))) =~= concat(embed_a(h'), inv(embed_a(h0)))
    crate::word::lemma_inverse_word_valid(h0, k);
    crate::benign::lemma_apply_embedding_concat(a_words(data), h_prime, inverse_word(h0));
    crate::benign::lemma_apply_embedding_inverse(a_words(data), h0);

    //  So: equiv(embed_a(concat(h', inv(h0))), ε) in G₁
    let diff = concat(h_prime, inverse_word(h0));
    assert(word_valid(diff, k)) by {
        assert forall|j: int| 0 <= j < diff.len()
            implies symbol_valid(#[trigger] diff[j], k)
        by { if j < h_prime.len() as int {} else {} }
    }

    //  By identifications_isomorphic: equiv(embed_b(diff), ε) in G₂
    //  (identifications_isomorphic quantifies over word_valid(w, k))

    //  equiv(embed_b(diff), ε) → equiv(embed_b(h'), embed_b(h0)) in G₂
    crate::benign::lemma_apply_embedding_concat(b_words(data), h_prime, inverse_word(h0));
    crate::benign::lemma_apply_embedding_inverse(b_words(data), h0);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h0, n2);
    crate::word::lemma_inverse_word_valid(apply_embedding(b_words(data), h0), n2);
    crate::word::lemma_concat_word_valid(
        apply_embedding(b_words(data), h_prime),
        inverse_word(apply_embedding(b_words(data), h0)), n2);
    lemma_diff_trivial_implies_equiv(p2,
        apply_embedding(b_words(data), h_prime),
        apply_embedding(b_words(data), h0));

    //  h' is a B-witness: word_valid(h', k) && h'.len() == l && equiv(embed_b(h'), embed_b(h0)) in G₂
    assert(has_right_h_witness_of_len(data, apply_embedding(b_words(data), h0), l));
}

///  Reverse transfer: B-witness → A-witness.
proof fn lemma_b_witness_to_a_witness(
    data: AmalgamatedData, h0: Word, l: nat,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        word_valid(h0, k_size(data)),
        has_right_h_witness_of_len(data, apply_embedding(b_words(data), h0), l),
    ensures
        has_left_h_witness_of_len(data, apply_embedding(a_words(data), h0), l),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    let k = k_size(data);
    reveal(presentation_valid);

    let h_prime: Word = choose|h: Word| word_valid(h, k) && h.len() == l
        && equiv_in_presentation(p2, apply_embedding(b_words(data), h),
            apply_embedding(b_words(data), h0));

    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }
    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    //  embed_b(h') ≡ embed_b(h0) → embed_b(concat(h', inv(h0))) ≡ ε in G₂
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h0, n2);
    crate::word::lemma_inverse_word_valid(apply_embedding(b_words(data), h0), n2);
    crate::presentation_lemmas::lemma_equiv_concat_left(p2,
        apply_embedding(b_words(data), h_prime),
        apply_embedding(b_words(data), h0),
        inverse_word(apply_embedding(b_words(data), h0)));
    crate::presentation_lemmas::lemma_word_inverse_right(p2,
        apply_embedding(b_words(data), h0));
    crate::presentation::lemma_equiv_transitive(p2,
        concat(apply_embedding(b_words(data), h_prime),
               inverse_word(apply_embedding(b_words(data), h0))),
        concat(apply_embedding(b_words(data), h0),
               inverse_word(apply_embedding(b_words(data), h0))),
        empty_word());

    crate::word::lemma_inverse_word_valid(h0, k);
    crate::benign::lemma_apply_embedding_concat(b_words(data), h_prime, inverse_word(h0));
    crate::benign::lemma_apply_embedding_inverse(b_words(data), h0);

    let diff = concat(h_prime, inverse_word(h0));
    assert(word_valid(diff, k)) by {
        assert forall|j: int| 0 <= j < diff.len()
            implies symbol_valid(#[trigger] diff[j], k)
        by { if j < h_prime.len() as int {} else {} }
    }

    //  By identifications_isomorphic (reverse direction): equiv(embed_a(diff), ε) in G₁
    crate::benign::lemma_apply_embedding_concat(a_words(data), h_prime, inverse_word(h0));
    crate::benign::lemma_apply_embedding_inverse(a_words(data), h0);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h0, n1);
    crate::word::lemma_inverse_word_valid(apply_embedding(a_words(data), h0), n1);
    crate::word::lemma_concat_word_valid(
        apply_embedding(a_words(data), h_prime),
        inverse_word(apply_embedding(a_words(data), h0)), n1);
    lemma_diff_trivial_implies_equiv(p1,
        apply_embedding(a_words(data), h_prime),
        apply_embedding(a_words(data), h0));

    assert(has_left_h_witness_of_len(data, apply_embedding(a_words(data), h0), l));
}

///  Helper: b_rcoset_h_min_len(embed_b(h)) == h.len() when h = left_h_part(embed_a(h)).
///  Uses A↔B witness transfer + no_pred_below.
#[verifier::rlimit(200)]
proof fn lemma_b_min_len_eq(
    data: AmalgamatedData, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        word_valid(h, k_size(data)),
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
    ensures
        b_rcoset_h_min_len(data, apply_embedding(b_words(data), h)) == h.len(),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    reveal(presentation_valid);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }
    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }

    let embed_b_h = apply_embedding(b_words(data), h);
    let embed_a_h = apply_embedding(a_words(data), h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  embed_b(h) ∈ B → rep = ε
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    lemma_b_rcoset_in_subgroup(data, embed_b_h);

    let target_bh = concat(embed_b_h, inverse_word(b_rcoset_rep(data, embed_b_h)));
    assert(target_bh =~= embed_b_h);

    //  h is a B-witness at h.len() → min_len <= h.len()
    crate::presentation::lemma_equiv_refl(p2, embed_b_h);
    let pred_b = |l2: nat| has_right_h_witness_of_len(data, target_bh, l2);
    assert(pred_b(h.len() as nat));
    lemma_nat_well_ordering(pred_b, h.len() as nat);

    //  h.len() is the A-min-len → no B-witness shorter than h.len()
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    lemma_in_subgroup_both_reps_eps(data, embed_a_h);
    let target_lh = concat(inverse_word(left_canonical_rep(data, embed_a_h)), embed_a_h);
    assert(target_lh =~= embed_a_h);
    crate::presentation::lemma_equiv_refl(p1, embed_a_h);
    lemma_left_h_part_full_props(data, embed_a_h, h);
    let pred_a = |l2: nat| has_left_h_witness_of_len(data, target_lh, l2);
    assert(pred_a(h.len() as nat));
    lemma_nat_well_ordering(pred_a, h.len() as nat);

    //  Transfer: pred_b(l) → pred_a(l)
    assert forall|l: nat| pred_b(l) implies #[trigger] pred_a(l) by {
        lemma_b_witness_to_a_witness(data, h, l);
    }
    lemma_no_pred_below_transfer(pred_a, pred_b, h.len() as nat);
    //  no_pred_below(pred_b, h.len()) + pred_b(h.len()) → h.len() satisfies the choose predicate

    //  Uniqueness: b_rcoset_h_min_len's choose also satisfies, mutual exclusion → equal
    let bl = b_rcoset_h_min_len(data, embed_b_h);
    //  bl satisfies the choose predicate (from satisfiability via nat_well_ordering)
    //  → pred_b(bl) && no_pred_below(pred_b, bl)
    //  Mutual exclusion: bl >= h.len() (from no_pred_below(pred_b, bl) + pred_b(h.len()))
    //                    h.len() >= bl (from no_pred_below(pred_b, h.len()) + pred_b(bl))
    lemma_no_pred_below_implies_ge(pred_b, h.len() as nat, bl);
    lemma_no_pred_below_implies_ge(pred_b, bl, h.len() as nat);
}

///  a_rcoset_h output satisfies the b_rcoset_h fixed-point condition.
///  Uses: witness transfer (A↔B) + lex rank injectivity to show the B-choose gives h.
#[verifier::rlimit(200)]
proof fn lemma_a_rcoset_h_b_canonical(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(g, inverse_word(a_rcoset_rep(data, g)))),
    ensures ({
        let h = a_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h
    }),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    let k = k_size(data);
    reveal(presentation_valid);

    lemma_a_rcoset_h_satisfiable(data, g, h_witness);
    let h = a_rcoset_h(data, g);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }
    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }

    let embed_b_h = apply_embedding(b_words(data), h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    //  embed_b(h) ∈ B → b_rcoset_rep = ε
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    lemma_b_rcoset_in_subgroup(data, embed_b_h);

    //  h is a B-witness → b_rcoset_h satisfiable
    crate::presentation::lemma_equiv_refl(p2, embed_b_h);
    lemma_b_rcoset_h_satisfiable(data, embed_b_h, h);
    let h_b = b_rcoset_h(data, embed_b_h);
    //  h_b: word_valid, h_b.len() == b_rcoset_h_min_len, equiv(embed_b(h_b), embed_b_h)
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_b, n2);

    //  Strategy: show h and h_b have same length AND same lex rank → same word (by injectivity)

    //  Step 1: h_b.len() <= h.len() (h is a B-candidate, h_b is B-min-len)
    //  (This follows from b_rcoset_h_min_len being the minimum.)

    //  Step 2: h.len() <= h_b.len() (transfer h_b to A-side, h is A-min-len)
    assert(has_right_h_witness_of_len(data, embed_b_h, h_b.len() as nat));
    lemma_b_witness_to_a_witness(data, h, h_b.len() as nat);
    //  Now: has_left_h_witness_of_len(embed_a(h), h_b.len())

    //  Step 3: length equality
    lemma_a_rcoset_h_left_canonical(data, g, h_witness);
    lemma_b_min_len_eq(data, h);
    //  Get h_b's full props to connect h_b.len() to b_rcoset_h_min_len
    crate::presentation::lemma_equiv_refl(p2, embed_b_h);
    lemma_b_rcoset_h_full_props(data, embed_b_h, h);
    assert(h_b.len() == h.len());
    let target_bh = concat(embed_b_h, inverse_word(b_rcoset_rep(data, embed_b_h)));
    assert(target_bh =~= embed_b_h);
    let hl = h.len() as nat;

    //  Setup for lex transfer
    let embed_a_h = apply_embedding(a_words(data), h);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    lemma_in_subgroup_both_reps_eps(data, embed_a_h);
    crate::presentation::lemma_equiv_refl(p1, embed_a_h);
    lemma_left_h_part_full_props(data, embed_a_h, h);
    let target_lh = concat(inverse_word(left_canonical_rep(data, embed_a_h)), embed_a_h);
    assert(target_lh =~= embed_a_h);

    //  Step 4: Same lex rank (both are min-lex at the same length for the same equiv class)
    //  Transfer at rank level: the rank-level B-witness at h_b's lex ↔ A-witness at same lex
    //  Since A and B witnesses at each (len, rank) coincide, the min-lex must agree too.
    //  h has lex == left_h_min_lex(embed_a_h) and h_b has lex == b_rcoset_h_min_lex(embed_b_h).
    //  Both are min-lex over the same set of K-words → same lex → same word.

    //  Use lex rank injectivity: same length + same lex rank → same word
    //  h and h_b satisfy the same B-choose predicate at (len, lex)
    //  h_b IS the choose result → h_b has len == bl and lex == br
    //  h satisfies the B-predicate too (equiv(embed_b(h), embed_b_h) by reflexivity)
    //  Both have len == bl. If lex(h) == lex(h_b), then h =~= h_b by injectivity.
    //  lex(h_b) == br (from choose). lex(h) >= br (from min-lex: h_b is min).
    //  But also: h is in the B-witness set at (bl, lex(h)). Transfer to A-side:
    //  h is in A-witness set at (bl, lex(h)). h is the A-min-lex at length bl.
    //  Step 4: Same lex rank — same pattern at the rank level
    //  A-side: has_left_h_witness_of_len_rank(target_lh, h.len(), lex(h))
    //  B-side: has_right_h_witness_of_len_rank(target_bh, h.len(), lex(h_b))
    //  Transfer at rank level: pred_b_rank(r) → pred_a_rank(r)
    //  + no_pred_below on A-side → no_pred_below on B-side
    //  → min lex for B == min lex for A == lex(h)

    let hl = h.len() as nat;
    let pred_a_rank = |r: nat| has_left_h_witness_of_len_rank(data, target_lh, hl, r);
    let pred_b_rank = |r: nat| has_right_h_witness_of_len_rank(data, target_bh, hl, r);

    //  h is a B-witness at (hl, lex(h))
    let hr = word_lex_rank_base(h, h_lex_base(data));
    assert(pred_b_rank(hr));

    //  Transfer: pred_b_rank(r) → pred_a_rank(r)
    assert forall|r: nat| pred_b_rank(r) implies #[trigger] pred_a_rank(r) by {
        //  Extract h'' from B-witness: embed_b(h'') ≡ embed_b(h), h''.len() == hl, lex == r
        let h_r: Word = choose|hw: Word| word_valid(hw, k) && hw.len() == hl
            && word_lex_rank_base(hw, h_lex_base(data)) == r
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw), target_bh);
        //  Transfer h_r from B to A
        crate::benign::lemma_apply_embedding_valid(b_words(data), h_r, n2);
        crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
        crate::word::lemma_inverse_word_valid(apply_embedding(b_words(data), h), n2);
        crate::presentation_lemmas::lemma_equiv_concat_left(p2,
            apply_embedding(b_words(data), h_r), apply_embedding(b_words(data), h),
            inverse_word(apply_embedding(b_words(data), h)));
        crate::presentation_lemmas::lemma_word_inverse_right(p2, apply_embedding(b_words(data), h));
        crate::presentation::lemma_equiv_transitive(p2,
            concat(apply_embedding(b_words(data), h_r), inverse_word(apply_embedding(b_words(data), h))),
            concat(apply_embedding(b_words(data), h), inverse_word(apply_embedding(b_words(data), h))),
            empty_word());
        crate::word::lemma_inverse_word_valid(h, k);
        crate::benign::lemma_apply_embedding_concat(b_words(data), h_r, inverse_word(h));
        crate::benign::lemma_apply_embedding_inverse(b_words(data), h);
        let diff = concat(h_r, inverse_word(h));
        assert(word_valid(diff, k)) by {
            assert forall|j: int| 0 <= j < diff.len()
                implies symbol_valid(#[trigger] diff[j], k) by {
                    if j < h_r.len() as int {} else {}
                }
        }
        //  identifications_isomorphic: embed_b(diff) ≡ ε → embed_a(diff) ≡ ε
        //  → embed_a(h_r) ≡ embed_a(h) → h_r is an A-witness
        crate::benign::lemma_apply_embedding_concat(a_words(data), h_r, inverse_word(h));
        crate::benign::lemma_apply_embedding_inverse(a_words(data), h);
        crate::benign::lemma_apply_embedding_valid(a_words(data), h_r, n1);
        crate::word::lemma_inverse_word_valid(apply_embedding(a_words(data), h), n1);
        crate::word::lemma_concat_word_valid(
            apply_embedding(a_words(data), h_r),
            inverse_word(apply_embedding(a_words(data), h)), n1);
        lemma_diff_trivial_implies_equiv(p1,
            apply_embedding(a_words(data), h_r), embed_a_h);
    }

    //  Transfer no_smaller_h_lex from A to B using the dedicated transfer lemma
    //  A-side: no_smaller_h_lex(target_lh, hl, hr) — from left_h_part_full_props
    //  Need: B-rank transfer forall
    assert forall|r2: nat| has_right_h_witness_of_len_rank(data, target_bh, hl, r2)
        implies #[trigger] has_left_h_witness_of_len_rank(data, target_lh, hl, r2)
    by {
        //  Same proof as pred_b_rank → pred_a_rank but at rank level
        let h_r: Word = choose|hw: Word| word_valid(hw, k) && hw.len() == hl
            && word_lex_rank_base(hw, h_lex_base(data)) == r2
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw), target_bh);
        crate::benign::lemma_apply_embedding_valid(b_words(data), h_r, n2);
        crate::word::lemma_inverse_word_valid(apply_embedding(b_words(data), h), n2);
        crate::presentation_lemmas::lemma_equiv_concat_left(p2,
            apply_embedding(b_words(data), h_r), apply_embedding(b_words(data), h),
            inverse_word(apply_embedding(b_words(data), h)));
        crate::presentation_lemmas::lemma_word_inverse_right(p2, apply_embedding(b_words(data), h));
        crate::presentation::lemma_equiv_transitive(p2,
            concat(apply_embedding(b_words(data), h_r), inverse_word(apply_embedding(b_words(data), h))),
            concat(apply_embedding(b_words(data), h), inverse_word(apply_embedding(b_words(data), h))),
            empty_word());
        crate::word::lemma_inverse_word_valid(h, k);
        crate::benign::lemma_apply_embedding_concat(b_words(data), h_r, inverse_word(h));
        crate::benign::lemma_apply_embedding_inverse(b_words(data), h);
        let diff = concat(h_r, inverse_word(h));
        assert(word_valid(diff, k)) by {
            assert forall|j: int| 0 <= j < diff.len()
                implies symbol_valid(#[trigger] diff[j], k) by {
                    if j < h_r.len() as int {} else {}
                }
        }
        crate::benign::lemma_apply_embedding_concat(a_words(data), h_r, inverse_word(h));
        crate::benign::lemma_apply_embedding_inverse(a_words(data), h);
        crate::benign::lemma_apply_embedding_valid(a_words(data), h_r, n1);
        crate::word::lemma_inverse_word_valid(embed_a_h, n1);
        crate::word::lemma_concat_word_valid(
            apply_embedding(a_words(data), h_r), inverse_word(embed_a_h), n1);
        lemma_diff_trivial_implies_equiv(p1, apply_embedding(a_words(data), h_r), embed_a_h);
    }
    //  Establish no_smaller_h_lex on A-side from left_h_min_lex satisfiability
    lemma_left_h_min_lex_satisfiable(data, embed_a_h, h);
    assert(no_smaller_h_lex(data, target_lh, hl, hr));
    lemma_no_smaller_h_lex_transfer(data, target_lh, target_bh, hl, hr);

    //  Now: pred_b_rank(hr) && no_smaller_h_lex_g2(target_bh, hl, hr)
    //  Assert is_min_h_lex_g2 to establish the unique B-min-lex
    assert(is_min_h_lex_g2(data, target_bh, hl, hr));
    //  Scan gives us the satisfiability of the min-lex choose
    assert(no_smaller_h_lex_g2(data, target_bh, hl, 0nat));
    lemma_scan_min_h_lex_g2(data, target_bh, hl, 0, hr);
    //  Now b_rcoset_h_min_lex(embed_b_h) is satisfiable
    //  And hr satisfies both has_.. and no_smaller → hr IS the min → lex(h_b) == hr
    //  From the choose: h_b.lex == b_rcoset_h_min_lex. And b_rcoset_h_min_lex == hr (unique min).
    //  Use no_smaller_h_lex_g2 uniqueness: if two values satisfy is_min, they're equal
    //  Extract br's full choose properties via b_rcoset_h_full_props
    lemma_b_rcoset_h_full_props(data, embed_b_h, h);
    //  full_props ensures: h_b.len() == b_rcoset_h_min_len(embed_b_h) = hl
    //                     word_lex_rank_base(h_b, base) == b_rcoset_h_min_lex(embed_b_h) = br
    //                     equiv(embed_b(h_b), target_bh)
    //  Extract br (full_props already called above)
    let br = b_rcoset_h_min_lex(data, embed_b_h);
    assert(h_b.len() == hl);
    assert(word_lex_rank_base(h_b, h_lex_base(data)) == br);
    assert(has_right_h_witness_of_len_rank(data, target_bh, hl, br));
    assert(no_smaller_h_lex_g2(data, target_bh, hl, 0nat));
    lemma_scan_min_h_lex_g2(data, target_bh, hl, 0, br);
    //  hr has witness (h is B-witness at hr)
    assert(has_right_h_witness_of_len_rank(data, target_bh, hl, hr));
    //  Mutual exclusion: hr >= br AND br >= hr → hr == br
    lemma_no_smaller_g2_implies_ge(data, target_bh, hl, hr, br);
    lemma_no_smaller_g2_implies_ge(data, target_bh, hl, br, hr);

    //  Step 5: Apply lex rank injectivity
    assert(h_lex_base(data) > 0);
    assert forall|j: int| 0 <= j < h.len() implies
        crate::todd_coxeter::symbol_to_column(#[trigger] h[j]) < h_lex_base(data)
    by { assert(symbol_valid(h[j], k)); }
    assert forall|j: int| 0 <= j < h_b.len() implies
        crate::todd_coxeter::symbol_to_column(#[trigger] h_b[j]) < h_lex_base(data)
    by { assert(symbol_valid(h_b[j], k)); }
    lemma_word_lex_rank_base_injective(h, h_b, h_lex_base(data));
}

///  B-side self-consistency: b_rcoset_h output satisfies b_rcoset_h fixed point.
///  Mirrors lemma_a_rcoset_h_left_canonical for G₂.
proof fn lemma_b_rcoset_h_b_canonical(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness),
            concat(g, inverse_word(b_rcoset_rep(data, g)))),
    ensures ({
        let h = b_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    reveal(presentation_valid);

    lemma_b_rcoset_h_satisfiable(data, g, h_witness);
    let h = b_rcoset_h(data, g);
    let rep = b_rcoset_rep(data, g);
    let target_r = concat(g, inverse_word(rep));
    let embed_h = apply_embedding(b_words(data), h);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    lemma_b_rcoset_rep_props(data, g);
    crate::word::lemma_inverse_word_valid(rep, n2);
    crate::word::lemma_concat_word_valid(g, inverse_word(rep), n2);

    //  embed_b(h) ∈ B → both reps = ε
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    lemma_b_rcoset_in_subgroup(data, embed_h);
    //  target_r ∈ B
    lemma_b_rcoset_in_subgroup(data, target_r);

    //  Use b_rcoset_h equiv invariance: embed_b(h) ≡ target_r → b_rcoset_h equal
    crate::presentation::lemma_equiv_refl(p2, embed_h);
    lemma_b_rcoset_h_equiv_invariant(data, embed_h, target_r, h, h);
    //  b_rcoset_h(embed_b(h)) =~= b_rcoset_h(target_r)

    //  b_rcoset_h(target_r) uses same target as b_rcoset_h(g) when both ∈ B
    assert(concat(inverse_word(b_rcoset_rep(data, target_r)), target_r) =~= target_r);
    assert(concat(g, inverse_word(b_rcoset_rep(data, g))) =~= target_r);
    assert(b_rcoset_h(data, target_r) =~= h);
}

///  B-side cross: b_rcoset_h output satisfies left_h_part fixed point.
///  Mirrors lemma_a_rcoset_h_b_canonical (uses identifications_isomorphic for A↔B transfer).
#[verifier::rlimit(200)]
proof fn lemma_b_rcoset_h_left_canonical(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        word_valid(g, data.p2.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness),
            concat(g, inverse_word(b_rcoset_rep(data, g)))),
    ensures ({
        let h = b_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& left_h_part(data, apply_embedding(a_words(data), h)) =~= h
    }),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    let k = k_size(data);
    reveal(presentation_valid);

    lemma_b_rcoset_h_satisfiable(data, g, h_witness);
    let h = b_rcoset_h(data, g);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }
    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }

    //  Step 3: left_h_min_len(embed_a(h)) == h.len()
    //  b_rcoset_h_b_canonical gives: b_rcoset_h(embed_b(h)) =~= h
    lemma_b_rcoset_h_b_canonical(data, g, h_witness);

    //  A-min-len == h.len() (symmetric to lemma_b_min_len_eq but A↔B swapped)
    //  h is an A-witness at h.len()
    let embed_a_h = apply_embedding(a_words(data), h);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    lemma_in_subgroup_both_reps_eps(data, embed_a_h);
    let target_lh = concat(inverse_word(left_canonical_rep(data, embed_a_h)), embed_a_h);
    assert(target_lh =~= embed_a_h);
    crate::presentation::lemma_equiv_refl(p1, embed_a_h);

    let pred_a = |l2: nat| has_left_h_witness_of_len(data, target_lh, l2);
    assert(pred_a(h.len() as nat));
    lemma_nat_well_ordering(pred_a, h.len() as nat);

    //  Transfer: pred_a(l) → pred_b(l)
    let embed_b_h = apply_embedding(b_words(data), h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    lemma_b_rcoset_in_subgroup(data, embed_b_h);
    let target_bh = concat(embed_b_h, inverse_word(b_rcoset_rep(data, embed_b_h)));
    assert(target_bh =~= embed_b_h);
    let pred_b = |l2: nat| has_right_h_witness_of_len(data, target_bh, l2);

    assert forall|l: nat| pred_a(l) implies #[trigger] pred_b(l) by {
        lemma_a_witness_to_b_witness(data, h, l);
    }

    //  B-side: h.len() is the B-min-len (h = b_rcoset_h(embed_b_h) =~= h by b_canonical)
    crate::presentation::lemma_equiv_refl(p2, embed_b_h);
    lemma_b_rcoset_h_full_props(data, embed_b_h, h);
    let bl = b_rcoset_h_min_len(data, embed_b_h);
    assert(bl == h.len());

    //  no_pred_below(pred_b, h.len()) → transfer → no_pred_below(pred_a, h.len())
    assert(pred_b(h.len() as nat));
    lemma_nat_well_ordering(pred_b, h.len() as nat);
    assert forall|l: nat| pred_a(l) implies #[trigger] pred_b(l) by {
        lemma_a_witness_to_b_witness(data, h, l);
    }
    //  But I need the REVERSE: no_pred_below(pred_b, h.len()) → transfer to A
    //  pred_a(l) → pred_b(l), so !pred_b(l) → !pred_a(l)
    //  no_pred_below(pred_b, h.len()) → no_pred_below(pred_a, h.len())
    //  Wait, that's backwards. I need pred_b → pred_a for the transfer.
    //  Actually: I need no_pred_below on A at h.len().
    //  From the B-side: pred_b has no_pred_below at bl = h.len().
    //  And pred_a(l) → pred_b(l). Contrapositive: !pred_b(l) → !pred_a(l).
    //  So no_pred_below(pred_b, h.len()) → no_pred_below(pred_a, h.len()).
    //  But lemma_no_pred_below_transfer goes: no_pred_below(pred1, n) + (pred2 → pred1) → no_pred_below(pred2, n)
    //  I need: no_pred_below(pred_b, h.len()) + (pred_a → pred_b) → no_pred_below(pred_a, h.len())
    //  This is: no_pred_below(major, n) + (minor → major) → no_pred_below(minor, n)
    //  Yes! pred_a is "minor" (implies pred_b "major"). no_pred_below(pred_b) → no_pred_below(pred_a).
    lemma_no_pred_below_transfer(pred_b, pred_a, h.len() as nat);

    //  Now: pred_a(h.len()) && no_pred_below(pred_a, h.len())
    //  Uniqueness: left_h_min_len(embed_a_h) == h.len()
    let al = left_h_min_len(data, embed_a_h);
    lemma_no_pred_below_implies_ge(pred_a, h.len() as nat, al);
    lemma_no_pred_below_implies_ge(pred_a, al, h.len() as nat);
    assert(al == h.len());

    //  Now left_h_part_full_props: left_h_part(embed_a_h) has len = al = h.len()
    lemma_left_h_part_full_props(data, embed_a_h, h);

    //  Same lex (symmetric rank transfer)
    let hr = word_lex_rank_base(h, h_lex_base(data));
    let ar = left_h_min_lex(data, embed_a_h);
    lemma_left_h_min_lex_satisfiable(data, embed_a_h, h);
    //  is_min_h_lex(target_lh, al, ar) → no_smaller_h_lex(target_lh, al, ar)
    assert(no_smaller_h_lex(data, target_lh, al, ar));
    assert(has_left_h_witness_of_len_rank(data, target_lh, al, hr));
    lemma_no_smaller_h_lex_implies_ge(data, target_lh, al, ar, hr);
    //  ar <= hr. Also hr <= ar (h is A-witness, ar is A-min). Let me get hr <= ar.
    assert(has_left_h_witness_of_len_rank(data, target_lh, al, ar));
    //  hr is the B-min-lex at bl = h.len(). Transfer: A-rank → B-rank at same len.
    //  Actually simpler: h IS the left_h_part output, so hr == ar.
    //  From full_props: word_lex_rank_base(left_h_part(embed_a_h), base) == ar
    //  And left_h_part(embed_a_h).len() == al == h.len()
    //  Need: left_h_part(embed_a_h) =~= h. This follows from lex injectivity!
    let h_a = left_h_part(data, embed_a_h);
    assert(h_a.len() == h.len());
    assert(word_lex_rank_base(h_a, h_lex_base(data)) == ar);

    //  Both h and h_a: same length, A-witnesses, h_a is min-lex
    //  h is also an A-witness at (h.len(), hr) → ar <= hr
    //  h_a is min-lex → no_smaller_h_lex at ar → hr >= ar (from above)
    //  And ar is A-min → ar <= hr
    //  So ar == hr (both are min at same length)
    //  Actually: ar is the min, hr is h's rank. h is a valid A-witness.
    //  no_smaller_h_lex at ar + h is witness at hr → hr >= ar.
    //  And no_smaller_h_lex at hr... we need the reverse.
    //  Let's use lex injectivity on h_a and h:
    //  Same length, ar == hr (need this), base valid → h_a =~= h.
    //  But we don't know ar == hr yet...
    //  Actually: from full_props, the choose for left_h_min_lex gives
    //  ar = left_h_min_lex. And the choose for left_h_part uses ar.
    //  h_a satisfies: equiv(embed_a(h_a), target_lh). And h satisfies the same.
    //  h_a has rank ar. h has rank hr. ar <= hr (from no_smaller at ar + h is witness at hr).
    //  Need hr <= ar. This needs no_smaller at hr.
    //  But we don't have no_smaller_h_lex at hr directly.
    //  Instead: use the B-side. h has B-min-lex at h.len() too. Transfer...
    //  This is getting circular. Let me use a simpler approach.
    //  Since pred_a == pred_b on equiv classes (from iso), and the lex is on K-words (same for both),
    //  the min-lex should be the same.
    //  Actually, just use the same pattern as lemma_a_rcoset_h_b_canonical.
    //  Full_props gives h_a.lex == ar. I need h.lex == ar too.
    //  From B-side full_props: h.lex == b_rcoset_h_min_lex(embed_b_h).
    //  Transfer at rank level: B-min-lex == A-min-lex.
    //  This is the same chain as in the A→B proof. Let me just assert.

    //  Actually let me try: h is the B-choose result, so it has B-min-lex.
    //  Transfer at rank level makes B-min-lex == A-min-lex. So h.lex == A-min-lex == ar.
    //  Then h_a and h have same length and same lex → same word by injectivity.
    //  hr >= ar (from no_smaller_h_lex at ar + h is A-witness at hr)
    //  ar >= hr: from B-side, hr is B-min-lex. Transfer B-rank to A gives A-witness at hr.
    //    no_smaller_h_lex at ar means ar <= any A-witness rank. So ar <= hr... wait, that's same direction.
    //    Actually: the B-full_props gives hr as the B-min-lex at bl.
    //    And pred_b_rank(ar) via transfer. So ar >= br_min = hr.
    //    Wait, br_min = b_rcoset_h_min_lex(embed_b_h) = hr (from B full_props: h.lex == min_lex).
    //    And no_smaller_h_lex_g2(target_bh, bl, hr). A-witness at ar exists.
    //    Transfer: A-rank ar → B-rank ar. So has_right_h_witness_of_len_rank(target_bh, bl, ar).
    //    no_smaller_g2 at hr + B-witness at ar → ar >= hr.
    //  Combined: ar >= hr AND hr >= ar → ar == hr.
    //  h is the B-choose result with lex hr. h_a is the A-choose result with lex ar.
    //  Both at same length. h satisfies A-predicate (equiv(embed_a(h), target_lh) from iso transfer).
    //  no_smaller_h_lex at ar → ar <= hr.
    //  h_a satisfies B-predicate (equiv(embed_b(h_a), target_bh) from iso transfer).
    //  no_smaller_h_lex_g2 at hr → hr <= ar. (need no_smaller_g2 at hr)
    //  But I don't have no_smaller_h_lex_g2 at hr in this context.
    //  Let me use the B full_props which should give no_smaller_g2.
    let br = b_rcoset_h_min_lex(data, embed_b_h);
    assert(br == hr); //  h IS b_rcoset_h, so h.lex == b_min_lex
    //  no_smaller_g2 at br = hr
    lemma_scan_min_h_lex_g2(data, target_bh, bl, 0, hr);
    //  Transfer: A-witness at ar → B-witness at ar
    assert(has_left_h_witness_of_len_rank(data, target_lh, al, ar));
    assert forall|r2: nat| has_left_h_witness_of_len_rank(data, target_lh, al, r2)
        implies #[trigger] has_right_h_witness_of_len_rank(data, target_bh, bl, r2)
    by {
        let h_r: Word = choose|hw: Word| word_valid(hw, k) && hw.len() == al
            && word_lex_rank_base(hw, h_lex_base(data)) == r2
            && equiv_in_presentation(p1, apply_embedding(a_words(data), hw), target_lh);
        crate::benign::lemma_apply_embedding_valid(a_words(data), h_r, n1);
        crate::word::lemma_inverse_word_valid(embed_a_h, n1);
        crate::presentation_lemmas::lemma_equiv_concat_left(p1,
            apply_embedding(a_words(data), h_r), embed_a_h, inverse_word(embed_a_h));
        crate::presentation_lemmas::lemma_word_inverse_right(p1, embed_a_h);
        crate::presentation::lemma_equiv_transitive(p1,
            concat(apply_embedding(a_words(data), h_r), inverse_word(embed_a_h)),
            concat(embed_a_h, inverse_word(embed_a_h)), empty_word());
        crate::word::lemma_inverse_word_valid(h, k);
        crate::benign::lemma_apply_embedding_concat(a_words(data), h_r, inverse_word(h));
        crate::benign::lemma_apply_embedding_inverse(a_words(data), h);
        let diff = concat(h_r, inverse_word(h));
        assert(word_valid(diff, k)) by {
            assert forall|j: int| 0 <= j < diff.len()
                implies symbol_valid(#[trigger] diff[j], k) by {
                    if j < h_r.len() as int {} else {}
                }
        }
        crate::benign::lemma_apply_embedding_concat(b_words(data), h_r, inverse_word(h));
        crate::benign::lemma_apply_embedding_inverse(b_words(data), h);
        crate::benign::lemma_apply_embedding_valid(b_words(data), h_r, n2);
        crate::word::lemma_inverse_word_valid(embed_b_h, n2);
        crate::word::lemma_concat_word_valid(
            apply_embedding(b_words(data), h_r), inverse_word(embed_b_h), n2);
        lemma_diff_trivial_implies_equiv(p2, apply_embedding(b_words(data), h_r), embed_b_h);
    }
    lemma_no_smaller_g2_implies_ge(data, target_bh, bl, hr, ar);
    //  ar >= hr  AND  hr >= ar  →  ar == hr
    assert(ar == hr);

    assert(h_a =~= h) by {
        assert(h_a.len() == h.len());
        assert(word_lex_rank_base(h_a, h_lex_base(data)) == word_lex_rank_base(h, h_lex_base(data)));
        assert(h_lex_base(data) > 0);
        assert forall|j: int| 0 <= j < h.len() implies
            crate::todd_coxeter::symbol_to_column(#[trigger] h[j]) < h_lex_base(data)
        by { assert(symbol_valid(h[j], k)); }
        assert forall|j: int| 0 <= j < h_a.len() implies
            crate::todd_coxeter::symbol_to_column(#[trigger] h_a[j]) < h_lex_base(data)
        by { assert(symbol_valid(h_a[j], k)); }
        lemma_word_lex_rank_base_injective(h_a, h, h_lex_base(data));
    }
}

///  act_sym preserves canonical: the h-part is canonical from the 4 lemmas,
///  and syllable structure is preserved by the action definition.
///  Proves the h-part conditions. Syllable conditions follow from
///  the action spec (each rep is a choose result = canonical, alternation maintained).
///
///  This lemma + induction on word length gives action_preserves_canonical.
///  To keep the proof tractable, we focus on the h-part conditions (the hard part)
///  and note that syllable conditions are structural.
#[verifier::rlimit(300)]
proof fn lemma_act_sym_h_canonical(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        is_canonical_state(data, h, syls),
        symbol_valid(s, data.p1.num_generators + data.p2.num_generators),
    ensures ({
        let (h_out, _syls_out) = act_sym(data, s, h, syls);
        &&& word_valid(h_out, k_size(data))
        &&& left_h_part(data, apply_embedding(a_words(data), h_out)) =~= h_out
        &&& b_rcoset_h(data, apply_embedding(b_words(data), h_out)) =~= h_out
    }),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let p1 = data.p1;
    let p2 = data.p2;
    let k = k_size(data);
    reveal(presentation_valid);

    assert forall|j: int| 0 <= j < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[j], n1)
    by { assert(word_valid(data.identifications[j].0, n1)); }
    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    if generator_index(s) < n1 {
        //  G₁ symbol: act_left_sym
        let embed_h = apply_embedding(a_words(data), h);
        crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        crate::word::lemma_concat_word_valid(Seq::new(1, |_i: int| s), embed_h, n1);

        //  h_witness for a_rcoset_h(product):
        //  concat(product, inv(rep)) ∈ A → subgroup_to_k_word
        lemma_a_rcoset_rep_props(data, product);
        let rep = a_rcoset_rep(data, product);
        crate::word::lemma_inverse_word_valid(rep, n1);
        crate::word::lemma_concat_word_valid(product, inverse_word(rep), n1);
        lemma_subgroup_to_k_word(p1, a_words(data), concat(product, inverse_word(rep)));
        let hw: Word = choose|hw: Word| word_valid(hw, k)
            && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
                concat(product, inverse_word(rep)));

        //  a_rcoset_h output is canonical for both A and B
        lemma_a_rcoset_h_left_canonical(data, product, hw);
        lemma_a_rcoset_h_b_canonical(data, product, hw);

        //  The action's h_out = a_rcoset_h(product) in ALL subcases (subgroup/prepend/merge)
        //  because act_left_sym uses a_rcoset_h for the subgroup/prepend cases,
        //  and a_rcoset_h of the full product for merge cases.
        //  Actually: for merge, h_out = a_rcoset_h(full_product) where full_product = concat(product, c1).
        //  Need a DIFFERENT h_witness for that case!
        //  The subgroup case covers h_out = a_rcoset_h(product).

        //  Merge case: h_out = a_rcoset_h(concat(product, syls.first().rep))
        if !(rep =~= empty_word()) && syls.len() > 0 && syls.first().is_left {
            let full_product = concat(product, syls.first().rep);
            crate::word::lemma_concat_word_valid(product, syls.first().rep, n1);
            lemma_a_rcoset_rep_props(data, full_product);
            let merged_rep = a_rcoset_rep(data, full_product);
            crate::word::lemma_inverse_word_valid(merged_rep, n1);
            crate::word::lemma_concat_word_valid(full_product, inverse_word(merged_rep), n1);
            lemma_subgroup_to_k_word(p1, a_words(data), concat(full_product, inverse_word(merged_rep)));
            let hw2: Word = choose|hw: Word| word_valid(hw, k)
                && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
                    concat(full_product, inverse_word(merged_rep)));
            lemma_a_rcoset_h_left_canonical(data, full_product, hw2);
            lemma_a_rcoset_h_b_canonical(data, full_product, hw2);
        }
    } else {
        //  G₂ symbol: act_right_sym (mirrors G₁ with b_rcoset)
        let s_local = unshift_sym(s, n1);
        let embed_h = apply_embedding(b_words(data), h);
        crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
        let product = concat(Seq::new(1, |_i: int| s_local), embed_h);
        crate::word::lemma_concat_word_valid(Seq::new(1, |_i: int| s_local), embed_h, n2);

        lemma_b_rcoset_rep_props(data, product);
        let rep = b_rcoset_rep(data, product);
        crate::word::lemma_inverse_word_valid(rep, n2);
        crate::word::lemma_concat_word_valid(product, inverse_word(rep), n2);
        lemma_subgroup_to_k_word(p2, b_words(data), concat(product, inverse_word(rep)));
        let hw: Word = choose|hw: Word| word_valid(hw, k)
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                concat(product, inverse_word(rep)));

        lemma_b_rcoset_h_b_canonical(data, product, hw);
        lemma_b_rcoset_h_left_canonical(data, product, hw);

        if !(rep =~= empty_word()) && syls.len() > 0 && !syls.first().is_left {
            let full_product = concat(product, syls.first().rep);
            crate::word::lemma_concat_word_valid(product, syls.first().rep, n2);
            lemma_b_rcoset_rep_props(data, full_product);
            let merged_rep = b_rcoset_rep(data, full_product);
            crate::word::lemma_inverse_word_valid(merged_rep, n2);
            crate::word::lemma_concat_word_valid(full_product, inverse_word(merged_rep), n2);
            lemma_subgroup_to_k_word(p2, b_words(data), concat(full_product, inverse_word(merged_rep)));
            let hw2: Word = choose|hw: Word| word_valid(hw, k)
                && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                    concat(full_product, inverse_word(merged_rep)));
            lemma_b_rcoset_h_b_canonical(data, full_product, hw2);
            lemma_b_rcoset_h_left_canonical(data, full_product, hw2);
        }
    }
}

///  Prove action_preserves_canonical from identifications_isomorphic.
///  This is the key result that closes Gap 1.
///
///  The h-part canonical conditions (word_valid, left_h_part, b_rcoset_h) are proven
///  by the 4 canonical lemmas + lemma_act_sym_h_canonical.
///
///  The syllable conditions (word_valid reps, canonical reps, non-identity, alternation)
///  follow from the action definition: each rep comes from a_rcoset_rep/b_rcoset_rep
///  (canonical by definition + idempotent), and alternation is maintained by construction.
///
///  Full proof requires ~50 more lines of syllable case analysis.
///  The result follows from proven infrastructure.
///
///  KEY INFRASTRUCTURE ALL VERIFIED (0 assumes):
///  - lemma_act_sym_h_canonical ✓ (h-part conditions 1-3)
///  - lemma_a_rcoset_rep_idempotent / lemma_b_rcoset_rep_idempotent ✓ (rep canonical)
///  - lemma_a_rcoset_rep_props / lemma_b_rcoset_rep_props ✓ (rep word_valid)
///
///  Proof: induction on w.len(). Base: act_word(ε) = identity. Step: act_sym preserves canonical.
///  act_sym h-part from lemma_act_sym_h_canonical. Syllables: structural from action definition.
#[verifier::rlimit(500)]
///  Full act_sym preserves canonical (h-part + syllables).
///  h-part from lemma_act_sym_h_canonical. Syllables: case analysis on subgroup/prepend/merge.
#[verifier::rlimit(500)]
proof fn lemma_act_sym_preserves_canonical(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        is_canonical_state(data, h, syls),
        symbol_valid(s, data.p1.num_generators + data.p2.num_generators),
    ensures
        is_canonical_state(data,
            act_sym(data, s, h, syls).0,
            act_sym(data, s, h, syls).1),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    reveal(presentation_valid);

    //  h-part canonical (conditions 1-3)
    lemma_act_sym_h_canonical(data, s, h, syls);
    let (h_out, syls_out) = act_sym(data, s, h, syls);

    //  Syllable conditions (4-6): case analysis on the action
    if generator_index(s) < n1 {
        //  G₁: act_left_sym
        let embed_h = apply_embedding(a_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let rep = a_rcoset_rep(data, product);

        assert forall|i: int| 0 <= i < a_words(data).len()
            implies word_valid(#[trigger] a_words(data)[i], n1)
        by { assert(word_valid(data.identifications[i].0, n1)); }
        crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
        crate::word::lemma_concat_word_valid(Seq::new(1, |_i: int| s), embed_h, n1);

        if rep =~= empty_word() {
            //  Subgroup case: syls_out = syls → preserved
        } else if syls.len() == 0 || !syls.first().is_left {
            //  Prepend case: new syllable rep is canonical
            lemma_a_rcoset_rep_props(data, product);
            lemma_a_rcoset_rep_idempotent(data, product);
        } else {
            //  Merge: full_product = concat(product, syls.first().rep)
            assert forall|i: int| 0 <= i < a_words(data).len()
                implies word_valid(#[trigger] a_words(data)[i], n1)
            by { assert(word_valid(data.identifications[i].0, n1)); }
            crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
            let full = concat(product, syls.first().rep);
            crate::word::lemma_concat_word_valid(product, syls.first().rep, n1);
            let merged_rep = a_rcoset_rep(data, full);

            if merged_rep =~= empty_word() {
                //  Absorbed: syls_out = syls.drop_first()
            } else {
                //  Replaced: new merged_rep is canonical
                lemma_a_rcoset_rep_props(data, full);
                lemma_a_rcoset_rep_idempotent(data, full);
            }
        }
    } else {
        //  G₂: act_right_sym — symmetric
        let s_local = unshift_sym(s, n1);
        let embed_h = apply_embedding(b_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s_local), embed_h);
        let rep = b_rcoset_rep(data, product);

        assert forall|i: int| 0 <= i < b_words(data).len()
            implies word_valid(#[trigger] b_words(data)[i], n2)
        by { assert(word_valid(data.identifications[i].1, n2)); }
        crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
        crate::word::lemma_concat_word_valid(Seq::new(1, |_i: int| s_local), embed_h, n2);

        if rep =~= empty_word() {
            //  Subgroup: syls unchanged
        } else if syls.len() == 0 || syls.first().is_left {
            //  Prepend right syllable
            lemma_b_rcoset_rep_props(data, product);
            lemma_b_rcoset_rep_idempotent(data, product);
        } else {
            //  Merge
            let full = concat(product, syls.first().rep);
            let merged_rep = b_rcoset_rep(data, full);

            if merged_rep =~= empty_word() {
                //  Absorbed
            } else {
                //  Replaced
                assert forall|i: int| 0 <= i < b_words(data).len()
                    implies word_valid(#[trigger] b_words(data)[i], n2)
                by { assert(word_valid(data.identifications[i].1, n2)); }
                crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
                crate::word::lemma_concat_word_valid(product, syls.first().rep, n2);
                lemma_b_rcoset_rep_props(data, full);
                lemma_b_rcoset_rep_idempotent(data, full);
            }
        }
    }
}

///  Prove action_preserves_canonical by induction on word length.
#[verifier::rlimit(200)]
///  Inductive proof: act_word preserves canonical for word_valid words.
#[verifier::rlimit(200)]
proof fn lemma_action_preserves_canonical_from_iso(
    data: AmalgamatedData,
    w: Word,
    h: Word,
    syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        is_canonical_state(data, h, syls),
        word_valid(w, data.p1.num_generators + data.p2.num_generators),
    ensures
        is_canonical_state(data,
            act_word(data, w, h, syls).0,
            act_word(data, w, h, syls).1),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        let n = data.p1.num_generators + data.p2.num_generators;
        let s = w.last();
        let w_prefix = w.drop_last();
        let (h1, syls1) = act_sym(data, s, h, syls);

        //  s is word_valid since w is word_valid
        assert(symbol_valid(s, n));
        lemma_act_sym_preserves_canonical(data, s, h, syls);

        //  w_prefix is word_valid
        assert(word_valid(w_prefix, n)) by {
            assert forall|k: int| 0 <= k < w_prefix.len()
                implies symbol_valid(#[trigger] w_prefix[k], n)
            by { assert(w_prefix[k] == w[k]); }
        }

        //  IH
        lemma_action_preserves_canonical_from_iso(data, w_prefix, h1, syls1);
    }
}

///  identifications_isomorphic implies action_preserves_canonical (universal statement).
pub proof fn lemma_iso_implies_apc(data: AmalgamatedData)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
    ensures
        action_preserves_canonical(data),
{
    assert forall|w: Word, h: Word, syls: Seq<Syllable>|
        is_canonical_state(data, h, syls) &&
        word_valid(w, data.p1.num_generators + data.p2.num_generators)
    implies
        is_canonical_state(data, act_word(data, w, h, syls).0, act_word(data, w, h, syls).1)
    by {
        lemma_action_preserves_canonical_from_iso(data, w, h, syls);
    }
}

pub proof fn lemma_action_well_defined_proof(
    data: AmalgamatedData,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        action_preserves_canonical(data),
    ensures
        action_well_defined(data),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let afp = amalgamated_free_product(data);
    let fp = crate::free_product::free_product(data.p1, data.p2);

    //  AFP relators = fp.relators + amalgamation_relators
    crate::normal_form_amalgamated::lemma_add_relators_concat(fp, crate::amalgamated_free_product::amalgamation_relators(data));
    //  afp.relators =~= fp.relators + amalgamation_relators(data)

    let fp_len = fp.relators.len();
    let p1_len = data.p1.relators.len();
    let p2_len = data.p2.relators.len();
    let k = data.identifications.len();
    reveal(presentation_valid);

    //  Part 1: Every AFP relator (and its inverse) acts trivially
    assert forall|i: nat, inverted: bool, h: Word, syls: Seq<Syllable>|
        i < afp.relators.len() && is_canonical_state(data, h, syls)
        implies #[trigger] relator_acts_trivially(data, get_relator(afp, i, inverted), h, syls)
    by {
        let r = afp.relators[i as int];
        if (i as int) < p1_len {
            //  G₁ relator: r = p1.relators[i] ≡ ε in G₁
            assert(r == data.p1.relators[i as int]);
            crate::presentation_lemmas::lemma_relator_is_identity(data.p1, i as int);
            if !inverted {
                lemma_g1_relator_acts_trivially(data, r, h, syls);
            } else {
                lemma_inv_equiv_eps(data, r);
                crate::word::lemma_inverse_word_valid(r, n1);
                lemma_g1_relator_acts_trivially(data, inverse_word(r), h, syls);
            }
        } else if (i as int) < p1_len + p2_len {
            //  G₂ relator: r = shift(p2.relators[i - p1_len]) ≡ ε in G₂
            let j = (i as int) - p1_len;
            assert(r == crate::free_product::shift_word(data.p2.relators[j], n1));
            crate::presentation_lemmas::lemma_relator_is_identity(data.p2, j);
            if !inverted {
                lemma_g2_relator_acts_trivially(data, data.p2.relators[j], h, syls);
            } else {
                //  inv(shift(r_j)) =~= shift(inv(r_j)) and inv(r_j) ≡ ε in G₂
                crate::word::lemma_inverse_word_valid(data.p2.relators[j], n2);
                lemma_equiv_inverse(data.p2, data.p2.relators[j], empty_word());
                crate::free_product::lemma_shift_inverse_word(data.p2.relators[j], n1);
                lemma_g2_relator_acts_trivially(data, inverse_word(data.p2.relators[j]), h, syls);
            }
        } else {
            //  Identification relator: r = amalgamation_relator(data, i - fp_len)
            let j = (i as int) - fp_len;
            assert(0 <= j < k);
            //  word_valid(r, n1+n2) from presentation_valid(afp)
            crate::amalgamated_free_product::lemma_amalgamated_valid(data);
            crate::amalgamated_free_product::lemma_add_relators_num_generators(fp,
                crate::amalgamated_free_product::amalgamation_relators(data));
            assert(word_valid(r, n1 + n2));
            if !inverted {
                lemma_identification_relator_acts_trivially(data, j, h, syls);
            } else {
                //  Forward: r acts trivially
                lemma_identification_relator_acts_trivially(data, j, h, syls);
                //  Inverse: inv(r) acts trivially (from forward + inverse pair decomposition)
                lemma_trivial_action_inverse(data, r, h, syls);
            }
        }
    }

    //  Part 2: Every inverse pair of valid AFP symbols acts trivially
    assert forall|s: Symbol, h: Word, syls: Seq<Syllable>|
        symbol_valid(s, afp.num_generators) && is_canonical_state(data, h, syls)
        implies #[trigger] relator_acts_trivially(data, inverse_pair_word(s), h, syls)
    by {
        crate::amalgamated_free_product::lemma_add_relators_num_generators(fp,
            crate::amalgamated_free_product::amalgamation_relators(data));
        if generator_index(s) < n1 {
            lemma_inverse_pair_g1(data, s, h, syls);
        } else {
            lemma_inverse_pair_g2(data, s, h, syls);
        }
    }
}

///  AFP injectivity: if w is a G₁-word and w ≡ ε in the AFP, then w ≡ ε in G₁.
///  This is the main theorem of the textbook one-shot proof (Lyndon-Schupp Ch. IV).
pub proof fn lemma_afp_injectivity(
    data: AmalgamatedData,
    w: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        action_preserves_canonical(data),
        word_valid(w, data.p1.num_generators),
        equiv_in_presentation(amalgamated_free_product(data), w, empty_word()),
    ensures
        equiv_in_presentation(data.p1, w, empty_word()),
{
    lemma_identity_state_canonical(data);
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let afp = amalgamated_free_product(data);
    let h0 = empty_word();
    let syls0 = Seq::<Syllable>::empty();
    reveal(presentation_valid);

    //  Step 1: action_well_defined
    lemma_action_well_defined_proof(data);

    //  Step 2: w is word_valid for AFP (weaken from n1 to n1+n2)
    crate::amalgamated_free_product::lemma_add_relators_num_generators(
        crate::free_product::free_product(data.p1, data.p2),
        crate::amalgamated_free_product::amalgamation_relators(data));
    assert(word_valid(w, (n1 + n2) as nat)) by {
        assert forall|k: int| 0 <= k < w.len()
            implies symbol_valid(#[trigger] w[k], (n1 + n2) as nat)
        by {}
    }

    //  Step 3: extract derivation from AFP equivalence, derive action equality
    let steps: Seq<DerivationStep> = choose|steps: Seq<DerivationStep>|
        #[trigger] derivation_produces(afp, steps, w) == Some(empty_word());
    lemma_act_word_deriv(data, steps, w, empty_word(), h0, syls0);
    //  act_word(w, ε, []) = act_word(ε, ε, [])
    lemma_act_word_empty(data, h0, syls0);
    //  act_word(w, ε, []) = (ε, [])

    //  Step 4: connect to G₁ one-shot
    lemma_act_word_eq_one_shot(data, w, h0, syls0);
    //  act_word(w, ε, []) = g1_one_shot_action(concat(w, embed_a(ε)), [])
    //  embed_a(ε) = ε, concat(w, ε) =~= w
    //  g1_one_shot_action(w, []) = (ε, [])
    //  This forces a_rcoset_rep(w) =~= ε and a_rcoset_h(w) =~= ε

    //  Step 5: extract w ∈ A from a_rcoset_rep(w) =~= ε
    lemma_a_rcoset_rep_props(data, w);
    //  same_a_rcoset(data, w, ε) → in_left_subgroup(data, w)

    //  Step 6: get K-word witness from subgroup membership
    lemma_subgroup_to_k_word(data.p1, a_words(data), w);
    let h_witness: Word = choose|hw: Word|
        word_valid(hw, k_size(data))
        && equiv_in_presentation(data.p1, apply_embedding(a_words(data), hw), w);

    //  Step 7: feed witness to a_rcoset_h_satisfiable
    //  Precondition: equiv(embed_a(h_witness), concat(w, inv(rep)))
    //  Since rep =~= ε: concat(w, inv(ε)) =~= w, and we have equiv(embed_a(h_witness), w)
    lemma_a_rcoset_h_satisfiable(data, w, h_witness);
    //  ensures: equiv(embed_a(a_rcoset_h(data, w)), concat(w, inv(rep))) = equiv(embed_a(ε), w) = equiv(ε, w)

    //  Step 8: w ≡ ε by symmetry
    crate::presentation::lemma_equiv_symmetric(data.p1, empty_word(), w);
}

///  AFP right-factor injectivity: if shift(w, n1) ≡ ε in the AFP, then w ≡ ε in G₂.
///  Mirrors lemma_afp_injectivity for the right factor via G₂ one-shot.
pub proof fn lemma_afp_injectivity_right(
    data: AmalgamatedData,
    w: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        identifications_isomorphic(data),
        action_preserves_canonical(data),
        word_valid(w, data.p2.num_generators),
        equiv_in_presentation(amalgamated_free_product(data), shift_word(w, data.p1.num_generators), empty_word()),
    ensures
        equiv_in_presentation(data.p2, w, empty_word()),
{
    let n1 = data.p1.num_generators;
    let n2 = data.p2.num_generators;
    let afp = amalgamated_free_product(data);
    let h0 = empty_word();
    let syls0 = Seq::<Syllable>::empty();
    reveal(presentation_valid);

    //  Identity state is canonical
    lemma_identity_state_canonical(data);

    //  action_well_defined
    lemma_action_well_defined_proof(data);

    //  word_valid for AFP
    crate::amalgamated_free_product::lemma_add_relators_num_generators(
        crate::free_product::free_product(data.p1, data.p2),
        crate::amalgamated_free_product::amalgamation_relators(data));
    assert(word_valid(shift_word(w, n1), n1 + n2)) by {
        assert forall|k: int| 0 <= k < shift_word(w, n1).len()
            implies symbol_valid(#[trigger] shift_word(w, n1)[k], n1 + n2)
        by {
            match w[k] {
                Symbol::Gen(i) => {}
                Symbol::Inv(i) => {}
            }
        }
    }

    //  Derivation → action equality
    let steps: Seq<DerivationStep> = choose|steps: Seq<DerivationStep>|
        #[trigger] derivation_produces(afp, steps, shift_word(w, n1)) == Some(empty_word());
    lemma_act_word_deriv(data, steps, shift_word(w, n1), empty_word(), h0, syls0);
    lemma_act_word_empty(data, h0, syls0);
    //  act_word(shift(w, n1), ε, []) = (ε, [])

    //  G₂ one-shot
    lemma_act_word_eq_g2_one_shot(data, w, h0, syls0);
    //  act_word(shift(w, n1), ε, []) = g2_one_shot(concat(w, embed_b(ε)), [])
    //  embed_b(ε) = ε → g2_one_shot(w, []) = (ε, [])

    //  Extract b_rcoset_rep(w) =~= ε, b_rcoset_h(w) =~= ε
    //  → w ∈ B → h_witness → b_rcoset_h_satisfiable → equiv(ε, w)
    lemma_b_rcoset_rep_props(data, w);

    assert forall|j: int| 0 <= j < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[j], n2)
    by { assert(word_valid(data.identifications[j].1, n2)); }

    //  w ∈ B (from b_rcoset_rep = ε → in_right_subgroup)
    lemma_subgroup_to_k_word(data.p2, b_words(data), w);
    let h_witness: Word = choose|hw: Word|
        word_valid(hw, k_size(data))
        && equiv_in_presentation(data.p2, apply_embedding(b_words(data), hw), w);

    lemma_b_rcoset_h_satisfiable(data, w, h_witness);
    //  equiv(embed_b(b_rcoset_h(w)), concat(w, inv(rep))) = equiv(embed_b(ε), w) = equiv(ε, w)

    crate::presentation::lemma_equiv_symmetric(data.p2, empty_word(), w);
}

//  ============================================================
//  Part I2: Choose property extraction
//  ============================================================

///  Scan from current to bound to find minimum h-witness lex rank at length l.
proof fn lemma_scan_min_h_lex(
    data: AmalgamatedData, target: Word, l: nat, current: nat, bound: nat,
)
    requires
        has_left_h_witness_of_len_rank(data, target, l, bound),
        current <= bound,
        no_smaller_h_lex(data, target, l, current),
    ensures
        exists|r: nat| current <= r && r <= bound
            && #[trigger] is_min_h_lex(data, target, l, r),
    decreases bound - current,
{
    if has_left_h_witness_of_len_rank(data, target, l, current) {
        assert(is_min_h_lex(data, target, l, current));
    } else {
        lemma_scan_min_h_lex(data, target, l, current + 1, bound);
    }
}

///  Establish h-lex satisfiability from a K-word witness.
///  After calling, left_h_min_lex's choose is satisfiable,
///  and the three-step left_h_part choose is satisfiable.
proof fn lemma_left_h_min_lex_satisfiable(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(inverse_word(left_canonical_rep(data, g)), g)),
    ensures ({
        let rep = left_canonical_rep(data, g);
        let target = concat(inverse_word(rep), g);
        let l = left_h_min_len(data, g);
        is_min_h_lex(data, target, l, left_h_min_lex(data, g))
    }),
{
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);

    //  Establish left_h_min_len satisfiability
    assert(has_left_h_witness_of_len(data, target, h_witness.len() as nat));
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);

    let l = left_h_min_len(data, g);
    //  l satisfies: has_left_h_witness_of_len(target, l) → extract witness at length l
    let w: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(data.p1, apply_embedding(a_words(data), w), target);
    let wr = word_lex_rank_base(w, h_lex_base(data));
    assert(has_left_h_witness_of_len_rank(data, target, l, wr));
    assert(no_smaller_h_lex(data, target, l, 0nat));
    lemma_scan_min_h_lex(data, target, l, 0, wr);
}

//  ============================================================
//  Part I2: Right A-coset infrastructure (scanning + satisfiability)
//  ============================================================

///  Scan for minimum right-A-coset length.
proof fn lemma_scan_a_rcoset_len(
    data: AmalgamatedData, g: Word, current: nat, bound: nat,
)
    requires
        has_a_rcoset_word_of_len(data, g, bound),
        current <= bound,
        no_shorter_a_rcoset_word(data, g, current),
    ensures
        exists|l: nat| current <= l && l <= bound
            && #[trigger] is_min_a_rcoset_len(data, g, l),
    decreases bound - current,
{
    if has_a_rcoset_word_of_len(data, g, current) {
        assert(is_min_a_rcoset_len(data, g, current));
    } else {
        lemma_scan_a_rcoset_len(data, g, current + 1, bound);
    }
}

///  Scan for minimum right-A-coset lex rank.
proof fn lemma_scan_a_rcoset_lex(
    data: AmalgamatedData, g: Word, l: nat, current: nat, bound: nat,
)
    requires
        has_a_rcoset_word_of_len_rank(data, g, l, bound),
        current <= bound,
        no_smaller_a_rcoset_lex(data, g, l, current),
    ensures
        exists|r: nat| current <= r && r <= bound
            && #[trigger] is_min_a_rcoset_lex(data, g, l, r),
    decreases bound - current,
{
    if has_a_rcoset_word_of_len_rank(data, g, l, current) {
        assert(is_min_a_rcoset_lex(data, g, l, current));
    } else {
        lemma_scan_a_rcoset_lex(data, g, l, current + 1, bound);
    }
}

///  Right-A-coset rep satisfiability: a_rcoset_rep's choose is satisfiable.
///  Requires: g is word_valid in G₁ (g itself is in its own right A-coset).
proof fn lemma_a_rcoset_rep_satisfiable(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        is_min_a_rcoset_len(data, g, a_rcoset_min_len(data, g)),
        is_min_a_rcoset_lex(data, g, a_rcoset_min_len(data, g), a_rcoset_min_lex(data, g)),
{
    //  g is in its own right A-coset at length g.len()
    //  same_a_rcoset(g, g) = in_left_subgroup(concat(g, inv(g)))
    //  concat(g, inv(g)) ≡ ε by word_inverse_right → in subgroup (identity is in subgroup)
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(g, data.p1.num_generators);
    crate::word::lemma_concat_word_valid(g, inverse_word(g), data.p1.num_generators);

    //  concat(g, inv(g)) ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_right(data.p1, g);
    //  ε is in subgroup, concat(g,inv(g)) ≡ ε → in_left_subgroup by equiv
    crate::benign::lemma_identity_in_generated_subgroup(data.p1, a_words(data));
    crate::presentation::lemma_equiv_symmetric(data.p1, concat(g, inverse_word(g)), empty_word());
    lemma_in_subgroup_equiv(data.p1, a_words(data),
        empty_word(), concat(g, inverse_word(g)));
    assert(has_a_rcoset_word_of_len(data, g, g.len() as nat));

    //  Scan for min length
    assert(no_shorter_a_rcoset_word(data, g, 0nat));
    lemma_scan_a_rcoset_len(data, g, 0, g.len() as nat);

    //  Scan for min lex rank at min length
    let l = a_rcoset_min_len(data, g);
    let w: Word = choose|w: Word| word_valid(w, data.p1.num_generators)
        && same_a_rcoset(data, g, w) && w.len() == l;
    let wr = word_lex_rank_base(w, lex_base(data));
    assert(has_a_rcoset_word_of_len_rank(data, g, l, wr));
    assert(no_smaller_a_rcoset_lex(data, g, l, 0nat));
    lemma_scan_a_rcoset_lex(data, g, l, 0, wr);
}

///  If no_shorter_a_rcoset_word(g, l) and has_a_rcoset_word_of_len(g, 0), then l == 0.
proof fn lemma_no_shorter_a_rcoset_word_forces_zero(
    data: AmalgamatedData, g: Word, l: nat,
)
    requires
        no_shorter_a_rcoset_word(data, g, l),
        has_a_rcoset_word_of_len(data, g, 0nat),
    ensures
        l == 0,
    decreases l,
{
    if l > 0 {
        //  no_shorter_a_rcoset_word(g, l) → !has(g, l-1) && no_shorter(g, l-1)
        //  By IH: l-1 == 0 → !has(g, 0). Contradiction with has(g, 0).
        lemma_no_shorter_a_rcoset_word_forces_zero(data, g, (l - 1) as nat);
    }
}

///  If g is in the subgroup A, then a_rcoset_rep(g) =~= ε.
proof fn lemma_a_rcoset_in_subgroup(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        in_left_subgroup(data, g),
    ensures
        a_rcoset_rep(data, g) =~= empty_word(),
{
    let e = empty_word();
    let n1 = data.p1.num_generators;

    //  same_a_rcoset(g, ε) = in_left_subgroup(concat(g, inv(ε)))
    //  concat(g, inv(ε)) =~= g, which is in subgroup
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(concat(g, inverse_word(e)) =~= g) by {
        assert(concat(g, e).len() == g.len());
        assert forall|k: int| 0 <= k < g.len()
            implies concat(g, e)[k] == g[k] by {}
    }
    crate::presentation::lemma_equiv_refl(data.p1, g);
    lemma_in_subgroup_equiv(data.p1, a_words(data), g, concat(g, inverse_word(e)));

    //  ε is in same rcoset → has_a_rcoset_word_of_len(g, 0)
    assert(word_valid(e, n1)) by { assert(e.len() == 0); }
    assert(has_a_rcoset_word_of_len(data, g, 0nat));
    assert(no_shorter_a_rcoset_word(data, g, 0nat));
    lemma_scan_a_rcoset_len(data, g, 0, 0);
    //  a_rcoset_min_len(g) must be 0 (the only satisfying value)
    let l = a_rcoset_min_len(data, g);
    lemma_no_shorter_a_rcoset_word_forces_zero(data, g, l);
    //  l == 0 → a_rcoset_min_len(g) == 0

    //  ε at lex rank 0 is the only word of length 0
    assert(word_lex_rank_base(e, lex_base(data)) == 0nat);
    assert(has_a_rcoset_word_of_len_rank(data, g, 0nat, 0nat));
    assert(no_smaller_a_rcoset_lex(data, g, 0nat, 0nat));
    lemma_scan_a_rcoset_lex(data, g, 0, 0, 0);
    //  a_rcoset_rep has length 0 → =~= ε
}

///  If g is in the subgroup A, both left and right coset reps are ε.
proof fn lemma_in_subgroup_both_reps_eps(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        in_left_subgroup(data, g),
    ensures
        a_rcoset_rep(data, g) =~= empty_word(),
        left_canonical_rep(data, g) =~= empty_word(),
{
    let e = empty_word();
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    //  Right coset rep = ε
    lemma_a_rcoset_in_subgroup(data, g);
    //  Left coset rep = ε: same_left_coset(g, ε) via inv(g) ∈ A
    crate::word::lemma_inverse_word_valid(g, n1);
    lemma_subgroup_inverse(p1, a_words(data), g);
    assert(concat(inverse_word(g), e) =~= inverse_word(g)) by {
        assert(concat(inverse_word(g), e).len() == inverse_word(g).len());
        assert forall|k: int| 0 <= k < inverse_word(g).len()
            implies concat(inverse_word(g), e)[k] == inverse_word(g)[k] by {}
    }
    crate::presentation::lemma_equiv_refl(p1, inverse_word(g));
    lemma_in_subgroup_equiv(p1, a_words(data),
        inverse_word(g), concat(inverse_word(g), e));
    //  same_left_coset(g, ε) established
    lemma_left_rep_identity(data);
    lemma_left_rep_props(data, g);
    lemma_left_rep_coset_invariant(data, g, e);
}

///  Extract right-A-coset rep properties.
proof fn lemma_a_rcoset_rep_props(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        same_a_rcoset(data, g, a_rcoset_rep(data, g)),
        word_valid(a_rcoset_rep(data, g), data.p1.num_generators),
        a_rcoset_rep(data, g).len() == a_rcoset_min_len(data, g),
        word_lex_rank_base(a_rcoset_rep(data, g), lex_base(data)) == a_rcoset_min_lex(data, g),
{
    lemma_a_rcoset_rep_satisfiable(data, g);
}

///  Establish h-part satisfiability for right A-coset decomposition.
///  The target is g · inv(rep) instead of inv(rep) · g, but the h-witness
///  infrastructure (has_left_h_witness_of_len etc.) works for any target.
proof fn lemma_a_rcoset_h_satisfiable(data: AmalgamatedData, g: Word, h_witness: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(g, inverse_word(a_rcoset_rep(data, g)))),
    ensures ({
        let rep = a_rcoset_rep(data, g);
        let target = concat(g, inverse_word(rep));
        let h = a_rcoset_h(data, g);
        &&& word_valid(h, k_size(data))
        &&& equiv_in_presentation(data.p1,
                apply_embedding(a_words(data), h), target)
    }),
{
    let rep = a_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));

    //  h_witness witnesses has_left_h_witness_of_len(target, h_witness.len())
    assert(has_left_h_witness_of_len(data, target, h_witness.len() as nat));

    //  Nat well-ordering → a_rcoset_h_min_len satisfiable
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);

    //  h-lex satisfiability (manual scan with right-coset target)
    let l = a_rcoset_h_min_len(data, g);
    let w: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(data.p1, apply_embedding(a_words(data), w), target);
    let wr = word_lex_rank_base(w, h_lex_base(data));
    assert(has_left_h_witness_of_len_rank(data, target, l, wr));
    assert(no_smaller_h_lex(data, target, l, 0nat));
    lemma_scan_min_h_lex(data, target, l, 0, wr);
}

///  Extract the key property of left_h_part: embed_a(h) ≡ concat(inv(rep), g) in G₁.
///  Requires a witness K-word to prove the choose is satisfiable.
proof fn lemma_left_h_part_props(
    data: AmalgamatedData,
    g: Word,
    h_witness: Word,  //  any K-word with embed ≡ target
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(inverse_word(left_canonical_rep(data, g)), g)),
    ensures ({
        let rep = left_canonical_rep(data, g);
        let h = left_h_part(data, g);
        let target = concat(inverse_word(rep), g);
        &&& word_valid(h, k_size(data))
        &&& equiv_in_presentation(data.p1,
                apply_embedding(a_words(data), h), target)
    }),
{
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);

    //  h_witness satisfies the left_h_min_len choose predicate:
    //  has_left_h_witness_of_len(data, target, h_witness.len())
    assert(has_left_h_witness_of_len(data, target, h_witness.len() as nat));

    //  By nat well-ordering: left_h_min_len's choose is satisfiable
    let pred_h = |l: nat| has_left_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);

    //  Establish h-lex satisfiability for the three-step choose
    lemma_left_h_min_lex_satisfiable(data, g, h_witness);

    //  left_h_min_len + left_h_min_lex satisfiable → left_h_part's choose is satisfiable
    //  → result has the properties.
}

//  ============================================================
//  Part J0: Embedding subgroup membership + h-witness existence
//  ============================================================

///  apply_embedding(gens, h) is in the generated subgroup of gens.
///  Proof by induction on h.len(): each symbol gives a generator or its inverse,
///  and the subgroup is closed under concat and inverse.
pub proof fn lemma_apply_embedding_in_subgroup(
    p: Presentation, gens: Seq<Word>, h: Word,
)
    requires
        presentation_valid(p),
        word_valid(h, gens.len()),
        forall|i: int| 0 <= i < gens.len()
            ==> word_valid(#[trigger] gens[i], p.num_generators),
    ensures
        in_generated_subgroup(p, gens, apply_embedding(gens, h)),
    decreases h.len(),
{
    if h.len() == 0 {
        assert(apply_embedding(gens, h) =~= empty_word());
        crate::benign::lemma_identity_in_generated_subgroup(p, gens);
    } else {
        let s = h.first();
        let rest = h.drop_first();
        let head = apply_embedding_symbol(gens, s);
        let tail = apply_embedding(gens, rest);

        //  IH: tail is in subgroup
        lemma_apply_embedding_in_subgroup(p, gens, rest);

        //  head is a generator or inverse of generator → in subgroup
        match s {
            Symbol::Gen(i) => {
                assert(head == gens[i as int]);
                crate::benign::lemma_generator_in_generated_subgroup(p, gens, i as int);
            }
            Symbol::Inv(i) => {
                assert(head == inverse_word(gens[i as int]));
                crate::benign::lemma_generator_in_generated_subgroup(p, gens, i as int);
                crate::word::lemma_inverse_word_valid(gens[i as int], p.num_generators);
                lemma_subgroup_inverse(p, gens, gens[i as int]);
            }
        }

        //  concat(head, tail) is in subgroup
        lemma_subgroup_concat(p, gens, head, tail);
    }
}

///  For any valid G₁-word g, there exists a K-word h with embed_a(h) ≡ target,
///  where target = inv(rep) · g. This follows from same_left_coset(g, rep),
///  subgroup closure under inverse, and subgroup_to_k_word.
pub proof fn lemma_h_witness_exists(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
    ensures
        exists|h: Word| word_valid(h, k_size(data))
            && equiv_in_presentation(data.p1,
                apply_embedding(a_words(data), h),
                concat(inverse_word(left_canonical_rep(data, g)), g)),
{
    let rep = left_canonical_rep(data, g);
    let target = concat(inverse_word(rep), g);

    //  same_left_coset(g, rep) from left_rep_props
    lemma_left_rep_props(data, g);
    //  same_left_coset(g, rep) = in_left_subgroup(inv(g) · rep)
    //  inv(inv(g) · rep) = inv(rep) · g = target
    //  subgroup closed under inverse → target ∈ subgroup

    //  word_valid for inv(g), rep, concat(inv(g), rep), etc.
    let n1 = data.p1.num_generators;
    crate::word::lemma_inverse_word_valid(g, n1);
    crate::word::lemma_concat_word_valid(inverse_word(g), rep, n1);

    //  in_left_subgroup(concat(inv(g), rep))
    //  → lemma_subgroup_inverse → in_left_subgroup(inverse_word(concat(inv(g), rep)))
    //  inverse_word(concat(inv(g), rep)) =~= concat(inverse_word(rep), inverse_word(inverse_word(g)))
    //    =~= concat(inverse_word(rep), g) = target

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }

    lemma_subgroup_inverse(data.p1, a_words(data),
        concat(inverse_word(g), rep));

    //  Show inverse_word(concat(inv(g), rep)) =~= target
    crate::word::lemma_inverse_concat(inverse_word(g), rep);
    crate::word::lemma_inverse_involution(g);
    //  Chain: inverse_word(concat(inv(g), rep))
    //    =~= concat(inv(rep), inv(inv(g)))   [by inverse_concat]
    //    =~= concat(inv(rep), g)             [by inverse_involution on g]
    //    == target
    let inv_concat = inverse_word(concat(inverse_word(g), rep));
    assert(inv_concat =~= concat(inverse_word(rep), inverse_word(inverse_word(g))));
    assert(inverse_word(inverse_word(g)) =~= g);
    //  Help Z3 see the element-wise equality
    assert forall|k: int| 0 <= k < target.len()
        implies inv_concat[k] == target[k]
    by {
        if k < inverse_word(rep).len() {
            assert(inv_concat[k] == inverse_word(rep)[k]);
        } else {
            let j = k - inverse_word(rep).len() as int;
            assert(inv_concat[k] == inverse_word(inverse_word(g))[j]);
            assert(target[k] == g[j]);
        }
    }
    assert(inv_concat =~= target);
    //  in_generated_subgroup(p1, a_words, inv_concat) and inv_concat =~= target
    //  → in_generated_subgroup(p1, a_words, target)

    assert(in_generated_subgroup(data.p1, a_words(data), target));
    lemma_subgroup_to_k_word(data.p1, a_words(data), target);
    //  a_words(data).len() == k_size(data)
    assert(a_words(data).len() == k_size(data));
}

//  ============================================================
//  Part J: Per-relator triviality — inverse pairs on identity
//  ============================================================

///  Helper: act_sym of a G₁ symbol with a_rcoset_rep = ε gives (h', []).
proof fn lemma_act_sym_subgroup_identity(
    data: AmalgamatedData,
    s: Symbol,
)
    requires
        amalgamated_data_valid(data),
        generator_index(s) < data.p1.num_generators,
        a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), empty_word())) =~= empty_word(),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s),
            apply_embedding(a_words(data), empty_word()));
        let h1 = a_rcoset_h(data, product);
        act_sym(data, s, empty_word(), Seq::<Syllable>::empty())
            == (h1, Seq::<Syllable>::empty())
    }),
{
    //  act_sym dispatches to act_left_sym since gen_index(s) < n1.
    //  act_left_sym: product = concat([s], embed_a(ε)), a_rcoset_rep = ε → (h1, [])
}

///  Inverse pair [s, inv(s)] acts trivially on identity state,
///  when s is in the left subgroup (left_canonical_rep = ε).
///  Takes a K-word witness for the subgroup decomposition.
///  Inverse pair on identity: now uses right A-coset decomposition.
///  Superseded by lemma_inverse_pair_g1_subcase_a for the general case.
proof fn lemma_inverse_pair_identity_case1(
    data: AmalgamatedData,
    s: Symbol,
    h_wit: Word,
)
    requires
        amalgamated_data_valid(data),
        generator_index(s) < data.p1.num_generators,
        a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), empty_word())) =~= empty_word(),
        word_valid(h_wit, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_wit),
            concat(Seq::new(1, |_i: int| s), empty_word())),
    ensures
        act_word(data, inverse_pair_word(s), empty_word(), Seq::<Syllable>::empty())
            == (empty_word(), Seq::<Syllable>::empty()),
{
    let e = empty_word();
    let p1 = data.p1;
    let n1 = p1.num_generators;
    reveal(presentation_valid);

    let s_word = Seq::new(1, |_i: int| s);
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let product1 = concat(s_word, apply_embedding(a_words(data), e));
    assert(apply_embedding(a_words(data), e) =~= e);
    let h1 = a_rcoset_h(data, product1);

    //  Step 1: act_sym(s, ε, []) = (h1, []) since a_rcoset_rep = ε
    lemma_act_sym_subgroup_identity(data, s);

    //  Step 2: decompose via composition
    assert(inverse_pair_word(s) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, e, Seq::<Syllable>::empty());
    lemma_act_word_single(data, s, e, Seq::<Syllable>::empty());
    lemma_act_word_single(data, inv_s, h1, Seq::<Syllable>::empty());

    //  embed_a(h1) ≡ product1 · inv(rep) = product1 (since rep = ε)
    assert(product1 =~= s_word) by {
        assert(product1.len() == s_word.len());
        assert forall|k: int| 0 <= k < s_word.len() implies product1[k] == s_word[k] by {}
    }
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    //  h_wit witnesses the h-part satisfiability
    //  target = concat(product1, inv(a_rcoset_rep(product1))) =~= product1 =~= s_word
    assert(concat(product1, inverse_word(a_rcoset_rep(data, product1))) =~= product1) by {
        assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
        let c = concat(product1, e);
        assert(c.len() == product1.len());
        assert forall|k: int| 0 <= k < product1.len() implies c[k] == product1[k] by {}
    }
    lemma_a_rcoset_h_satisfiable(data, product1, h_wit);

    //  embed_a(h1) ≡ product1
    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h1, n1);

    //  product2 = [inv(s)] · embed_a(h1) ≡ [inv(s)] · product1 ≡ [inv(s)] · [s] ≡ ε
    let product2 = concat(inv_s_word, apply_embedding(a_words(data), h1));
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p1, inv_s_word, apply_embedding(a_words(data), h1), product1);

    assert(inverse_word(s_word) =~= inv_s_word) by {
        assert(s_word.first() == s);
        assert(s_word.drop_first().len() == 0);
        assert(inverse_word(s_word.drop_first()) =~= e);
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p1, s_word);
    crate::presentation::lemma_equiv_transitive(p1, product2,
        concat(inv_s_word, product1), e);

    //  product2 ≡ ε → product2 is in the subgroup
    crate::word::lemma_concat_word_valid(inv_s_word,
        apply_embedding(a_words(data), h1), n1);
    crate::benign::lemma_identity_in_generated_subgroup(p1, a_words(data));
    crate::presentation::lemma_equiv_symmetric(p1, product2, e);
    lemma_in_subgroup_equiv(p1, a_words(data), e, product2);

    //  product2 in subgroup → a_rcoset_rep(product2) =~= ε
    lemma_a_rcoset_in_subgroup(data, product2);

    //  a_rcoset_h(product2) =~= ε: need h_min_len = 0
    assert(word_valid(e, k_size(data))) by { assert(e.len() == 0); }
    assert(apply_embedding(a_words(data), e) =~= e);
    let target_p2 = concat(product2, inverse_word(a_rcoset_rep(data, product2)));
    //  target =~= product2 (since rep = ε) ≡ ε → equiv(ε, target)
    crate::presentation::lemma_equiv_symmetric(p1, product2, e);
    assert(has_left_h_witness_of_len(data, target_p2, 0nat));
    let pred_p2 = |l: nat| has_left_h_witness_of_len(data, target_p2, l);
    assert(pred_p2(0nat));
    assert(no_pred_below(pred_p2, 0nat));
    lemma_nat_well_ordering(pred_p2, 0nat);
    let hl_p2 = a_rcoset_h_min_len(data, product2);
    lemma_no_pred_below_forces_zero(pred_p2, hl_p2);
    assert(word_lex_rank_base(e, h_lex_base(data)) == 0nat);
    assert(has_left_h_witness_of_len_rank(data, target_p2, 0nat, 0nat));
    assert(no_smaller_h_lex(data, target_p2, 0nat, 0nat));
    lemma_scan_min_h_lex(data, target_p2, 0, 0, 0);
    //  a_rcoset_h(product2) has length 0 → =~= ε
}

///  For a single G₁ symbol s: act_word([s], ε, []) = g1_decompose_state([s]).
///  This connects the symbol-by-symbol action to the one-shot decomposition.
pub proof fn lemma_act_single_eq_decompose(
    data: AmalgamatedData,
    s: Symbol,
)
    requires
        amalgamated_data_valid(data),
        generator_index(s) < data.p1.num_generators,
    ensures
        act_word(data, Seq::new(1, |_i: int| s), empty_word(), Seq::<Syllable>::empty())
            == g1_decompose_state(data, Seq::new(1, |_i: int| s)),
{
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);

    //  act_word([s], ε, []) = act_sym(s, ε, [])
    lemma_act_word_single(data, s, e, Seq::<Syllable>::empty());

    //  act_sym(s, ε, []) = act_left_sym(s, ε, []) since gen_index(s) < n1

    //  act_left_sym uses right-coset decomposition:
    //    product = concat([s], embed_a(ε)) = concat([s], ε) =~= [s]
    //    h' = a_rcoset_h(product), rep' = a_rcoset_rep(product)

    //  g1_decompose_state([s]) uses the same right-coset fns.
    //  Since product =~= [s]: the rcoset reps and h-parts are the same.
    assert(apply_embedding(a_words(data), e) =~= e);
    let product = concat(s_word, apply_embedding(a_words(data), e));
    assert(product =~= s_word) by {
        assert(product.len() == s_word.len());
        assert forall|k: int| 0 <= k < s_word.len()
            implies product[k] == s_word[k] by {}
    }
    //  product =~= s_word → a_rcoset_rep(product) == a_rcoset_rep(s_word)
    //  and a_rcoset_h(product) == a_rcoset_h(s_word)
}

//  ============================================================
//  Part K: Bridge — in_generated_subgroup ↔ apply_embedding
//  ============================================================

///  If w is in the generated subgroup, there exists a K-word whose embedding ≡ w.
///  This bridges in_generated_subgroup (existential over factors) to
///  apply_embedding (K-word based).
///
///  Proof: in_generated_subgroup gives factors with concat_all(factors) ≡ w.
///  Each factor = gens[i] or inv(gens[i]). Map to K-word: Gen(i) or Inv(i).
///  Then apply_embedding produces the same word as concat_all.
pub proof fn lemma_subgroup_to_k_word(
    p: Presentation,
    gens: Seq<Word>,
    w: Word,
)
    requires
        in_generated_subgroup(p, gens, w),
    ensures
        exists|h: Word|
            word_valid(h, gens.len())
            && equiv_in_presentation(p, apply_embedding(gens, h), w),
{
    //  Extract factors witness
    let factors: Seq<Word> = choose|factors: Seq<Word>|
        #[trigger] factors_from_generators(gens, factors)
        && equiv_in_presentation(p, concat_all(factors), w);

    //  Build the K-word from the factors by induction
    lemma_factors_to_k_word_exists(p, gens, factors);
    //  Now: exists|h| word_valid(h, gens.len()) && equiv(embed(h), concat_all(factors))

    //  Chain: embed(h) ≡ concat_all(factors) ≡ w
    let h: Word = choose|h: Word| word_valid(h, gens.len())
        && equiv_in_presentation(p, apply_embedding(gens, h), concat_all(factors));
    crate::presentation::lemma_equiv_transitive(p,
        apply_embedding(gens, h), concat_all(factors), w);
}

///  Helper: given factors from generators, construct a K-word with matching embedding.
proof fn lemma_factors_to_k_word_exists(
    p: Presentation,
    gens: Seq<Word>,
    factors: Seq<Word>,
)
    requires
        factors_from_generators(gens, factors),
    ensures
        exists|h: Word|
            word_valid(h, gens.len())
            && equiv_in_presentation(p, apply_embedding(gens, h), concat_all(factors)),
    decreases factors.len(),
{
    if factors.len() == 0 {
        //  h = ε: word_valid(ε, anything) and embed(ε) = ε = concat_all([])
        let h = empty_word();
        assert(word_valid(h, gens.len())) by { assert(h.len() == 0); }
        assert(apply_embedding(gens, h) =~= empty_word());
        assert(concat_all(factors) =~= empty_word());
        crate::presentation::lemma_equiv_refl(p, empty_word());
        //  Witness the exists: h = ε satisfies both conditions
        assert(equiv_in_presentation(p, apply_embedding(gens, h), concat_all(factors)));
    } else {
        //  IH on rest
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies is_generator_or_inverse(gens, #[trigger] rest[k])
            by { assert(rest[k] == factors[k + 1]); }
        }
        lemma_factors_to_k_word_exists(p, gens, rest);
        //  exists|h_rest| word_valid(h_rest, gens.len()) && equiv(embed(h_rest), concat_all(rest))

        let h_rest: Word = choose|h_rest: Word| word_valid(h_rest, gens.len())
            && equiv_in_presentation(p, apply_embedding(gens, h_rest), concat_all(rest));

        //  First factor: is_generator_or_inverse(gens, factors.first())
        //  So factors.first() = gens[i] or inv(gens[i]) for some i < gens.len()
        let first = factors.first();
        let i: nat = choose|i: nat| i < gens.len()
            && (first =~= gens[i as int] || first =~= inverse_word(gens[i as int]));

        //  Construct the K-word: [sym] ++ h_rest
        let sym = if first =~= gens[i as int] { Symbol::Gen(i) } else { Symbol::Inv(i) };
        let h = Seq::new(1, |_j: int| sym) + h_rest;

        //  word_valid(h, gens.len()): sym has gen_index = i < gens.len(), rest is word_valid by IH
        assert(word_valid(h, gens.len())) by {
            assert(symbol_valid(sym, gens.len()));
            assert forall|k: int| 0 <= k < h.len()
                implies symbol_valid(h[k], gens.len())
            by {
                if k == 0 {
                } else {
                    assert(h[k] == h_rest[k - 1]);
                }
            }
        }

        //  embed(h) = concat(embed_sym(sym), embed(h_rest))
        //           = concat(first, embed(h_rest))
        //           ≡ concat(first, concat_all(rest))   [by IH on h_rest]
        //           = concat_all(factors)

        //  embed_sym(sym) =~= first
        assert(apply_embedding_symbol(gens, sym) =~= first);

        //  Unfold apply_embedding(gens, h) one level:
        //  h = [sym] ++ h_rest, so h.first() = sym, h.drop_first() =~= h_rest
        assert(h.len() > 0);
        assert(h.first() == sym);
        assert(h.drop_first() =~= h_rest) by {
            let d = h.drop_first();
            assert(d.len() == h_rest.len());
            assert forall|k: int| 0 <= k < h_rest.len()
                implies d[k] == h_rest[k] by {}
        }
        //  apply_embedding(gens, h) = concat(embed_sym(h.first()), embed(h.drop_first()))
        //                           = concat(embed_sym(sym), embed(h_rest))
        //                           = concat(first, embed(h_rest))

        //  IH gives: equiv(embed(h_rest), concat_all(rest))
        //  By right-congruence: concat(first, embed(h_rest)) ≡ concat(first, concat_all(rest))
        crate::presentation_lemmas::lemma_equiv_concat_right(p, first,
            apply_embedding(gens, h_rest), concat_all(rest));

        //  concat(first, concat_all(rest)) = concat_all(factors)
        //  So: equiv(concat(first, embed(h_rest)), concat_all(factors))
        //  And: apply_embedding(gens, h) =~= concat(first, embed(h_rest))
        //  Therefore: equiv(apply_embedding(gens, h), concat_all(factors))
        assert(equiv_in_presentation(p, apply_embedding(gens, h), concat_all(factors)));
    }
}

///  concat_all distributes over sequence append.
proof fn lemma_concat_all_append(xs: Seq<Word>, ys: Seq<Word>)
    ensures
        concat_all(xs + ys) =~= concat(concat_all(xs), concat_all(ys)),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert((xs + ys) =~= ys) by {
            assert((xs + ys).len() == ys.len());
            assert forall|k: int| 0 <= k < ys.len()
                implies (xs + ys)[k] == ys[k] by {}
        }
        assert(concat_all(xs) =~= empty_word());
        assert(concat(empty_word(), concat_all(ys)) =~= concat_all(ys)) by {
            let c = concat(empty_word(), concat_all(ys));
            assert(c.len() == concat_all(ys).len());
            assert forall|k: int| 0 <= k < c.len()
                implies c[k] == concat_all(ys)[k] by {}
        }
    } else {
        //  concat_all(xs ++ ys) = concat(xs.first(), concat_all(xs.drop_first() ++ ys))
        assert((xs + ys).first() == xs.first());
        assert((xs + ys).drop_first() =~= xs.drop_first() + ys) by {
            let lhs = (xs + ys).drop_first();
            let rhs = xs.drop_first() + ys;
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < rhs.len()
                implies lhs[k] == rhs[k] by {}
        }
        //  IH: concat_all(xs.drop_first() ++ ys) =~= concat(concat_all(xs.drop_first()), concat_all(ys))
        lemma_concat_all_append(xs.drop_first(), ys);
        //  concat_all(xs) = concat(xs.first(), concat_all(xs.drop_first()))
        //  concat(concat_all(xs), concat_all(ys)) = concat(concat(xs.first(), concat_all(xs.drop_first())), concat_all(ys))
        //  By concat associativity: = concat(xs.first(), concat(concat_all(xs.drop_first()), concat_all(ys)))
        //  = concat(xs.first(), concat_all(xs.drop_first() ++ ys)) [by IH]
        //  = concat_all(xs ++ ys)
    }
}

///  Generated subgroup is closed under concatenation.
pub proof fn lemma_subgroup_concat(
    p: Presentation, gens: Seq<Word>, a: Word, b: Word,
)
    requires
        in_generated_subgroup(p, gens, a),
        in_generated_subgroup(p, gens, b),
    ensures
        in_generated_subgroup(p, gens, concat(a, b)),
{
    //  Extract factor witnesses
    let fa: Seq<Word> = choose|fa: Seq<Word>|
        #[trigger] factors_from_generators(gens, fa)
        && equiv_in_presentation(p, concat_all(fa), a);
    let fb: Seq<Word> = choose|fb: Seq<Word>|
        #[trigger] factors_from_generators(gens, fb)
        && equiv_in_presentation(p, concat_all(fb), b);

    //  Combined factors: fa ++ fb
    let fab = fa + fb;
    assert(factors_from_generators(gens, fab)) by {
        assert forall|k: int| 0 <= k < fab.len()
            implies is_generator_or_inverse(gens, #[trigger] fab[k])
        by {
            if k < fa.len() {
                assert(fab[k] == fa[k]);
            } else {
                assert(fab[k] == fb[k - fa.len()]);
            }
        }
    }

    //  concat_all(fab) =~= concat(concat_all(fa), concat_all(fb))
    lemma_concat_all_append(fa, fb);
    //  concat(concat_all(fa), concat_all(fb)) ≡ concat(a, b) by congruence
    crate::presentation_lemmas::lemma_equiv_concat(p,
        concat_all(fa), a, concat_all(fb), b);
    //  Since concat_all(fab) =~= concat(concat_all(fa), concat_all(fb)) (extensional eq = eq for Seq),
    //  and equiv(concat(concat_all(fa), concat_all(fb)), concat(a, b)),
    //  we get equiv(concat_all(fab), concat(a, b)).
}

///  Inverse preserves equivalence: if a ≡ b then inv(a) ≡ inv(b).
///  Split into two helpers to stay within rlimit.
proof fn lemma_equiv_inverse_helper(
    p: Presentation, a: Word, b: Word,
)
    requires
        equiv_in_presentation(p, a, b),
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
    ensures
        //  concat(inv(b), a) ≡ ε
        equiv_in_presentation(p, concat(inverse_word(b), a), empty_word()),
{
    let inv_b = inverse_word(b);
    crate::word::lemma_inverse_word_valid(b, p.num_generators);
    //  inv(b) * b ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_left(p, b);
    //  a ≡ b → concat(inv(b), a) ≡ concat(inv(b), b) by right-congruence
    crate::presentation_lemmas::lemma_equiv_concat_right(p, inv_b, a, b);
    //  ε ≡ concat(inv(b), b) by symmetry
    crate::word::lemma_concat_word_valid(inv_b, b, p.num_generators);
    crate::presentation::lemma_equiv_symmetric(p, concat(inv_b, b), empty_word());
    //  concat(inv(b), a) ≡ concat(inv(b), b) ≡... need direction.
    //  We have: equiv(concat(inv_b, a), concat(inv_b, b)) from right-congruence
    //  And: equiv(concat(inv_b, b), ε) from word_inverse_left
    //  Transitivity: equiv(concat(inv_b, a), ε)
    crate::presentation::lemma_equiv_transitive(p,
        concat(inv_b, a), concat(inv_b, b), empty_word());
}

pub proof fn lemma_equiv_inverse(
    p: Presentation, a: Word, b: Word,
)
    requires
        equiv_in_presentation(p, a, b),
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
    ensures
        equiv_in_presentation(p, inverse_word(a), inverse_word(b)),
{
    let inv_a = inverse_word(a);
    let inv_b = inverse_word(b);
    crate::word::lemma_inverse_word_valid(a, p.num_generators);
    crate::word::lemma_inverse_word_valid(b, p.num_generators);

    //  From helper: concat(inv(b), a) ≡ ε
    lemma_equiv_inverse_helper(p, a, b);

    //  concat(concat(inv(b), a), inv(a)) ≡ concat(ε, inv(a)) by left-congruence
    crate::word::lemma_concat_word_valid(inv_b, a, p.num_generators);
    crate::presentation_lemmas::lemma_equiv_concat_left(p,
        concat(inv_b, a), empty_word(), inv_a);
    //  LHS ≡ concat(ε, inv(a)) =~= inv(a)

    //  a * inv(a) ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_right(p, a);
    //  concat(inv(b), concat(a, inv(a))) ≡ concat(inv(b), ε) by right-congruence
    crate::presentation_lemmas::lemma_equiv_concat_right(p, inv_b,
        concat(a, inv_a), empty_word());
    //  RHS ≡ concat(inv(b), ε) =~= inv(b)

    //  Key: concat(concat(inv(b), a), inv(a)) =~= concat(inv(b), concat(a, inv(a))) [seq assoc]
    //  From above: LHS ≡ inv(a) and RHS ≡ inv(b)
    //  Since LHS =~= RHS: inv(a) ≡ LHS =~= RHS ≡ inv(b)
    //  i.e., equiv(inv(a), inv(b)) by the chain.

    //  Step by step for Z3:
    //  equiv(concat(concat(inv_b, a), inv_a), concat(ε, inv_a))  [from left-congruence]
    //  equiv(concat(inv_b, concat(a, inv_a)), concat(inv_b, ε))  [from right-congruence]
    //  These two LHS expressions are =~= (seq associativity)
    //  So: equiv(concat(inv_b, concat(a, inv_a)), concat(ε, inv_a)) by chain:
    //    concat(inv_b, concat(a, inv_a)) =~= concat(concat(inv_b, a), inv_a) ≡ concat(ε, inv_a)
    //  And: equiv(concat(inv_b, ε), concat(ε, inv_a)) by transitivity with above
    //    concat(inv_b, ε) ≡ concat(inv_b, concat(a, inv_a)) ≡ concat(ε, inv_a)
    //  And concat(inv_b, ε) =~= inv_b and concat(ε, inv_a) =~= inv_a
    //  So equiv(inv_b, inv_a), hence equiv(inv_a, inv_b) by symmetry.

    //  Explicit chain: connect the two congruence results through seq associativity.
    //  We have:
    //    (A) equiv(concat(concat(inv_b, a), inv_a), concat(ε, inv_a))  [left-cong]
    //    (B) equiv(concat(inv_b, concat(a, inv_a)), concat(inv_b, ε))  [right-cong]
    //  And concat(concat(inv_b, a), inv_a) =~= concat(inv_b, concat(a, inv_a)) [assoc]

    //  From (A): symmetry gives equiv(concat(ε, inv_a), concat(concat(inv_b, a), inv_a))
    //  =~= equiv(concat(ε, inv_a), concat(inv_b, concat(a, inv_a)))
    //  Then transitivity with (B): equiv(concat(ε, inv_a), concat(inv_b, ε))
    //  word_valid for intermediate expressions
    crate::word::lemma_concat_word_valid(concat(inv_b, a), inv_a, p.num_generators);
    crate::word::lemma_concat_word_valid(a, inv_a, p.num_generators);
    //  Symmetry on (A): equiv(concat(ε, inv_a), concat(concat(inv_b, a), inv_a))
    crate::presentation::lemma_equiv_symmetric(p,
        concat(concat(inv_b, a), inv_a), concat(empty_word(), inv_a));
    //  Transitivity: concat(ε, inv_a) ≡ concat(concat(inv_b,a), inv_a) =~= concat(inv_b, concat(a,inv_a)) ≡ concat(inv_b, ε)
    //  The middle =~= (assoc) is automatic for Z3 since Seq =~= implies ==.
    //  But the symmetry gave equiv(concat(ε, inv_a), concat(concat(inv_b,a), inv_a))
    //  And (B) gives equiv(concat(inv_b, concat(a, inv_a)), concat(inv_b, ε))
    //  These connect via assoc: concat(concat(inv_b,a), inv_a) =~= concat(inv_b, concat(a, inv_a))
    //  Seq associativity: concat(concat(x,y),z) =~= concat(x, concat(y,z))
    assert(concat(concat(inv_b, a), inv_a) =~= concat(inv_b, concat(a, inv_a))) by {
        let lhs = concat(concat(inv_b, a), inv_a);
        let rhs = concat(inv_b, concat(a, inv_a));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inv_b.len() {} else if k < inv_b.len() + a.len() {} else {}
        }
    }
    crate::presentation::lemma_equiv_transitive(p,
        concat(empty_word(), inv_a),
        concat(concat(inv_b, a), inv_a),
        concat(inv_b, empty_word()));
    //  Now: equiv(concat(ε, inv_a), concat(inv_b, ε))
    //  concat(ε, inv_a) =~= inv_a and concat(inv_b, ε) =~= inv_b
    //  So equiv(inv_a, inv_b). Z3 should handle the =~= substitution.
    assert(concat(empty_word(), inv_a) =~= inv_a) by {
        let c = concat(empty_word(), inv_a);
        assert(c.len() == inv_a.len());
        assert forall|k: int| 0 <= k < inv_a.len() implies c[k] == inv_a[k] by {}
    }
    assert(concat(inv_b, empty_word()) =~= inv_b) by {
        let c = concat(inv_b, empty_word());
        assert(c.len() == inv_b.len());
        assert forall|k: int| 0 <= k < inv_b.len() implies c[k] == inv_b[k] by {}
    }
}

///  Generated subgroup is closed under equivalence (already proved as lemma_in_subgroup_equiv).

///  Reverse a sequence of words and invert each element.
pub open spec fn reverse_invert_factors(factors: Seq<Word>) -> Seq<Word>
    decreases factors.len(),
{
    if factors.len() == 0 {
        Seq::empty()
    } else {
        reverse_invert_factors(factors.drop_first())
            + Seq::new(1, |_i: int| inverse_word(factors.first()))
    }
}

///  Each factor in reverse_invert_factors is still a generator-or-inverse.
proof fn lemma_reverse_invert_preserves_generators(
    gens: Seq<Word>, factors: Seq<Word>,
)
    requires
        factors_from_generators(gens, factors),
    ensures
        factors_from_generators(gens, reverse_invert_factors(factors)),
    decreases factors.len(),
{
    if factors.len() == 0 {
    } else {
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies is_generator_or_inverse(gens, #[trigger] rest[k])
            by { assert(rest[k] == factors[k + 1]); }
        }
        lemma_reverse_invert_preserves_generators(gens, rest);
        let rif = reverse_invert_factors(factors);
        let rif_rest = reverse_invert_factors(rest);
        let inv_first = inverse_word(factors.first());
        assert forall|k: int| 0 <= k < rif.len()
            implies is_generator_or_inverse(gens, #[trigger] rif[k])
        by {
            if k < rif_rest.len() {
                assert(rif[k] == rif_rest[k]);
            } else {
                assert(rif[k] == inv_first);
                //  inv_first = inv(factors.first())
                //  factors.first() is is_generator_or_inverse(gens, ...)
                //  So exists i: factors.first() == gens[i] or factors.first() == inv(gens[i])
                //  Case 1: factors.first() == gens[i] → inv_first == inv(gens[i])
                //    → is_generator_or_inverse(gens, inv_first) with the inv case ✓
                //  Case 2: factors.first() == inv(gens[i]) → inv_first == inv(inv(gens[i]))
                //    inv(inv(gens[i])) =~= gens[i] by inverse involution
                //    → is_generator_or_inverse(gens, inv_first) with the direct case ✓
                let i: nat = choose|i: nat| i < gens.len()
                    && (factors.first() =~= gens[i as int]
                        || factors.first() =~= inverse_word(gens[i as int]));
                if factors.first() =~= gens[i as int] {
                    //  inv_first = inv(gens[i]) → is_gen_or_inv
                } else {
                    //  inv_first = inv(inv(gens[i])) =~= gens[i]
                    crate::word::lemma_inverse_involution(gens[i as int]);
                }
            }
        }
    }
}

///  concat_all of factors_from_generators produces a word_valid word.
proof fn lemma_concat_all_word_valid(
    gens: Seq<Word>, factors: Seq<Word>, n: nat,
)
    requires
        factors_from_generators(gens, factors),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], n),
    ensures
        word_valid(concat_all(factors), n),
    decreases factors.len(),
{
    if factors.len() == 0 {
    } else {
        let rest = factors.drop_first();
        assert(factors_from_generators(gens, rest)) by {
            assert forall|k: int| 0 <= k < rest.len()
                implies is_generator_or_inverse(gens, #[trigger] rest[k])
            by { assert(rest[k] == factors[k + 1]); }
        }
        lemma_concat_all_word_valid(gens, rest, n);
        //  factors.first() is word_valid: it's gens[i] or inv(gens[i])
        let first = factors.first();
        let i: nat = choose|i: nat| i < gens.len()
            && (first =~= gens[i as int] || first =~= inverse_word(gens[i as int]));
        if first =~= inverse_word(gens[i as int]) {
            crate::word::lemma_inverse_word_valid(gens[i as int], n);
        }
        crate::word::lemma_concat_word_valid(first, concat_all(rest), n);
    }
}

///  concat_all of reverse_invert_factors ≡ inverse_word of concat_all.
proof fn lemma_reverse_invert_is_inverse(
    p: Presentation, factors: Seq<Word>,
)
    ensures
        equiv_in_presentation(p,
            concat_all(reverse_invert_factors(factors)),
            inverse_word(concat_all(factors))),
    decreases factors.len(),
{
    if factors.len() == 0 {
        //  All three expressions evaluate to ε when factors is empty:
        let rif = reverse_invert_factors(factors);
        let ca = concat_all(factors);
        assert(rif.len() == 0);
        assert(concat_all(rif) =~= empty_word());
        assert(ca =~= empty_word());
        assert(inverse_word(ca) =~= empty_word()) by {
            assert(inverse_word(empty_word()).len() == 0);
        }
        crate::presentation::lemma_equiv_refl(p, concat_all(rif));
        //  Explicitly assert the postcondition using bound variables:
        assert(equiv_in_presentation(p, concat_all(rif), inverse_word(ca)));
        return;
    } else {
        let rest = factors.drop_first();
        let first = factors.first();
        let inv_first = inverse_word(first);
        let rif_rest = reverse_invert_factors(rest);

        lemma_reverse_invert_is_inverse(p, rest);
        crate::word::lemma_inverse_concat(first, concat_all(rest));
        lemma_concat_all_append(rif_rest, Seq::new(1, |_i: int| inv_first));
        crate::presentation_lemmas::lemma_equiv_concat_left(p,
            concat_all(rif_rest), inverse_word(concat_all(rest)), inv_first);
        //  Connect to postcondition:
        //  Postcondition LHS = concat_all(reverse_invert_factors(factors))
        //    = concat_all(rif_rest ++ [inv_first])  [by def of reverse_invert_factors]
        //    =~= concat(concat_all(rif_rest), concat_all([inv_first]))  [by concat_all_append]
        //    =~= concat(concat_all(rif_rest), inv_first)  [concat_all of singleton]
        //  Key =~= chain for the postcondition:
        //  LHS of postcondition: concat_all(reverse_invert_factors(factors))
        //  reverse_invert_factors(factors) = rif_rest ++ [inv_first] by definition
        //  concat_all_append gave:
        //    concat_all(rif_rest ++ singleton) =~= concat(concat_all(rif_rest), concat_all(singleton))
        //  concat_all(singleton) where singleton = [inv_first]:
        let singleton = Seq::new(1, |_i: int| inv_first);
        assert(singleton.len() == 1);
        assert(singleton.first() == inv_first);
        let singleton_rest = singleton.drop_first();
        assert(singleton_rest.len() == 0);
        assert(concat_all(singleton_rest) =~= empty_word());
        //  concat_all(singleton) = concat(singleton.first(), concat_all(singleton.drop_first()))
        //                        = concat(inv_first, ε)
        assert(concat(inv_first, empty_word()) =~= inv_first) by {
            let c = concat(inv_first, empty_word());
            assert(c.len() == inv_first.len());
            assert forall|k: int| 0 <= k < c.len() implies c[k] == inv_first[k] by {}
        }
        //  So: LHS =~= concat(concat_all(rif_rest), inv_first)

        //  RHS of postcondition: inverse_word(concat_all(factors))
        //  = inverse_word(concat(first, concat_all(rest))) [concat_all unfolds]
        //  =~= concat(inverse_word(concat_all(rest)), inv_first) [from inverse_concat]

        //  equiv_concat_left gave:
        //    equiv(concat(concat_all(rif_rest), inv_first), concat(inv(concat_all(rest)), inv_first))
        //  LHS =~= postcondition LHS (shown above)
        //  RHS =~= postcondition RHS (from inverse_concat)
        //  So: equiv(postcondition LHS, postcondition RHS). QED.
        return;
    }
}

///  Generated subgroup is closed under inverse.
pub proof fn lemma_subgroup_inverse(
    p: Presentation, gens: Seq<Word>, w: Word,
)
    requires
        in_generated_subgroup(p, gens, w),
        presentation_valid(p),
        word_valid(w, p.num_generators),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], p.num_generators),
    ensures
        in_generated_subgroup(p, gens, inverse_word(w)),
{
    let n = p.num_generators;
    let fa: Seq<Word> = choose|fa: Seq<Word>|
        #[trigger] factors_from_generators(gens, fa)
        && equiv_in_presentation(p, concat_all(fa), w);

    let rif = reverse_invert_factors(fa);
    lemma_reverse_invert_preserves_generators(gens, fa);
    lemma_reverse_invert_is_inverse(p, fa);
    //  concat_all(rif) ≡ inv(concat_all(fa))

    //  concat_all(fa) is word_valid (each factor is gens[i] or inv(gens[i]), all word_valid):
    lemma_concat_all_word_valid(gens, fa, n);

    //  inv(concat_all(fa)) ≡ inv(w) by lemma_equiv_inverse:
    lemma_equiv_inverse(p, concat_all(fa), w);

    //  Chain: concat_all(rif) ≡ inv(concat_all(fa)) ≡ inv(w)
    crate::word::lemma_inverse_word_valid(concat_all(fa), n);
    crate::word::lemma_inverse_word_valid(w, n);
    crate::presentation::lemma_equiv_transitive(p,
        concat_all(rif), inverse_word(concat_all(fa)), inverse_word(w));

    //  in_generated_subgroup(concat_all(rif)): rif satisfies factors_from_generators, and
    //  concat_all(rif) ≡ concat_all(rif) by reflexivity.
    crate::presentation::lemma_equiv_refl(p, concat_all(rif));
    assert(in_generated_subgroup(p, gens, concat_all(rif)));
    //  + equiv(concat_all(rif), inv(w)) → in_generated_subgroup(inv(w))
    lemma_in_subgroup_equiv(p, gens, concat_all(rif), inverse_word(w));
}

//  ============================================================
//  Part K2: Coset invariance — same coset → same canonical rep
//  ============================================================

///  same_left_coset is symmetric.
proof fn lemma_same_left_coset_symmetric(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
    ensures
        same_left_coset(data, g2, g1),
{
    //  same_left_coset(g1, g2) = in_left_subgroup(concat(inv(g1), g2))
    //  same_left_coset(g2, g1) = in_left_subgroup(concat(inv(g2), g1))
    //  concat(inv(g2), g1) = inv(concat(inv(g1), g2)) approximately
    //  inv(concat(inv(g1), g2)) = concat(inv(g2), inv(inv(g1))) = concat(inv(g2), g1)
    //  So: in_left_subgroup(concat(inv(g2), g1)) follows from
    //      in_left_subgroup(concat(inv(g1), g2)) + subgroup inverse closure.

    let diff12 = concat(inverse_word(g1), g2);
    //  in_left_subgroup(diff12) is given.
    //  inv(diff12) = inv(concat(inv(g1), g2)) =~= concat(inv(g2), inv(inv(g1)))
    //             =~= concat(inv(g2), g1) [by inverse involution]
    crate::word::lemma_inverse_concat(inverse_word(g1), g2);
    //  inv(diff12) =~= concat(inv(g2), inv(inv(g1)))
    crate::word::lemma_inverse_involution(g1);
    //  inv(inv(g1)) =~= g1

    //  inv(diff12) =~= concat(inv(g2), g1)
    let diff21 = concat(inverse_word(g2), g1);

    //  in_left_subgroup(diff12) → in_left_subgroup(inv(diff12)) by subgroup inverse
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(g1, data.p1.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(g1), g2, data.p1.num_generators);
    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], data.p1.num_generators) by {
        assert(word_valid(data.identifications[i].0, data.p1.num_generators));
    }
    lemma_subgroup_inverse(data.p1, a_words(data), diff12);
    //  in_left_subgroup(inv(diff12))
    //  inv(diff12) =~= diff21, so in_left_subgroup(diff21)
}

///  same_left_coset is transitive.
proof fn lemma_same_left_coset_transitive(
    data: AmalgamatedData, g1: Word, g2: Word, g3: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        same_left_coset(data, g2, g3),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        word_valid(g3, data.p1.num_generators),
    ensures
        same_left_coset(data, g1, g3),
{
    //  same_left_coset(g1, g2) = in_left_subgroup(inv(g1) * g2)
    //  same_left_coset(g2, g3) = in_left_subgroup(inv(g2) * g3)
    //  same_left_coset(g1, g3) = in_left_subgroup(inv(g1) * g3)
    //  inv(g1) * g3 = inv(g1) * g2 * inv(g2) * g3
    //  = (inv(g1)*g2) * (inv(g2)*g3)
    //  Both factors are in the subgroup → product is in the subgroup (by concat closure).
    let d12 = concat(inverse_word(g1), g2);
    let d23 = concat(inverse_word(g2), g3);

    //  in_left_subgroup(d12) && in_left_subgroup(d23)
    //  → in_left_subgroup(concat(d12, d23)) by subgroup_concat
    lemma_subgroup_concat(data.p1, a_words(data), d12, d23);
    //  concat(d12, d23) = concat(concat(inv(g1), g2), concat(inv(g2), g3))
    //                   =~= concat(inv(g1), concat(g2, concat(inv(g2), g3)))
    //                   and g2 * inv(g2) ≡ ε...
    //  Actually: concat(d12, d23) ≡ inv(g1) * g2 * inv(g2) * g3 ≡ inv(g1) * g3 (group theory)
    //  So in_left_subgroup(concat(d12, d23)) and concat(d12, d23) ≡ inv(g1)*g3
    //  → in_left_subgroup(inv(g1)*g3) by equiv closure.

    //  The equiv: concat(d12, d23) ≡ concat(inv(g1), g3) because:
    //  d12 * d23 = inv(g1)*g2*inv(g2)*g3
    //  g2*inv(g2) ≡ ε, so inv(g1)*g2*inv(g2)*g3 ≡ inv(g1)*g3.
    //  Formally: by right inverse of g2 + congruence.
    crate::presentation_lemmas::lemma_word_inverse_right(data.p1, g2);
    //  g2 * inv(g2) ≡ ε
    //  concat(d12, d23) = concat(concat(inv(g1), g2), concat(inv(g2), g3))
    //  ≡ concat(inv(g1), concat(g2, concat(inv(g2), g3))) [assoc]
    //  ≡ concat(inv(g1), concat(concat(g2, inv(g2)), g3)) [assoc]
    //  ≡ concat(inv(g1), concat(ε, g3)) [g2*inv(g2) ≡ ε congruence]
    //  = concat(inv(g1), g3) [concat(ε, g3) =~= g3]
    //  This chain needs several transitivity + congruence steps.
    //  Use lemma_in_subgroup_equiv to bridge.
    let d13 = concat(inverse_word(g1), g3);
    let p1 = data.p1;
    crate::word::lemma_inverse_word_valid(g1, p1.num_generators);
    crate::word::lemma_inverse_word_valid(g2, p1.num_generators);

    //  Step 1: g2 * inv(g2) ≡ ε → concat(concat(g2, inv(g2)), g3) ≡ concat(ε, g3)
    crate::presentation_lemmas::lemma_equiv_concat_left(p1,
        concat(g2, inverse_word(g2)), empty_word(), g3);

    //  Step 2: seq assoc + =~= to get equiv(concat(g2, concat(inv(g2), g3)), g3)
    assert(concat(concat(g2, inverse_word(g2)), g3)
        =~= concat(g2, concat(inverse_word(g2), g3))) by {
        let l = concat(concat(g2, inverse_word(g2)), g3);
        let r = concat(g2, concat(inverse_word(g2), g3));
        assert(l.len() == r.len());
        assert forall|k: int| 0 <= k < l.len() implies l[k] == r[k]
        by { if k < g2.len() {} else if k < g2.len() + inverse_word(g2).len() {} else {} }
    }
    assert(concat(empty_word(), g3) =~= g3) by {
        let c = concat(empty_word(), g3);
        assert(c.len() == g3.len());
        assert forall|k: int| 0 <= k < c.len() implies c[k] == g3[k] by {}
    }
    //  Now Z3 has equiv(concat(g2, concat(inv(g2), g3)), g3)

    //  Step 3: right-congruence with inv(g1):
    crate::presentation_lemmas::lemma_equiv_concat_right(p1,
        inverse_word(g1),
        concat(g2, concat(inverse_word(g2), g3)),
        g3);
    //  LHS of the equiv =~= concat(d12, d23) by seq associativity:
    assert(concat(inverse_word(g1), concat(g2, concat(inverse_word(g2), g3)))
        =~= concat(d12, d23)) by {
        let l = concat(inverse_word(g1), concat(g2, concat(inverse_word(g2), g3)));
        let r = concat(d12, d23);
        assert(l.len() == r.len());
        assert forall|k: int| 0 <= k < l.len() implies l[k] == r[k] by {
            if k < inverse_word(g1).len() {}
            else if k < inverse_word(g1).len() + g2.len() {}
            else {}
        }
    }
    //  So: equiv(concat(d12, d23), d13).
    lemma_in_subgroup_equiv(p1, a_words(data), concat(d12, d23), d13);
}

///  If no_pred_below(pred, m) and pred(k), then k >= m.
///  Contrapositive: if k < m, then !pred(k) (from no_pred_below).
proof fn lemma_no_pred_below_implies_ge(pred: spec_fn(nat) -> bool, m: nat, k: nat)
    requires
        no_pred_below(pred, m),
        pred(k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {
    } else {
        if k == (m - 1) as nat {
            //  no_pred_below(pred, m) = !pred(m-1) && ... But pred(k) = pred(m-1). Contradiction.
        } else if k < (m - 1) as nat {
            //  no_pred_below(pred, m) = !pred(m-1) && no_pred_below(pred, m-1)
            lemma_no_pred_below_implies_ge(pred, (m - 1) as nat, k);
        }
    }
}

///  If no_shorter_coset_word(g, m) and has_left_coset_word_of_len(g, k), then k >= m.
proof fn lemma_no_shorter_coset_word_implies_ge(
    data: AmalgamatedData, g: Word, m: nat, k: nat,
)
    requires
        no_shorter_coset_word(data, g, m),
        has_left_coset_word_of_len(data, g, k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {
    } else {
        if k == (m - 1) as nat {
            //  no_shorter_coset_word(g, m) = !has(g, m-1) && ... But has(g, k) = has(g, m-1). Contradiction.
        } else if k < (m - 1) as nat {
            lemma_no_shorter_coset_word_implies_ge(data, g, (m - 1) as nat, k);
        }
    }
}

///  Helper: if same_left_coset(g1, g2), then has_left_coset_word_of_len(g1, l) iff has_...(g2, l).
///  Specifically: has_left_coset_word_of_len(g2, l) → has_left_coset_word_of_len(g1, l).
proof fn lemma_coset_word_transfer(
    data: AmalgamatedData, g1: Word, g2: Word, l: nat,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        has_left_coset_word_of_len(data, g2, l),
    ensures
        has_left_coset_word_of_len(data, g1, l),
{
    let w: Word = choose|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g2, w) && w.len() == l;
    lemma_same_left_coset_transitive(data, g1, g2, w);
}

///  Min-length coset invariance: same coset → same min length.
proof fn lemma_left_min_len_coset_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
    ensures
        left_min_coset_len(data, g1) == left_min_coset_len(data, g2),
{
    let l1 = left_min_coset_len(data, g1);
    let l2 = left_min_coset_len(data, g2);

    //  Satisfiability: both chooses are satisfiable
    lemma_left_min_coset_len_satisfiable(data, g1);
    lemma_left_min_coset_len_satisfiable(data, g2);

    //  Transfer: coset word at l2 for g2 → also for g1 (and vice versa)
    lemma_coset_word_transfer(data, g1, g2, l2);
    //  has_left_coset_word_of_len(g1, l2) — so pred1(l2) holds
    lemma_same_left_coset_symmetric(data, g1, g2);
    lemma_coset_word_transfer(data, g2, g1, l1);
    //  has_left_coset_word_of_len(g2, l1) — so pred2(l1) holds

    //  The choose returned l1 satisfying is_min_coset_len(g1, l1).
    //  Since the choose is satisfiable (from above), l1 satisfies the full predicate.
    //  is_min_coset_len includes no_shorter_coset_word. These are NAMED spec fns, Z3 can extract.
    assert(is_min_coset_len(data, g1, l1));
    assert(no_shorter_coset_word(data, g1, l1));
    lemma_no_shorter_coset_word_implies_ge(data, g1, l1, l2);

    assert(is_min_coset_len(data, g2, l2));
    assert(no_shorter_coset_word(data, g2, l2));
    lemma_no_shorter_coset_word_implies_ge(data, g2, l2, l1);
    //  l1 >= l2 && l2 >= l1 → l1 == l2
}

///  If no_smaller_coset_lex and has_word_of_len_rank, then rank >= min.
proof fn lemma_no_smaller_coset_lex_implies_ge(
    data: AmalgamatedData, g: Word, l: nat, m: nat, k: nat,
)
    requires
        no_smaller_coset_lex(data, g, l, m),
        has_left_coset_word_of_len_rank(data, g, l, k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {
    } else {
        if k == (m - 1) as nat {
        } else if k < (m - 1) as nat {
            lemma_no_smaller_coset_lex_implies_ge(data, g, l, (m - 1) as nat, k);
        }
    }
}

///  Scan for min lex rank at a given length.
proof fn lemma_scan_min_coset_lex(
    data: AmalgamatedData, g: Word, l: nat, current: nat, bound: nat,
)
    requires
        has_left_coset_word_of_len_rank(data, g, l, bound),
        current <= bound,
        no_smaller_coset_lex(data, g, l, current),
    ensures
        exists|r: nat| current <= r && r <= bound
            && #[trigger] is_min_coset_lex(data, g, l, r),
    decreases bound - current,
{
    if has_left_coset_word_of_len_rank(data, g, l, current) {
        assert(is_min_coset_lex(data, g, l, current));
    } else {
        lemma_scan_min_coset_lex(data, g, l, current + 1, bound);
    }
}

///  Lex satisfiability: left_min_coset_lex's choose is satisfiable.
proof fn lemma_left_min_coset_lex_satisfiable(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
    ensures
        is_min_coset_lex(data, g, left_min_coset_len(data, g), left_min_coset_lex(data, g)),
{
    lemma_left_min_coset_len_satisfiable(data, g);
    let l = left_min_coset_len(data, g);
    //  has_left_coset_word_of_len(g, l) → exists w with right length
    let w: Word = choose|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g, w) && w.len() == l;
    //  w has lex rank word_lex_rank_base(w, lex_base(data))
    let wr = word_lex_rank_base(w, lex_base(data));
    assert(has_left_coset_word_of_len_rank(data, g, l, wr));
    assert(no_smaller_coset_lex(data, g, l, 0nat));
    lemma_scan_min_coset_lex(data, g, l, 0, wr);
}

///  Lex transfer: coset word at (l, r) for g2 → also for g1.
proof fn lemma_coset_lex_transfer(
    data: AmalgamatedData, g1: Word, g2: Word, l: nat, r: nat,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        has_left_coset_word_of_len_rank(data, g2, l, r),
    ensures
        has_left_coset_word_of_len_rank(data, g1, l, r),
{
    let w: Word = choose|w: Word| word_valid(w, data.p1.num_generators)
        && same_left_coset(data, g2, w) && w.len() == l
        && word_lex_rank_base(w, lex_base(data)) == r;
    lemma_same_left_coset_transitive(data, g1, g2, w);
}

///  Lex invariance: same coset → same min lex rank (at the same length).
proof fn lemma_left_min_lex_coset_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
    ensures
        left_min_coset_lex(data, g1) == left_min_coset_lex(data, g2),
{
    lemma_left_min_len_coset_invariant(data, g1, g2);
    let l = left_min_coset_len(data, g1);
    //  l == left_min_coset_len(g2)

    let r1 = left_min_coset_lex(data, g1);
    let r2 = left_min_coset_lex(data, g2);

    lemma_left_min_coset_lex_satisfiable(data, g1);
    lemma_left_min_coset_lex_satisfiable(data, g2);

    //  Transfer: lex word at (l, r2) for g2 → also for g1 (and vice versa)
    lemma_coset_lex_transfer(data, g1, g2, l, r2);
    lemma_same_left_coset_symmetric(data, g1, g2);
    lemma_coset_lex_transfer(data, g2, g1, l, r1);

    //  r1 has no_smaller_coset_lex(g1, l, r1). has(g1, l, r2) holds. → r2 >= r1.
    assert(is_min_coset_lex(data, g1, l, r1));
    assert(no_smaller_coset_lex(data, g1, l, r1));
    lemma_no_smaller_coset_lex_implies_ge(data, g1, l, r1, r2);

    assert(is_min_coset_lex(data, g2, l, r2));
    assert(no_smaller_coset_lex(data, g2, l, r2));
    lemma_no_smaller_coset_lex_implies_ge(data, g2, l, r2, r1);
}

///  Coset invariance: same_left_coset(g1, g2) → left_canonical_rep(g1) =~= left_canonical_rep(g2).
///  Proof: same min length (above) → same min lex rank (similar) → same word (lex rank injective).
pub proof fn lemma_left_rep_coset_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        same_left_coset(data, g1, g2),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
    ensures
        left_canonical_rep(data, g1) =~= left_canonical_rep(data, g2),
{
    lemma_left_min_len_coset_invariant(data, g1, g2);
    lemma_left_min_lex_coset_invariant(data, g1, g2);
    let l = left_min_coset_len(data, g1);
    let r = left_min_coset_lex(data, g1);

    //  Both reps satisfy: len == l, lex_rank_base == r (same l and r).
    lemma_left_rep_props(data, g1);
    lemma_left_rep_props(data, g2);
    let rep1 = left_canonical_rep(data, g1);
    let rep2 = left_canonical_rep(data, g2);

    //  rep1.len() == l && word_lex_rank_base(rep1, base) == r
    //  rep2.len() == l && word_lex_rank_base(rep2, base) == r
    //  By lex rank injectivity: rep1 =~= rep2.
    let base = lex_base(data);
    //  Need: symbol_to_column < base for all symbols in rep1 and rep2.
    //  word_valid(rep_i, n) means generator_index < n, so symbol_to_column < 2*n < 2*n+1 = base.
    assert forall|k: int| 0 <= k < rep1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rep1[k]) < base
    by {
        assert(symbol_valid(rep1[k], data.p1.num_generators));
        match rep1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert forall|k: int| 0 <= k < rep2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rep2[k]) < base
    by {
        assert(symbol_valid(rep2[k], data.p1.num_generators));
        match rep2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    //  The chooses are satisfiable (from left_rep_props).
    //  So rep1 and rep2 satisfy their predicates, including lex rank == r.
    //  Explicitly assert the lex rank equality:
    assert(word_lex_rank_base(rep1, base) == r);
    assert(word_lex_rank_base(rep2, base) == r);
    assert(word_lex_rank_base(rep1, base) == word_lex_rank_base(rep2, base));
    assert(base > 0) by { assert(lex_base(data) == 2 * data.p1.num_generators + 1); }
    lemma_word_lex_rank_base_injective(rep1, rep2, base);
}

//  ============================================================
//  Part K3: action_preserves_canonical
//  ============================================================

///  act_word preserves word_valid(h, k) by induction on word length.
///  Base: act_word(ε, h, syls) = (h, syls), preserves trivially.
///  Step: act_word([s] ++ rest, h, syls) = act_word(rest, act_sym(s, h, syls)).
///    Need: act_sym preserves word_valid(h, k).
///    act_sym dispatches to act_left_sym or act_right_sym.
///    Both produce h from left_h_part or right_h_part (choose with word_valid in predicate).
///    The merge case produces concat(merged_h, new_h) — both word_valid → concat is word_valid.
///
///  The choose satisfiability is the key: we need the products encountered
///  during the action to have decompositions. This holds because any valid
///  word in G₁ (or G₂) has a coset decomposition.
///
///  action_preserves_canonical is a precondition (proved from identifications_isomorphic).
///  The proof requires showing choose satisfiability at each step,
///  which follows the same lemma_nat_well_ordering + choose extraction pattern.

///  For a G₁-word w ≡ ε in G₁ acting on identity state:
///  act_word(w, ε, []) gives a state whose decomposition matches the identity.
///
///  This combines the action-to-decompose connection (for single symbols, already proved)
///  with the equivalence chain. The full multi-symbol connection is the remaining gap.
///
///  The full act-to-decompose induction
///  is deferred — it requires showing the transversal decomposition is compatible
///  with the step-by-step merging logic.

///  AFP injectivity from the textbook reduced-sequence action.
///
///  If:
///    - The action is well-defined (relators and inverse pairs act trivially)
///    - w is a G₁-word equivalent to ε in the AFP
///    - There exists a K-word witness for the decomposition (for the converse)
///
///  Then: w ≡ ε in G₁.
///  AFP injectivity: if w is a G₁-word and w ≡ ε in the AFP, and we know
///  the canonical rep and h-part are trivial (from action well-definedness),
///  then w ≡ ε in G₁.
///
///  The full chain: action_well_defined + derivation → act(w) = identity
///                  → left_canonical_rep(w) = ε, left_h_part(w) = ε
///                  → w ≡ ε in G₁ (by converse)
///
///  The act-to-decompose connection is needed to eliminate the rep/h preconditions.
///  The rep = ε and h = ε conditions come from the action analysis.
pub proof fn lemma_afp_injectivity_textbook(
    data: AmalgamatedData,
    w: Word,
    h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(w, data.p1.num_generators),
        //  The decomposition gives identity (from action well-definedness + derivation)
        left_canonical_rep(data, w) =~= empty_word(),
        left_h_part(data, w) =~= empty_word(),
        //  Decomposability witness: the left_h_part choose is satisfiable
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1, apply_embedding(a_words(data), h_witness), w),
    ensures
        equiv_in_presentation(data.p1, w, empty_word()),
{
    lemma_g1_decompose_converse(data, w, h_witness);
}

//  ============================================================
//  Part L: H-part equivalence invariance
//  ============================================================

///  Transfer h-witnesses between equivalent targets.
///  If target1 ≡ target2 and there's a K-word h with embed_a(h) ≡ target1,
///  then embed_a(h) ≡ target2 too (by transitivity).
proof fn lemma_h_witness_transfer(
    data: AmalgamatedData, target1: Word, target2: Word, l: nat,
)
    requires
        has_left_h_witness_of_len(data, target1, l),
        equiv_in_presentation(data.p1, target1, target2),
        presentation_valid(data.p1),
    ensures
        has_left_h_witness_of_len(data, target2, l),
{
    let h: Word = choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p1, apply_embedding(a_words(data), h), target1);
    crate::presentation::lemma_equiv_transitive(
        data.p1, apply_embedding(a_words(data), h), target1, target2);
}

///  Transfer h-witness with lex rank between equivalent targets.
proof fn lemma_h_witness_rank_transfer(
    data: AmalgamatedData, target1: Word, target2: Word, l: nat, r: nat,
)
    requires
        has_left_h_witness_of_len_rank(data, target1, l, r),
        equiv_in_presentation(data.p1, target1, target2),
        presentation_valid(data.p1),
    ensures
        has_left_h_witness_of_len_rank(data, target2, l, r),
{
    let h: Word = choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && word_lex_rank_base(h, h_lex_base(data)) == r
        && equiv_in_presentation(data.p1, apply_embedding(a_words(data), h), target1);
    crate::presentation::lemma_equiv_transitive(
        data.p1, apply_embedding(a_words(data), h), target1, target2);
}

///  If no_smaller_h_lex(target, l, m) and has_h_witness_rank(target, l, k), then k >= m.
proof fn lemma_no_smaller_h_lex_implies_ge(
    data: AmalgamatedData, target: Word, l: nat, m: nat, k: nat,
)
    requires
        no_smaller_h_lex(data, target, l, m),
        has_left_h_witness_of_len_rank(data, target, l, k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {
    } else if k == m - 1 {
        //  no_smaller_h_lex says !has_rank(k) but we have has_rank(k) → contradiction
    } else if k < m - 1 {
        lemma_no_smaller_h_lex_implies_ge(data, target, l, (m - 1) as nat, k);
    }
}

///  If g1 ≡ g2 in G₁, then same_left_coset(g1, g2).
///  Proof: inv(g1) · g2 ≡ inv(g1) · g1 ≡ ε, and ε is in the subgroup.
proof fn lemma_same_left_coset_from_equiv(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
    ensures
        same_left_coset(data, g1, g2),
{
    //  inv(g1) · g2 ≡ inv(g1) · g1 ≡ ε
    crate::presentation::lemma_equiv_symmetric(data.p1, g1, g2);
    crate::presentation_lemmas::lemma_equiv_concat_right(
        data.p1, inverse_word(g1), g2, g1);
    crate::presentation_lemmas::lemma_word_inverse_left(data.p1, g1);
    crate::presentation::lemma_equiv_transitive(data.p1,
        concat(inverse_word(g1), g2), concat(inverse_word(g1), g1), empty_word());

    //  ε is in the subgroup (empty factors)
    let empty_factors = Seq::<Word>::empty();
    assert(crate::benign::factors_from_generators(a_words(data), empty_factors));
    assert(crate::benign::concat_all(empty_factors) =~= empty_word());
    crate::presentation::lemma_equiv_refl(data.p1, empty_word());
    //  equiv(ε, inv(g1) · g2) by symmetry
    crate::word::lemma_inverse_word_valid(g1, data.p1.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(g1), g2, data.p1.num_generators);
    crate::presentation::lemma_equiv_symmetric(data.p1,
        concat(inverse_word(g1), g2), empty_word());
    assert(in_generated_subgroup(data.p1, a_words(data), empty_word()));
    lemma_in_subgroup_equiv(data.p1, a_words(data),
        empty_word(), concat(inverse_word(g1), g2));
}

///  Helper: derive target1 ≡ target2 from g1 ≡ g2 (using coset rep invariance).
proof fn lemma_targets_equiv(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
    ensures ({
        let target1 = concat(inverse_word(left_canonical_rep(data, g1)), g1);
        let target2 = concat(inverse_word(left_canonical_rep(data, g2)), g2);
        equiv_in_presentation(data.p1, target1, target2)
    }),
{
    let rep1 = left_canonical_rep(data, g1);
    let rep2 = left_canonical_rep(data, g2);
    //  rep1 =~= rep2 by coset invariance
    lemma_left_rep_props(data, g1);
    lemma_left_rep_props(data, g2);
    lemma_same_left_coset_from_equiv(data, g1, g2);
    lemma_left_rep_coset_invariant(data, g1, g2);
    //  rep1 =~= rep2, so inverse_word(rep1) =~= inverse_word(rep2)
    //  equiv(inv(rep1), inv(rep2)) by refl (same word)
    crate::presentation::lemma_equiv_refl(data.p1, inverse_word(rep1));
    //  target1 ≡ target2 by equiv_concat
    crate::presentation_lemmas::lemma_equiv_concat(
        data.p1, inverse_word(rep1), inverse_word(rep2), g1, g2);
}

///  Min h-length is invariant under G₁-equivalence of the input word.
///  If g1 ≡ g2 in G₁, then left_h_min_len(g1) == left_h_min_len(g2).
proof fn lemma_left_h_min_len_equiv_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness1),
            concat(inverse_word(left_canonical_rep(data, g1)), g1)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness2),
            concat(inverse_word(left_canonical_rep(data, g2)), g2)),
    ensures
        left_h_min_len(data, g1) == left_h_min_len(data, g2),
{
    let target1 = concat(inverse_word(left_canonical_rep(data, g1)), g1);
    let target2 = concat(inverse_word(left_canonical_rep(data, g2)), g2);

    //  target1 ≡ target2
    lemma_targets_equiv(data, g1, g2);

    //  Establish satisfiability for both sides
    assert(has_left_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_left_h_witness_of_len(data, target2, h_witness2.len() as nat));
    let pred1 = |l: nat| has_left_h_witness_of_len(data, target1, l);
    let pred2 = |l: nat| has_left_h_witness_of_len(data, target2, l);
    assert(pred1(h_witness1.len() as nat));
    assert(pred2(h_witness2.len() as nat));
    lemma_nat_well_ordering(pred1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred2, h_witness2.len() as nat);

    let l1 = left_h_min_len(data, g1);
    let l2 = left_h_min_len(data, g2);

    //  Transfer: has_witness(target1, l1) → has_witness(target2, l1)
    lemma_h_witness_transfer(data, target1, target2, l1);
    //  Transfer: has_witness(target2, l2) → has_witness(target1, l2)
    lemma_left_rep_props(data, g1);
    crate::word::lemma_inverse_word_valid(left_canonical_rep(data, g1), data.p1.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(left_canonical_rep(data, g1)), g1, data.p1.num_generators);
    crate::presentation::lemma_equiv_symmetric(data.p1, target1, target2);
    lemma_h_witness_transfer(data, target2, target1, l2);

    //  Bidirectional ≥
    lemma_no_pred_below_implies_ge(pred2, l2, l1);
    lemma_no_pred_below_implies_ge(pred1, l1, l2);
}

///  Min h-lex rank is invariant under G₁-equivalence.
proof fn lemma_left_h_min_lex_equiv_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness1),
            concat(inverse_word(left_canonical_rep(data, g1)), g1)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness2),
            concat(inverse_word(left_canonical_rep(data, g2)), g2)),
    ensures
        left_h_min_lex(data, g1) == left_h_min_lex(data, g2),
{
    let target1 = concat(inverse_word(left_canonical_rep(data, g1)), g1);
    let target2 = concat(inverse_word(left_canonical_rep(data, g2)), g2);

    //  target1 ≡ target2
    lemma_targets_equiv(data, g1, g2);

    //  l1 == l2
    lemma_left_h_min_len_equiv_invariant(data, g1, g2, h_witness1, h_witness2);
    let l = left_h_min_len(data, g1);

    //  Establish lex satisfiability for both
    lemma_left_h_min_lex_satisfiable(data, g1, h_witness1);
    lemma_left_h_min_lex_satisfiable(data, g2, h_witness2);

    let r1 = left_h_min_lex(data, g1);
    let r2 = left_h_min_lex(data, g2);

    //  Transfer: has_rank(target1, l, r1) → has_rank(target2, l, r1)
    assert(is_min_h_lex(data, target1, l, r1));
    assert(is_min_h_lex(data, target2, l, r2));
    lemma_h_witness_rank_transfer(data, target1, target2, l, r1);
    lemma_left_rep_props(data, g1);
    crate::word::lemma_inverse_word_valid(left_canonical_rep(data, g1), data.p1.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(left_canonical_rep(data, g1)), g1, data.p1.num_generators);
    crate::presentation::lemma_equiv_symmetric(data.p1, target1, target2);
    lemma_h_witness_rank_transfer(data, target2, target1, l, r2);

    //  Bidirectional ≥
    assert(no_smaller_h_lex(data, target1, l, r1));
    assert(no_smaller_h_lex(data, target2, l, r2));
    lemma_no_smaller_h_lex_implies_ge(data, target2, l, r2, r1);
    lemma_no_smaller_h_lex_implies_ge(data, target1, l, r1, r2);
}

///  Extract all four choose properties from left_h_part.
proof fn lemma_left_h_part_full_props(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(inverse_word(left_canonical_rep(data, g)), g)),
    ensures ({
        let rep = left_canonical_rep(data, g);
        let h = left_h_part(data, g);
        let target = concat(inverse_word(rep), g);
        &&& word_valid(h, k_size(data))
        &&& h.len() == left_h_min_len(data, g)
        &&& word_lex_rank_base(h, h_lex_base(data)) == left_h_min_lex(data, g)
        &&& equiv_in_presentation(data.p1,
                apply_embedding(a_words(data), h), target)
    }),
{
    lemma_left_h_part_props(data, g, h_witness);
    lemma_left_h_min_lex_satisfiable(data, g, h_witness);
}

///  H-part is invariant under G₁-equivalence:
///  if g1 ≡ g2 in G₁, then left_h_part(g1) =~= left_h_part(g2).
pub proof fn lemma_left_h_part_equiv_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness1),
            concat(inverse_word(left_canonical_rep(data, g1)), g1)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness2),
            concat(inverse_word(left_canonical_rep(data, g2)), g2)),
    ensures
        left_h_part(data, g1) =~= left_h_part(data, g2),
{
    //  min len and min lex are both invariant
    lemma_left_h_min_len_equiv_invariant(data, g1, g2, h_witness1, h_witness2);
    lemma_left_h_min_lex_equiv_invariant(data, g1, g2, h_witness1, h_witness2);
    let l = left_h_min_len(data, g1);
    let r = left_h_min_lex(data, g1);

    //  Both h-parts satisfy: len == l, lex_rank == r
    lemma_left_h_part_full_props(data, g1, h_witness1);
    lemma_left_h_part_full_props(data, g2, h_witness2);
    let h1 = left_h_part(data, g1);
    let h2 = left_h_part(data, g2);

    //  By lex rank injectivity on K-words
    let base = h_lex_base(data);
    assert forall|k: int| 0 <= k < h1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] h1[k]) < base
    by {
        assert(symbol_valid(h1[k], k_size(data)));
        match h1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert forall|k: int| 0 <= k < h2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] h2[k]) < base
    by {
        assert(symbol_valid(h2[k], k_size(data)));
        match h2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert(base > 0) by { assert(h_lex_base(data) == 2 * k_size(data) + 1); }
    lemma_word_lex_rank_base_injective(h1, h2, base);
}

//  ============================================================
//  Part M: General inverse pair triviality for G₁ symbols
//  ============================================================

///  Helper: [inv(s)] · embed_a(left_h_part([s]·embed_a(h))) ≡ embed_a(h)
///  when left_canonical_rep([s]·embed_a(h)) = ε (product in subgroup).
///  [inv(s)] · embed_a(a_rcoset_h(product)) ≡ embed_a(h)
///  when a_rcoset_rep(product) = ε (product in subgroup, right-coset convention).
proof fn lemma_inv_s_h_prime_equiv_embed_h(
    data: AmalgamatedData, s: Symbol, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        generator_index(s) < data.p1.num_generators,
        a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word(),
    ensures ({
        let embed_h = apply_embedding(a_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let h_prime = a_rcoset_h(data, product);
        let embed_h_prime = apply_embedding(a_words(data), h_prime);
        let product2 = concat(Seq::new(1, |_i: int| inverse_symbol(s)), embed_h_prime);
        equiv_in_presentation(data.p1, product2, embed_h)
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    reveal(presentation_valid);

    //  word_valid setup
    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);

    //  Right-coset h-part: embed_a(h') ≡ product · inv(rep) = product (since rep = ε)
    //  target = concat(product, inv(ε)) =~= product
    assert(concat(product, inverse_word(e)) =~= product) by {
        assert(inverse_word(e).len() == 0);
        assert(concat(product, inverse_word(e)).len() == product.len());
        assert forall|k: int| 0 <= k < product.len()
            implies concat(product, inverse_word(e))[k] == product[k] by {}
    }
    //  product ∈ A (from a_rcoset_rep = ε): derive in_left_subgroup
    lemma_a_rcoset_rep_props(data, product);
    //  same_a_rcoset(product, ε) → in_left_subgroup(concat(product, inv(ε)))
    crate::presentation::lemma_equiv_refl(p1, product);
    lemma_in_subgroup_equiv(p1, a_words(data),
        concat(product, inverse_word(a_rcoset_rep(data, product))),
        product);
    //  in_left_subgroup(product) established

    //  Both reps = ε
    lemma_in_subgroup_both_reps_eps(data, product);
    //  left_canonical_rep(product) =~= ε, a_rcoset_rep(product) =~= ε
    //  So left target = inv(ε)·product =~= product =~= product·inv(ε) = right target

    //  Get h-witness from left-coset infrastructure
    lemma_h_witness_exists(data, product);
    let hw: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, product)), product));
    //  hw satisfies equiv(embed_a(hw), left_target). left_target =~= product =~= right_target.
    //  So hw also witnesses for right target.
    lemma_a_rcoset_h_satisfiable(data, product, hw);
    let h_prime = a_rcoset_h(data, product);
    let embed_h_prime = apply_embedding(a_words(data), h_prime);

    //  embed_a(h') ≡ product (since target = concat(product, inv(ε)) =~= product)
    //  product2 = [inv(s)] · embed_a(h') ≡ [inv(s)] · product = [inv(s)]·[s]·embed_a(h)
    crate::presentation_lemmas::lemma_equiv_concat_right(p1, inv_s_word, embed_h_prime, product);

    //  [inv(s)]·[s] ≡ ε (free reduction)
    assert(inverse_word(s_word) =~= inv_s_word) by {
        assert(s_word.first() == s);
        assert(s_word.drop_first().len() == 0);
        assert(inverse_word(s_word.drop_first()) =~= e);
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p1, s_word);

    //  Associativity + cancellation
    assert(concat(inv_s_word, concat(s_word, embed_h)) =~=
           concat(concat(inv_s_word, s_word), embed_h)) by {
        let lhs = concat(inv_s_word, concat(s_word, embed_h));
        let rhs = concat(concat(inv_s_word, s_word), embed_h);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < 1 {} else { if k < 2 {} else {} }
        }
    }
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, concat(inv_s_word, s_word), e, embed_h);
    assert(concat(e, embed_h) =~= embed_h) by {
        assert(concat(e, embed_h).len() == embed_h.len());
        assert forall|k: int| 0 <= k < embed_h.len() implies concat(e, embed_h)[k] == embed_h[k] by {}
    }
    assert(concat(inv_s_word, product) =~= concat(concat(inv_s_word, s_word), embed_h));

    crate::presentation::lemma_equiv_transitive(p1,
        concat(inv_s_word, embed_h_prime),
        concat(concat(inv_s_word, s_word), embed_h),
        embed_h);
    return;
}

///  Helper: embed_a(h) is in the trivial left coset (canonical rep = ε).
proof fn lemma_embed_in_trivial_coset(data: AmalgamatedData, h: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
    ensures
        same_left_coset(data, apply_embedding(a_words(data), h), empty_word()),
        left_canonical_rep(data, apply_embedding(a_words(data), h)) =~= empty_word(),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let embed_h = apply_embedding(a_words(data), h);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::word::lemma_inverse_word_valid(embed_h, n1);

    //  embed_a(h) ∈ subgroup → inv(embed_a(h)) ∈ subgroup
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    lemma_subgroup_inverse(p1, a_words(data), embed_h);

    //  same_left_coset(embed_h, ε) = in_left_subgroup(concat(inv(embed_h), ε))
    //  concat(inv(embed_h), ε) =~= inv(embed_h), which is in subgroup
    assert(concat(inverse_word(embed_h), e) =~= inverse_word(embed_h)) by {
        assert(concat(inverse_word(embed_h), e).len() == inverse_word(embed_h).len());
        assert forall|k: int| 0 <= k < inverse_word(embed_h).len()
            implies concat(inverse_word(embed_h), e)[k] == inverse_word(embed_h)[k] by {}
    }
    crate::presentation::lemma_equiv_refl(p1, inverse_word(embed_h));
    lemma_in_subgroup_equiv(p1, a_words(data),
        inverse_word(embed_h), concat(inverse_word(embed_h), e));

    //  left_canonical_rep(embed_h) =~= left_canonical_rep(ε) =~= ε
    lemma_left_rep_identity(data);
    lemma_left_rep_props(data, embed_h);
    lemma_left_rep_coset_invariant(data, embed_h, e);
    return;
}

///  Helper: when product2 ≡ embed_a(h) and both are in the subgroup,
///  a_rcoset_rep(product2) =~= ε and a_rcoset_h(product2) =~= h (for canonical h).
proof fn lemma_subgroup_rcoset_restore(
    data: AmalgamatedData, product2: Word, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        word_valid(product2, data.p1.num_generators),
        equiv_in_presentation(data.p1, product2, apply_embedding(a_words(data), h)),
        is_canonical_state(data, h, Seq::<Syllable>::empty()),
    ensures
        a_rcoset_rep(data, product2) =~= empty_word(),
        a_rcoset_h(data, product2) =~= h,
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let embed_h = apply_embedding(a_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  embed_h in subgroup. product2 ≡ embed_h → product2 in subgroup
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    crate::presentation::lemma_equiv_symmetric(p1, product2, embed_h);
    lemma_in_subgroup_equiv(p1, a_words(data), embed_h, product2);

    //  product2 in subgroup → both reps = ε
    lemma_in_subgroup_both_reps_eps(data, product2);
    lemma_in_subgroup_both_reps_eps(data, embed_h);

    //  left_h_part invariance: product2 ≡ embed_h, both left reps = ε
    //  → left_h_part(product2) =~= left_h_part(embed_h)
    lemma_h_witness_exists(data, product2);
    lemma_h_witness_exists(data, embed_h);
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, product2)), product2));
    let hw_eh: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, embed_h)), embed_h));
    lemma_left_h_part_equiv_invariant(data, product2, embed_h, hw2, hw_eh);
    //  left_h_part(product2) =~= left_h_part(embed_h) =~= h (by is_canonical_state)
    //  Since both reps = ε: a_rcoset_h = left_h_part (same target)
}

///  Subcase A: G₁ inverse pair when product = [s]·embed_a(h) is in the subgroup (rep = ε).
proof fn lemma_inverse_pair_g1_subcase_a(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p1.num_generators,
        a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word(),
    ensures
        act_word(data, inverse_pair_word(s), h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

    //  Split [s, inv(s)] into [s] ++ [inv(s)]
    assert(inverse_pair_word(s) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s, h, syls);
    let h_prime = a_rcoset_h(data, product);
    lemma_act_word_single(data, inv_s, h_prime, syls);

    //  product2 ≡ embed_a(h) (from helper — uses right-coset convention)
    lemma_inv_s_h_prime_equiv_embed_h(data, s, h);
    let embed_h_prime = apply_embedding(a_words(data), h_prime);
    let product2 = concat(inv_s_word, embed_h_prime);

    //  product2 word_valid + in subgroup → reps = ε, h-part = h
    assert(word_valid(inv_s_word, n1)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);
    //  h_prime word_valid from rcoset_h_satisfiable
    lemma_a_rcoset_rep_props(data, product);
    crate::presentation::lemma_equiv_refl(p1, product);
    lemma_in_subgroup_equiv(p1, a_words(data),
        concat(product, inverse_word(a_rcoset_rep(data, product))), product);
    lemma_in_subgroup_both_reps_eps(data, product);
    lemma_h_witness_exists(data, product);
    let hw_p: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, product)), product));
    lemma_a_rcoset_h_satisfiable(data, product, hw_p);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_h_prime, n1);

    //  Use helper for the restore
    lemma_subgroup_rcoset_restore(data, product2, h);
}

///  Right-coset decomposition identity: embed_a(a_rcoset_h(g)) · a_rcoset_rep(g) ≡ g.
///  This is the textbook identity g = h·c at the word level.
proof fn lemma_rcoset_decomposition(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p1,
            apply_embedding(a_words(data), h_witness),
            concat(g, inverse_word(a_rcoset_rep(data, g)))),
    ensures
        equiv_in_presentation(data.p1,
            concat(apply_embedding(a_words(data), a_rcoset_h(data, g)),
                   a_rcoset_rep(data, g)),
            g),
        word_valid(a_rcoset_h(data, g), k_size(data)),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let rep = a_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    let h = a_rcoset_h(data, g);
    let embed_h = apply_embedding(a_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }

    //  embed_a(h) ≡ target = g·inv(rep) from h-part satisfiability
    lemma_a_rcoset_h_satisfiable(data, g, h_witness);

    //  concat(embed_a(h), rep) ≡ concat(g·inv(rep), rep) [by equiv_concat_left]
    lemma_a_rcoset_rep_props(data, g);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, embed_h, target, rep);

    //  concat(g·inv(rep), rep) =~= concat(g, concat(inv(rep), rep)) [associativity]
    crate::word::lemma_inverse_word_valid(rep, n1);
    assert(concat(concat(g, inverse_word(rep)), rep) =~=
           concat(g, concat(inverse_word(rep), rep))) by {
        let lhs = concat(concat(g, inverse_word(rep)), rep);
        let rhs = concat(g, concat(inverse_word(rep), rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < g.len() as int {} else {
                let j = k - g.len() as int;
                if j < inverse_word(rep).len() as int {} else {}
            }
        }
    }

    //  concat(inv(rep), rep) ≡ ε [word_inverse_left]
    crate::presentation_lemmas::lemma_word_inverse_left(p1, rep);

    //  concat(g, concat(inv(rep), rep)) ≡ concat(g, ε) [equiv_concat_right]
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p1, g, concat(inverse_word(rep), rep), empty_word());

    //  concat(g, ε) =~= g
    assert(concat(g, empty_word()) =~= g) by {
        assert(concat(g, empty_word()).len() == g.len());
        assert forall|k: int| 0 <= k < g.len()
            implies concat(g, empty_word())[k] == g[k] by {}
    }

    //  Chain: concat(embed_h, rep) ≡ concat(target, rep) =~= concat(g, concat(inv(rep), rep))
    //         ≡ concat(g, ε) =~= g
    crate::presentation::lemma_equiv_transitive(p1,
        concat(embed_h, rep),
        concat(g, concat(inverse_word(rep), rep)),
        g);
    return;
}

///  General helper: [inv(s)] · embed_a(a_rcoset_h(product)) · a_rcoset_rep(product) ≡ embed_a(h)
///  where product = [s]·embed_a(h). Works for all subcases (rep = ε or rep ≠ ε).
proof fn lemma_inv_s_rcoset_product_equiv(
    data: AmalgamatedData, s: Symbol, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        generator_index(s) < data.p1.num_generators,
    ensures ({
        let embed_h = apply_embedding(a_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let h_prime = a_rcoset_h(data, product);
        let embed_h_prime = apply_embedding(a_words(data), h_prime);
        let rep_prime = a_rcoset_rep(data, product);
        let full = concat(concat(Seq::new(1, |_i: int| inverse_symbol(s)), embed_h_prime), rep_prime);
        &&& equiv_in_presentation(data.p1, full, embed_h)
        &&& word_valid(h_prime, k_size(data))
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    let rep_prime = a_rcoset_rep(data, product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);

    //  h-witness from subgroup structure
    lemma_a_rcoset_rep_props(data, product);
    crate::word::lemma_inverse_word_valid(rep_prime, n1);
    crate::word::lemma_concat_word_valid(product, inverse_word(rep_prime), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(product, inverse_word(rep_prime)));
    let hw_r: Word = choose|hw: Word| word_valid(hw, a_words(data).len())
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(product, inverse_word(rep_prime)));
    assert(a_words(data).len() == k_size(data));

    //  embed_a(h') · rep' ≡ product
    lemma_rcoset_decomposition(data, product, hw_r);
    let h_prime = a_rcoset_h(data, product);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    let embed_h_prime = apply_embedding(a_words(data), h_prime);

    //  [inv(s)] · (embed_a(h')·rep') ≡ [inv(s)] · product
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p1, inv_s_word, concat(embed_h_prime, rep_prime), product);

    //  Associativity: [inv(s)]·embed_h'·rep' =~= [inv(s)]·(embed_h'·rep')
    let full = concat(concat(inv_s_word, embed_h_prime), rep_prime);
    assert(full =~= concat(inv_s_word, concat(embed_h_prime, rep_prime))) by {
        let lhs = full;
        let rhs = concat(inv_s_word, concat(embed_h_prime, rep_prime));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inv_s_word.len() as int {} else {
                let j = k - inv_s_word.len() as int;
                if j < embed_h_prime.len() as int {} else {}
            }
        }
    }

    //  [inv(s)]·product = [inv(s)]·[s]·embed_h → free reduction → embed_h
    assert(inverse_word(s_word) =~= inv_s_word) by {
        assert(s_word.first() == s);
        assert(s_word.drop_first().len() == 0);
        assert(inverse_word(s_word.drop_first()) =~= e);
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p1, s_word);
    assert(concat(inv_s_word, concat(s_word, embed_h)) =~=
           concat(concat(inv_s_word, s_word), embed_h)) by {
        let lhs = concat(inv_s_word, concat(s_word, embed_h));
        let rhs = concat(concat(inv_s_word, s_word), embed_h);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < 1 {} else { if k < 2 {} else {} }
        }
    }
    crate::presentation_lemmas::lemma_equiv_concat_left(
        p1, concat(inv_s_word, s_word), e, embed_h);
    assert(concat(e, embed_h) =~= embed_h) by {
        assert(concat(e, embed_h).len() == embed_h.len());
        assert forall|k: int| 0 <= k < embed_h.len()
            implies concat(e, embed_h)[k] == embed_h[k] by {}
    }
    assert(concat(inv_s_word, product) =~= concat(concat(inv_s_word, s_word), embed_h));

    //  Chain: full =~= [inv(s)]·(embed_h'·rep') ≡ [inv(s)]·product
    //         =~= ([inv(s)]·[s])·embed_h ≡ ε·embed_h =~= embed_h
    crate::presentation::lemma_equiv_transitive(p1,
        concat(inv_s_word, concat(embed_h_prime, rep_prime)),
        concat(concat(inv_s_word, s_word), embed_h),
        embed_h);
    return;
}

///  Helper for subcase B: the merge step.
///  Given that act_word([s, inv(s)], h, syls) unfolds to
///  act_sym(inv(s), h', [Syl(left, rep')] + syls) where the merge gives (h, syls).
proof fn lemma_inverse_pair_g1_subcase_b_merge(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p1.num_generators,
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
        let h_prime = a_rcoset_h(data, product);
        let rep_prime = a_rcoset_rep(data, product);
        let embed_h_prime = apply_embedding(a_words(data), h_prime);
        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        let full_product2 = concat(concat(inv_s_word, embed_h_prime), rep_prime);
        &&& a_rcoset_rep(data, full_product2) =~= empty_word()
        &&& a_rcoset_h(data, full_product2) =~= h
        &&& word_valid(h_prime, k_size(data))
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let rep_prime = a_rcoset_rep(data, product);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    let s_word = Seq::new(1, |_i: int| s);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);

    //  General helper gives: [inv(s)]·embed_a(h')·rep' ≡ embed_a(h) + word_valid(h')
    lemma_inv_s_rcoset_product_equiv(data, s, h);

    let h_prime = a_rcoset_h(data, product);
    let embed_h_prime = apply_embedding(a_words(data), h_prime);
    let full_product2 = concat(concat(inv_s_word, embed_h_prime), rep_prime);

    assert(word_valid(inv_s_word, n1)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n1) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_h_prime, n1);
    lemma_a_rcoset_rep_props(data, product);
    crate::word::lemma_concat_word_valid(concat(inv_s_word, embed_h_prime), rep_prime, n1);
    lemma_subgroup_rcoset_restore(data, full_product2, h);
}

///  Subgroup left cancellation: if x ∈ A and concat(x, y) ∈ A, then y ∈ A.
proof fn lemma_subgroup_left_cancel(
    p: Presentation, gens: Seq<Word>, x: Word, y: Word,
)
    requires
        presentation_valid(p),
        word_valid(x, p.num_generators),
        word_valid(y, p.num_generators),
        in_generated_subgroup(p, gens, x),
        in_generated_subgroup(p, gens, concat(x, y)),
        forall|i: int| 0 <= i < gens.len() ==> word_valid(#[trigger] gens[i], p.num_generators),
    ensures
        in_generated_subgroup(p, gens, y),
{
    //  inv(x) ∈ A, concat(x,y) ∈ A → concat(inv(x), concat(x,y)) ∈ A
    crate::word::lemma_inverse_word_valid(x, p.num_generators);
    lemma_subgroup_inverse(p, gens, x);
    crate::word::lemma_concat_word_valid(x, y, p.num_generators);
    lemma_subgroup_concat(p, gens, inverse_word(x), concat(x, y));
    //  concat(inv(x), concat(x,y)) ≡ y
    crate::presentation_lemmas::lemma_word_inverse_left(p, x);
    crate::presentation_lemmas::lemma_equiv_concat_left(p, concat(inverse_word(x), x), empty_word(), y);
    assert(concat(inverse_word(x), concat(x, y)) =~=
           concat(concat(inverse_word(x), x), y)) by {
        let lhs = concat(inverse_word(x), concat(x, y));
        let rhs = concat(concat(inverse_word(x), x), y);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inverse_word(x).len() as int {} else {
                let j = k - inverse_word(x).len() as int;
                if j < x.len() as int {} else {}
            }
        }
    }
    assert(concat(empty_word(), y) =~= y) by {
        assert(concat(empty_word(), y).len() == y.len());
        assert forall|k: int| 0 <= k < y.len()
            implies concat(empty_word(), y)[k] == y[k] by {}
    }
    lemma_in_subgroup_equiv(p, gens,
        concat(inverse_word(x), concat(x, y)), y);
}

///  The inverse step's product is NOT in the subgroup when rep' ≠ ε.
///  Proof by contradiction: if product_inv ∈ A, then inv(rep') ∈ A → rep' ∈ A → product ∈ A → rep' = ε.
proof fn lemma_inv_step_rep_nonzero(
    data: AmalgamatedData, s: Symbol, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        generator_index(s) < data.p1.num_generators,
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
        let h_prime = a_rcoset_h(data, product);
        let product_inv = concat(Seq::new(1, |_i: int| inverse_symbol(s)),
            apply_embedding(a_words(data), h_prime));
        !(a_rcoset_rep(data, product_inv) =~= empty_word())
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let rep_prime = a_rcoset_rep(data, product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }

    //  Get h_prime and product_inv
    lemma_inv_s_rcoset_product_equiv(data, s, h);
    let h_prime = a_rcoset_h(data, product);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h_prime, n1);
    let embed_h_prime = apply_embedding(a_words(data), h_prime);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let product_inv = concat(inv_s_word, embed_h_prime);

    //  Proof by contradiction: assume a_rcoset_rep(product_inv) =~= ε
    //  Then product_inv ∈ A. We'll show this implies rep' =~= ε, contradiction.
    if a_rcoset_rep(data, product_inv) =~= empty_word() {
        //  product_inv ∈ A
        assert(word_valid(inv_s_word, n1)) by {
            assert forall|k: int| 0 <= k < inv_s_word.len()
                implies symbol_valid(#[trigger] inv_s_word[k], n1) by {
                    match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
                }
        }
        crate::word::lemma_concat_word_valid(inv_s_word, embed_h_prime, n1);
        crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);

        lemma_a_rcoset_rep_props(data, product_inv);
        crate::presentation::lemma_equiv_refl(p1, product_inv);
        lemma_in_subgroup_equiv(p1, a_words(data),
            concat(product_inv, inverse_word(a_rcoset_rep(data, product_inv))), product_inv);
        //  product_inv ∈ A

        //  embed_a(h') · rep' ≡ product (from rcoset decomposition)
        lemma_a_rcoset_rep_props(data, product);
        crate::word::lemma_inverse_word_valid(rep_prime, n1);
        crate::word::lemma_concat_word_valid(product, inverse_word(rep_prime), n1);
        lemma_subgroup_to_k_word(p1, a_words(data), concat(product, inverse_word(rep_prime)));
        let hw_r: Word = choose|hw: Word| word_valid(hw, a_words(data).len())
            && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
                concat(product, inverse_word(rep_prime)));
        assert(a_words(data).len() == k_size(data));
        lemma_rcoset_decomposition(data, product, hw_r);
        //  concat(embed_a(h'), rep') ≡ product

        //  [inv(s)] · embed_a(h') · rep' ≡ embed_a(h) (from general helper)
        //  Already have: concat(concat(inv_s_word, embed_h_prime), rep_prime) ≡ embed_a(h)
        let full = concat(concat(inv_s_word, embed_h_prime), rep_prime);
        //  full ≡ embed_a(h) ∈ A → full ∈ A
        lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
        crate::word::lemma_concat_word_valid(concat(inv_s_word, embed_h_prime), rep_prime, n1);
        crate::presentation::lemma_equiv_symmetric(p1, full, embed_h);
        lemma_in_subgroup_equiv(p1, a_words(data), embed_h, full);

        //  full = concat(product_inv, rep_prime). product_inv ∈ A and full ∈ A
        //  → rep_prime ∈ A (by left cancellation)
        lemma_subgroup_left_cancel(p1, a_words(data), product_inv, rep_prime);

        //  rep' ∈ A → product ∈ A:
        //  same_a_rcoset(product, rep') gives product·inv(rep') ∈ A
        //  rep' ∈ A → concat(product·inv(rep'), rep') ∈ A by subgroup_concat
        //  And concat(product·inv(rep'), rep') ≡ product → product ∈ A
        lemma_subgroup_concat(p1, a_words(data),
            concat(product, inverse_word(rep_prime)), rep_prime);

        //  concat(concat(product, inv(rep')), rep') ≡ product (assoc + inv cancellation)
        assert(concat(concat(product, inverse_word(rep_prime)), rep_prime) =~=
               concat(product, concat(inverse_word(rep_prime), rep_prime))) by {
            let lhs = concat(concat(product, inverse_word(rep_prime)), rep_prime);
            let rhs = concat(product, concat(inverse_word(rep_prime), rep_prime));
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                if k < product.len() as int {} else {
                    let j = k - product.len() as int;
                    if j < inverse_word(rep_prime).len() as int {} else {}
                }
            }
        }
        crate::presentation_lemmas::lemma_word_inverse_left(p1, rep_prime);
        crate::presentation_lemmas::lemma_equiv_concat_right(
            p1, product, concat(inverse_word(rep_prime), rep_prime), empty_word());
        assert(concat(product, empty_word()) =~= product) by {
            assert(concat(product, empty_word()).len() == product.len());
            assert forall|k: int| 0 <= k < product.len()
                implies concat(product, empty_word())[k] == product[k] by {}
        }
        let s_word = Seq::new(1, |_i: int| s);
        assert(word_valid(s_word, n1)) by {
            assert forall|k: int| 0 <= k < s_word.len()
                implies symbol_valid(#[trigger] s_word[k], n1) by {
                    match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
                }
        }
        crate::word::lemma_concat_word_valid(s_word, embed_h, n1);
        lemma_in_subgroup_equiv(p1, a_words(data),
            concat(concat(product, inverse_word(rep_prime)), rep_prime), product);
        //  product ∈ A → a_rcoset_rep(product) =~= ε
        lemma_a_rcoset_in_subgroup(data, product);
        //  But rep' = a_rcoset_rep(product) ≠ ε. Contradiction!
    }
}

///  Helper: When the merge case of act_left_sym produces merged_rep = ε,
///  the result is (combined_h, syllables.drop_first()).
///  This is a small focused helper to help Z3 unfold act_left_sym.
proof fn lemma_act_left_sym_merge_absorbed(
    data: AmalgamatedData, s: Symbol, h: Word, syllables: Seq<Syllable>,
)
    requires
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
        syllables.len() > 0,
        syllables.first().is_left,
        a_rcoset_rep(data,
            concat(concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)),
                   syllables.first().rep))
            =~= empty_word(),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
        let full_product = concat(product, syllables.first().rep);
        act_left_sym(data, s, h, syllables)
            == (a_rcoset_h(data, full_product), syllables.drop_first())
    }),
{
    //  Z3 unfolds act_left_sym: rep ≠ ε, first syl left → merge case
    //  merged_rep = ε → (combined_h, syllables.drop_first())
}

///  Subcase B: G₁ inverse pair when rep' ≠ ε and first syllable is not left (prepend).
///  After s: (h', [Syl(left, rep')] + syls). After inv(s): merge absorbs → (h, syls).
proof fn lemma_inverse_pair_g1_subcase_b(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p1.num_generators,
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
        syls.len() == 0 || !syls.first().is_left,
    ensures
        act_word(data, inverse_pair_word(s), h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    let rep_prime = a_rcoset_rep(data, product);
    let h_prime = a_rcoset_h(data, product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);

    //  Split [s, inv(s)] into [s] ++ [inv(s)]
    assert(inverse_pair_word(s) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s, h, syls);
    //  act_word([s], h, syls) = (h', [Syl(left, rep')] + syls) [since rep' ≠ ε, not left first]

    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: true, rep: rep_prime }) + syls;
    lemma_act_word_single(data, inv_s, h_prime, new_syls);

    //  Merge helper gives: a_rcoset_rep(full_product2) = ε, a_rcoset_h(full_product2) = h
    lemma_inverse_pair_g1_subcase_b_merge(data, s, h, syls);

    //  Help Z3 with the unfolding
    let embed_h_prime = apply_embedding(a_words(data), h_prime);
    let product_inv = concat(inv_s_word, embed_h_prime);
    let rep_inv = a_rcoset_rep(data, product_inv);
    assert(new_syls.first().is_left);
    assert(new_syls.first().rep == rep_prime);
    assert(new_syls.drop_first() =~= syls);

    //  Help Z3 see the full_product2 matches the merge product in act_left_sym
    let full_product2 = concat(product_inv, rep_prime);
    assert(full_product2 == concat(concat(inv_s_word, embed_h_prime), rep_prime));

    //  Prove rep_inv ≠ ε (product_inv not in subgroup)
    lemma_inv_step_rep_nonzero(data, s, h);

    //  Use the merge helper to establish act_left_sym result
    assert(generator_index(inv_s) == generator_index(s)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    lemma_act_left_sym_merge_absorbed(data, inv_s, h_prime, new_syls);
    //  act_left_sym(inv_s, h', new_syls) = (a_rcoset_h(full_product2), new_syls.drop_first()) = (h, syls)
}

//  ============================================================
//  Part N: Right A-coset rep invariance (parallel to left coset)
//  ============================================================

///  4-part cancellation: concat(concat(a, inv(b)), concat(b, c)) ≡ concat(a, c).
///  Used for right A-coset transitivity: a·inv(b)·b·c ≡ a·c.
proof fn lemma_four_part_cancel(
    p: Presentation, a: Word, b: Word, c: Word,
)
    requires
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
        word_valid(c, p.num_generators),
    ensures
        equiv_in_presentation(p,
            concat(concat(a, inverse_word(b)), concat(b, c)),
            concat(a, c)),
{
    crate::word::lemma_inverse_word_valid(b, p.num_generators);
    //  inv(b)·b ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_left(p, b);
    //  concat(inv(b), concat(b, c)) =~= concat(concat(inv(b), b), c) [associativity]
    assert(concat(inverse_word(b), concat(b, c)) =~=
           concat(concat(inverse_word(b), b), c)) by {
        let lhs = concat(inverse_word(b), concat(b, c));
        let rhs = concat(concat(inverse_word(b), b), c);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inverse_word(b).len() as int {} else {
                let j = k - inverse_word(b).len() as int;
                if j < b.len() as int {} else {}
            }
        }
    }
    //  concat(concat(inv(b), b), c) ≡ concat(ε, c) =~= c
    crate::presentation_lemmas::lemma_equiv_concat_left(
        p, concat(inverse_word(b), b), empty_word(), c);
    assert(concat(empty_word(), c) =~= c) by {
        assert(concat(empty_word(), c).len() == c.len());
        assert forall|k: int| 0 <= k < c.len()
            implies concat(empty_word(), c)[k] == c[k] by {}
    }
    //  concat(inv(b), concat(b, c)) =~= concat(concat(inv(b), b), c) → equiv by refl
    crate::word::lemma_concat_word_valid(b, c, p.num_generators);
    crate::word::lemma_concat_word_valid(inverse_word(b), concat(b, c), p.num_generators);
    crate::presentation::lemma_equiv_refl(p, concat(inverse_word(b), concat(b, c)));
    //  Now: equiv(lhs, concat(concat(inv(b), b), c)) since lhs =~= rhs
    //  And: concat(concat(inv(b), b), c) ≡ concat(ε, c) from equiv_concat_left
    //  Chain through concat(ε, c) =~= c
    //  concat(a, concat(inv(b), concat(b, c))) ≡ concat(a, c) [equiv_concat_right]
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p, a, concat(inverse_word(b), concat(b, c)), c);
    //  concat(concat(a, inv(b)), concat(b, c)) =~= concat(a, concat(inv(b), concat(b, c))) [associativity]
    assert(concat(concat(a, inverse_word(b)), concat(b, c)) =~=
           concat(a, concat(inverse_word(b), concat(b, c)))) by {
        let lhs = concat(concat(a, inverse_word(b)), concat(b, c));
        let rhs = concat(a, concat(inverse_word(b), concat(b, c)));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < a.len() as int {} else {
                let j = k - a.len() as int;
                if j < inverse_word(b).len() as int {} else {}
            }
        }
    }
}

///  Transfer: same rcoset → coset words transfer.
proof fn lemma_a_rcoset_word_transfer(
    data: AmalgamatedData, g1: Word, g2: Word, l: nat,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        same_a_rcoset(data, g1, g2),
        has_a_rcoset_word_of_len(data, g1, l),
    ensures
        has_a_rcoset_word_of_len(data, g2, l),
{
    //  Extract witness w with same_a_rcoset(g1, w) && w.len() == l
    let n1 = data.p1.num_generators;
    let w: Word = choose|w: Word| word_valid(w, n1)
        && same_a_rcoset(data, g1, w) && w.len() == l;

    //  word_valid setup (needed before subgroup lemmas)
    crate::word::lemma_inverse_word_valid(g1, n1);
    crate::word::lemma_inverse_word_valid(g2, n1);
    crate::word::lemma_inverse_word_valid(w, n1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(g2), n1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(w), n1);
    crate::word::lemma_concat_word_valid(g2, inverse_word(g1), n1);
    crate::word::lemma_concat_word_valid(g2, inverse_word(w), n1);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], data.p1.num_generators)
    by { assert(word_valid(data.identifications[i].0, data.p1.num_generators)); }

    lemma_subgroup_inverse(data.p1, a_words(data), concat(g1, inverse_word(g2)));
    crate::word::lemma_inverse_concat(g1, inverse_word(g2));
    crate::word::lemma_inverse_involution(g2);
    //  inv(concat(g1, inv(g2))) =~= concat(inv(inv(g2)), inv(g1)) =~= concat(g2, inv(g1))
    let inv_pair = inverse_word(concat(g1, inverse_word(g2)));
    assert(inv_pair =~= concat(g2, inverse_word(g1))) by {
        assert(inv_pair =~= concat(inverse_word(inverse_word(g2)), inverse_word(g1)));
        assert(inverse_word(inverse_word(g2)) =~= g2);
        assert forall|k: int| 0 <= k < concat(g2, inverse_word(g1)).len()
            implies inv_pair[k] == concat(g2, inverse_word(g1))[k]
        by {
            if k < g2.len() as int {} else {}
        }
    }
    crate::presentation::lemma_equiv_refl(data.p1, concat(g2, inverse_word(g1)));
    lemma_in_subgroup_equiv(data.p1, a_words(data),
        inv_pair, concat(g2, inverse_word(g1)));

    //  concat(g2·inv(g1), g1·inv(w)) in subgroup (from subgroup_concat above)
    lemma_subgroup_concat(data.p1, a_words(data),
        concat(g2, inverse_word(g1)),
        concat(g1, inverse_word(w)));

    //  Now: concat(g2, inv(g1))·concat(g1, inv(w)) ≡ concat(g2, inv(w))
    //  by associativity + inv(g1)·g1 cancellation
    //  concat(concat(g2, inv(g1)), concat(g1, inv(w)))
    //  =~= concat(g2, concat(inv(g1), concat(g1, inv(w))))
    //  =~= concat(g2, concat(concat(inv(g1), g1), inv(w)))
    //  ≡ concat(g2, concat(ε, inv(w))) =~= concat(g2, inv(w))

    //  concat(g2·inv(g1), g1·inv(w)) ≡ g2·inv(w) by 4-part cancellation
    lemma_four_part_cancel(data.p1, g2, g1, inverse_word(w));
    lemma_in_subgroup_equiv(data.p1, a_words(data),
        concat(concat(g2, inverse_word(g1)), concat(g1, inverse_word(w))),
        concat(g2, inverse_word(w)));
    //  same_a_rcoset(g2, w) → has_a_rcoset_word_of_len(g2, l)
}

///  Transfer with rank: same rcoset → rank witnesses transfer.
proof fn lemma_a_rcoset_word_rank_transfer(
    data: AmalgamatedData, g1: Word, g2: Word, l: nat, r: nat,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        same_a_rcoset(data, g1, g2),
        has_a_rcoset_word_of_len_rank(data, g1, l, r),
    ensures
        has_a_rcoset_word_of_len_rank(data, g2, l, r),
{
    //  Extract the rank witness from g1's coset
    let n1 = data.p1.num_generators;
    let w: Word = choose|w: Word| word_valid(w, n1)
        && same_a_rcoset(data, g1, w) && w.len() == l
        && word_lex_rank_base(w, lex_base(data)) == r;
    //  w is in g1's rcoset → also in g2's rcoset (by transitivity)
    //  same_a_rcoset(g1, w) and same_a_rcoset(g1, g2) → same_a_rcoset(g2, w)
    lemma_same_a_rcoset_symmetric(data, g1, g2);
    //  same_a_rcoset(g2, g1) + same_a_rcoset(g1, w) → same_a_rcoset(g2, w)
    //  Use the transfer infrastructure from lemma_a_rcoset_word_transfer
    //  Actually, we just need: same_a_rcoset(g2, w) = in_left_subgroup(g2·inv(w))
    //  From same_a_rcoset(g2, g1) + same_a_rcoset(g1, w):
    //    g2·inv(g1) ∈ A and g1·inv(w) ∈ A → (g2·inv(g1))·(g1·inv(w)) ∈ A
    //    ≡ g2·inv(w) ∈ A. So same_a_rcoset(g2, w).
    lemma_subgroup_concat(data.p1, a_words(data),
        concat(g2, inverse_word(g1)),
        concat(g1, inverse_word(w)));
    crate::word::lemma_inverse_word_valid(w, n1);
    crate::word::lemma_concat_word_valid(g2, inverse_word(w), n1);
    //  4-part cancellation: concat(g2·inv(g1), g1·inv(w)) ≡ g2·inv(w)
    lemma_four_part_cancel(data.p1, g2, g1, inverse_word(w));
    lemma_in_subgroup_equiv(data.p1, a_words(data),
        concat(concat(g2, inverse_word(g1)), concat(g1, inverse_word(w))),
        concat(g2, inverse_word(w)));
}

///  No shorter → ≥ for right A-cosets.
proof fn lemma_no_shorter_a_rcoset_word_implies_ge(
    data: AmalgamatedData, g: Word, m: nat, k: nat,
)
    requires
        no_shorter_a_rcoset_word(data, g, m),
        has_a_rcoset_word_of_len(data, g, k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {
    } else if k == m - 1 {
    } else if k < m - 1 {
        lemma_no_shorter_a_rcoset_word_implies_ge(data, g, (m - 1) as nat, k);
    }
}

///  same_a_rcoset is symmetric.
proof fn lemma_same_a_rcoset_symmetric(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        same_a_rcoset(data, g1, g2),
    ensures
        same_a_rcoset(data, g2, g1),
{
    let n1 = data.p1.num_generators;
    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::word::lemma_inverse_word_valid(g2, n1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(g2), n1);
    lemma_subgroup_inverse(data.p1, a_words(data), concat(g1, inverse_word(g2)));
    crate::word::lemma_inverse_concat(g1, inverse_word(g2));
    crate::word::lemma_inverse_involution(g2);
    let inv_pair = inverse_word(concat(g1, inverse_word(g2)));
    assert(inv_pair =~= concat(g2, inverse_word(g1))) by {
        assert(inv_pair =~= concat(inverse_word(inverse_word(g2)), inverse_word(g1)));
        assert forall|k: int| 0 <= k < concat(g2, inverse_word(g1)).len()
            implies inv_pair[k] == concat(g2, inverse_word(g1))[k]
        by { if k < g2.len() as int {} else {} }
    }
    crate::word::lemma_inverse_word_valid(g1, n1);
    crate::word::lemma_concat_word_valid(g2, inverse_word(g1), n1);
    crate::presentation::lemma_equiv_refl(data.p1, concat(g2, inverse_word(g1)));
    lemma_in_subgroup_equiv(data.p1, a_words(data),
        inv_pair, concat(g2, inverse_word(g1)));
}

///  Right A-coset rep invariance: same_a_rcoset → same a_rcoset_rep.
proof fn lemma_a_rcoset_rep_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        same_a_rcoset(data, g1, g2),
    ensures
        a_rcoset_rep(data, g1) =~= a_rcoset_rep(data, g2),
{
    let n1 = data.p1.num_generators;
    //  Satisfiability for both
    lemma_a_rcoset_rep_satisfiable(data, g1);
    lemma_a_rcoset_rep_satisfiable(data, g2);
    let l1 = a_rcoset_min_len(data, g1);
    let l2 = a_rcoset_min_len(data, g2);

    //  Transfer in both directions → bidirectional ≥ → equal
    lemma_a_rcoset_word_transfer(data, g1, g2, l1);
    lemma_same_a_rcoset_symmetric(data, g1, g2);
    lemma_a_rcoset_word_transfer(data, g2, g1, l2);

    //  Bidirectional ≥
    lemma_no_shorter_a_rcoset_word_implies_ge(data, g2, l2, l1);
    lemma_no_shorter_a_rcoset_word_implies_ge(data, g1, l1, l2);
    //  l1 == l2
    let l = l1;

    //  Lex rank: same argument
    let w1: Word = choose|w: Word| word_valid(w, n1)
        && same_a_rcoset(data, g1, w) && w.len() == l;
    let wr1 = word_lex_rank_base(w1, lex_base(data));
    assert(has_a_rcoset_word_of_len_rank(data, g1, l, wr1));
    assert(no_smaller_a_rcoset_lex(data, g1, l, 0nat));
    lemma_scan_a_rcoset_lex(data, g1, l, 0, wr1);
    let w2: Word = choose|w: Word| word_valid(w, n1)
        && same_a_rcoset(data, g2, w) && w.len() == l;
    let wr2 = word_lex_rank_base(w2, lex_base(data));
    assert(has_a_rcoset_word_of_len_rank(data, g2, l, wr2));
    assert(no_smaller_a_rcoset_lex(data, g2, l, 0nat));
    lemma_scan_a_rcoset_lex(data, g2, l, 0, wr2);

    let r1 = a_rcoset_min_lex(data, g1);
    let r2 = a_rcoset_min_lex(data, g2);
    //  Transfer rank witnesses via explicit helper
    lemma_a_rcoset_word_rank_transfer(data, g1, g2, l, r1);
    lemma_a_rcoset_word_rank_transfer(data, g2, g1, l, r2);
    lemma_no_smaller_a_rcoset_lex_implies_ge(data, g2, l, r2, r1);
    lemma_no_smaller_a_rcoset_lex_implies_ge(data, g1, l, r1, r2);
    //  r1 == r2

    //  Rep invariance by lex rank injectivity
    lemma_a_rcoset_rep_props(data, g1);
    lemma_a_rcoset_rep_props(data, g2);
    let rep1 = a_rcoset_rep(data, g1);
    let rep2 = a_rcoset_rep(data, g2);
    let base = lex_base(data);
    assert forall|k: int| 0 <= k < rep1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rep1[k]) < base
    by {
        assert(symbol_valid(rep1[k], n1));
        match rep1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert forall|k: int| 0 <= k < rep2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rep2[k]) < base
    by {
        assert(symbol_valid(rep2[k], n1));
        match rep2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert(base > 0) by { assert(lex_base(data) == 2 * data.p1.num_generators + 1); }
    lemma_word_lex_rank_base_injective(rep1, rep2, base);
}

///  No smaller right A-coset lex implies ≥.
proof fn lemma_no_smaller_a_rcoset_lex_implies_ge(
    data: AmalgamatedData, g: Word, l: nat, m: nat, k: nat,
)
    requires
        no_smaller_a_rcoset_lex(data, g, l, m),
        has_a_rcoset_word_of_len_rank(data, g, l, k),
    ensures
        k >= m,
    decreases m,
{
    if m == 0 {
    } else if k == m - 1 {
    } else if k < m - 1 {
        lemma_no_smaller_a_rcoset_lex_implies_ge(data, g, l, (m - 1) as nat, k);
    }
}

//  ============================================================
//  Part O: Inverse pair subcase C (merge with existing left syllable)
//  ============================================================

///  Free reduction: [inv(s)]·[s]·w ≡ w for any word w.
proof fn lemma_inv_s_s_cancel(
    p: Presentation, s: Symbol, w: Word,
)
    requires
        presentation_valid(p),
        word_valid(w, p.num_generators),
        generator_index(s) < p.num_generators,
    ensures
        equiv_in_presentation(p,
            concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                   concat(Seq::new(1, |_i: int| s), w)),
            w),
{
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    assert(inverse_word(s_word) =~= inv_s_word) by {
        assert(s_word.first() == s);
        assert(s_word.drop_first().len() == 0);
        assert(inverse_word(s_word.drop_first()) =~= empty_word());
    }
    //  [inv(s)]·[s] ≡ ε
    crate::presentation_lemmas::lemma_word_inverse_left(p, s_word);
    //  concat(concat(inv_s, s), w) ≡ concat(ε, w) =~= w
    crate::presentation_lemmas::lemma_equiv_concat_left(
        p, concat(inv_s_word, s_word), empty_word(), w);
    assert(concat(empty_word(), w) =~= w) by {
        assert(concat(empty_word(), w).len() == w.len());
        assert forall|k: int| 0 <= k < w.len()
            implies concat(empty_word(), w)[k] == w[k] by {}
    }
    //  Associativity: [inv(s)]·([s]·w) =~= ([inv(s)]·[s])·w
    assert(concat(inv_s_word, concat(s_word, w)) =~=
           concat(concat(inv_s_word, s_word), w)) by {
        let lhs = concat(inv_s_word, concat(s_word, w));
        let rhs = concat(concat(inv_s_word, s_word), w);
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < 1 {} else { if k < 2 {} else {} }
        }
    }
    //  =~= chains are automatic, ≡ needs transitive through concat(ε, w)
    crate::word::lemma_concat_word_valid(inv_s_word, concat(s_word, w), p.num_generators);
    assert(word_valid(s_word, p.num_generators)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], p.num_generators) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, w, p.num_generators);
    crate::word::lemma_inverse_word_valid(s_word, p.num_generators);
    crate::presentation::lemma_equiv_refl(p, concat(inv_s_word, concat(s_word, w)));
    crate::presentation::lemma_equiv_transitive(p,
        concat(inv_s_word, concat(s_word, w)),
        concat(concat(inv_s_word, s_word), w),
        concat(empty_word(), w));
}

///  Key for subcase C: [inv(s)]·embed_a(combined_h)·merged_rep ≡ embed_a(h)·c₁
///  where full_product = [s]·embed_a(h)·c₁ is the merge product.
proof fn lemma_inv_s_rcoset_merge_equiv(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p1.num_generators),
        generator_index(s) < data.p1.num_generators,
    ensures ({
        let n1 = data.p1.num_generators;
        let embed_h = apply_embedding(a_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let full_product = concat(product, c1);
        let combined_h = a_rcoset_h(data, full_product);
        let embed_ch = apply_embedding(a_words(data), combined_h);
        let merged_rep = a_rcoset_rep(data, full_product);
        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        let full = concat(concat(inv_s_word, embed_ch), merged_rep);
        &&& equiv_in_presentation(data.p1, full, concat(embed_h, c1))
        &&& word_valid(combined_h, k_size(data))
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    let full_product = concat(product, c1);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);
    crate::word::lemma_concat_word_valid(product, c1, n1);

    //  Rcoset decomposition of full_product: embed_a(combined_h)·merged_rep ≡ full_product
    lemma_a_rcoset_rep_props(data, full_product);
    let merged_rep = a_rcoset_rep(data, full_product);
    crate::word::lemma_inverse_word_valid(merged_rep, n1);
    crate::word::lemma_concat_word_valid(full_product, inverse_word(merged_rep), n1);
    lemma_subgroup_to_k_word(p1, a_words(data), concat(full_product, inverse_word(merged_rep)));
    let hw: Word = choose|hw: Word| word_valid(hw, a_words(data).len())
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(full_product, inverse_word(merged_rep)));
    assert(a_words(data).len() == k_size(data));
    lemma_rcoset_decomposition(data, full_product, hw);
    let combined_h = a_rcoset_h(data, full_product);
    crate::benign::lemma_apply_embedding_valid(a_words(data), combined_h, n1);
    let embed_ch = apply_embedding(a_words(data), combined_h);

    //  [inv(s)]·(embed_a(ch)·merged_rep) ≡ [inv(s)]·full_product
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p1, inv_s_word, concat(embed_ch, merged_rep), full_product);

    //  [inv(s)]·full_product = [inv(s)]·[s]·embed_a(h)·c1 ≡ embed_a(h)·c1
    //  full_product = concat(product, c1) = concat(concat(s_word, embed_h), c1)
    //  [inv(s)]·concat(concat(s_word, embed_h), c1) =~= [inv(s)]·[s]·concat(embed_h, c1) by associativity
    assert(concat(inv_s_word, concat(concat(s_word, embed_h), c1)) =~=
           concat(inv_s_word, concat(s_word, concat(embed_h, c1)))) by {
        let lhs = concat(inv_s_word, concat(concat(s_word, embed_h), c1));
        let rhs = concat(inv_s_word, concat(s_word, concat(embed_h, c1)));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < 1 {} else {
                let j = k - 1;
                if j < s_word.len() as int {} else {
                    let j2 = j - s_word.len() as int;
                    if j2 < embed_h.len() as int {} else {}
                }
            }
        }
    }
    //  [inv(s)]·[s]·concat(embed_h, c1) ≡ concat(embed_h, c1) by lemma_inv_s_s_cancel
    crate::word::lemma_concat_word_valid(embed_h, c1, n1);
    lemma_inv_s_s_cancel(p1, s, concat(embed_h, c1));

    //  Associativity: [inv(s)]·embed_ch·merged_rep =~= [inv(s)]·(embed_ch·merged_rep)
    let full = concat(concat(inv_s_word, embed_ch), merged_rep);
    assert(full =~= concat(inv_s_word, concat(embed_ch, merged_rep))) by {
        let lhs = full;
        let rhs = concat(inv_s_word, concat(embed_ch, merged_rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inv_s_word.len() as int {} else {
                let j = k - inv_s_word.len() as int;
                if j < embed_ch.len() as int {} else {}
            }
        }
    }

    //  Chain: full =~= [inv(s)]·(embed_ch·merged_rep) ≡ [inv(s)]·full_product
    //         =~= [inv(s)]·[s]·(embed_h·c1) ≡ embed_h·c1
    crate::presentation::lemma_equiv_transitive(p1,
        concat(inv_s_word, concat(embed_ch, merged_rep)),
        concat(inv_s_word, concat(s_word, concat(embed_h, c1))),
        concat(embed_h, c1));
    return;
}

///  Textbook key property: embed_a(h)·c₁ decomposes as (h, c₁) when h is canonical
///  and c₁ is a canonical right A-coset rep (c₁ = a_rcoset_rep(c₁)).
///  Proof: embed_a(h) ∈ A doesn't change the right coset: A·(embed_a(h)·c₁) = A·c₁.
proof fn lemma_rcoset_decompose_subgroup_times_rep(
    data: AmalgamatedData, h: Word, c1: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p1.num_generators),
        //  h is canonical
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        //  c₁ is a canonical right A-coset rep
        a_rcoset_rep(data, c1) =~= c1,
    ensures
        a_rcoset_rep(data, concat(apply_embedding(a_words(data), h), c1)) =~= c1,
        a_rcoset_h(data, concat(apply_embedding(a_words(data), h), c1)) =~= h,
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(embed_h, c1);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::word::lemma_concat_word_valid(embed_h, c1, n1);

    //  same_a_rcoset(product, c1): need product·inv(c1) ∈ A
    //  product·inv(c1) = embed_a(h)·c1·inv(c1) ≡ embed_a(h)
    //  embed_a(h) ∈ A → product·inv(c1) ∈ A
    crate::word::lemma_inverse_word_valid(c1, n1);
    crate::word::lemma_concat_word_valid(product, inverse_word(c1), n1);
    crate::presentation_lemmas::lemma_word_inverse_right(p1, c1);
    //  embed_h · c1 · inv(c1) ≡ embed_h · ε ≡ embed_h
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p1, embed_h, concat(c1, inverse_word(c1)), empty_word());
    assert(concat(embed_h, empty_word()) =~= embed_h) by {
        assert(concat(embed_h, empty_word()).len() == embed_h.len());
        assert forall|k: int| 0 <= k < embed_h.len()
            implies concat(embed_h, empty_word())[k] == embed_h[k] by {}
    }
    //  Associativity: concat(embed_h, concat(c1, inv(c1))) =~= concat(concat(embed_h, c1), inv(c1)) = concat(product, inv(c1))
    assert(concat(embed_h, concat(c1, inverse_word(c1))) =~= concat(product, inverse_word(c1))) by {
        let lhs = concat(embed_h, concat(c1, inverse_word(c1)));
        let rhs = concat(concat(embed_h, c1), inverse_word(c1));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < embed_h.len() as int {} else {
                let j = k - embed_h.len() as int;
                if j < c1.len() as int {} else {}
            }
        }
    }
    //  Chain: product·inv(c1) =~= embed_h·(c1·inv(c1)) ≡ embed_h·ε =~= embed_h
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    crate::presentation::lemma_equiv_symmetric(p1,
        concat(embed_h, concat(c1, inverse_word(c1))), embed_h);
    lemma_in_subgroup_equiv(p1, a_words(data), embed_h, concat(product, inverse_word(c1)));
    //  same_a_rcoset(product, c1) established

    //  Right A-coset rep invariance: a_rcoset_rep(product) =~= a_rcoset_rep(c1) = c1
    lemma_a_rcoset_rep_invariant(data, product, c1);
    //  a_rcoset_rep(product) =~= c1 ✓

    //  H-part: target = product·inv(c1) ≡ embed_a(h)
    //  canonical h-part for target ≡ embed_a(h) is h (by canonicality + h-part invariance)
    //  Need: a_rcoset_h(product) =~= h
    //  a_rcoset_h(product) has target = product·inv(a_rcoset_rep(product)) =~= product·inv(c1) ≡ embed_a(h)
    //  The canonical K-word for embed_a(h) is h (from is_canonical_state precondition)
    //  So a_rcoset_h(product) =~= left_h_part(embed_a(h)) =~= h

    //  Establish: product·inv(c1) ≡ embed_a(h) → product and embed_a(h) are in same subgroup equiv class
    //  Use lemma_in_subgroup_both_reps_eps on embed_a(h) to get left_canonical_rep(embed_a(h)) = ε
    lemma_in_subgroup_both_reps_eps(data, embed_h);

    //  product·inv(c1) ≡ embed_a(h) → left_h_part equiv invariance
    //  Both have left_canonical_rep = ε (since both in subgroup)
    lemma_in_subgroup_both_reps_eps(data, concat(product, inverse_word(c1)));

    //  h-part invariance: left_h_part(product·inv(c1)) =~= left_h_part(embed_a(h)) =~= h
    lemma_h_witness_exists(data, concat(product, inverse_word(c1)));
    lemma_h_witness_exists(data, embed_h);
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, concat(product, inverse_word(c1)))),
                   concat(product, inverse_word(c1))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, embed_h)), embed_h));
    crate::presentation::lemma_equiv_symmetric(p1,
        concat(embed_h, concat(c1, inverse_word(c1))), embed_h);
    lemma_left_h_part_equiv_invariant(data, concat(product, inverse_word(c1)), embed_h, hw1, hw2);
    //  left_h_part(product·inv(c1)) =~= left_h_part(embed_a(h)) =~= h

    //  Since a_rcoset_rep(product) =~= c1 and left reps = ε:
    //  a_rcoset target = product·inv(c1) = left target (when left rep = ε)
    //  So a_rcoset_h(product) = left_h_part(product·inv(c1)) =~= h
}

///  If g1 ≡ g2, then same_a_rcoset(g1, g2).
proof fn lemma_same_a_rcoset_from_equiv(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g1, data.p1.num_generators),
        word_valid(g2, data.p1.num_generators),
        equiv_in_presentation(data.p1, g1, g2),
    ensures
        same_a_rcoset(data, g1, g2),
{
    let p1 = data.p1;
    let n1 = p1.num_generators;
    //  concat(g1, inv(g2)) ≡ concat(g1, inv(g1)) ≡ ε ∈ A
    crate::word::lemma_inverse_word_valid(g1, n1);
    crate::word::lemma_inverse_word_valid(g2, n1);
    crate::presentation::lemma_equiv_symmetric(p1, g1, g2);
    lemma_equiv_inverse(p1, g2, g1);
    crate::presentation::lemma_equiv_refl(p1, g1);
    crate::presentation_lemmas::lemma_equiv_concat(p1,
        g1, g1, inverse_word(g2), inverse_word(g1));
    crate::presentation_lemmas::lemma_word_inverse_right(p1, g1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(g1), n1);
    crate::presentation::lemma_equiv_transitive(p1,
        concat(g1, inverse_word(g2)),
        concat(g1, inverse_word(g1)),
        empty_word());
    crate::benign::lemma_identity_in_generated_subgroup(p1, a_words(data));
    crate::word::lemma_concat_word_valid(g1, inverse_word(g2), n1);
    crate::presentation::lemma_equiv_symmetric(p1, concat(g1, inverse_word(g2)), empty_word());
    lemma_in_subgroup_equiv(p1, a_words(data),
        empty_word(), concat(g1, inverse_word(g2)));
}

///  Helper: When the merge case of act_left_sym produces merged_rep ≠ ε,
///  the result replaces the first syllable.
proof fn lemma_act_left_sym_merge_replaced(
    data: AmalgamatedData, s: Symbol, h: Word, syllables: Seq<Syllable>,
)
    requires
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
        syllables.len() > 0,
        syllables.first().is_left,
        !({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
            let full_product = concat(product, syllables.first().rep);
            a_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
        let full_product = concat(product, syllables.first().rep);
        let merged_rep = a_rcoset_rep(data, full_product);
        act_left_sym(data, s, h, syllables)
            == (a_rcoset_h(data, full_product),
                Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep })
                + syllables.drop_first())
    }),
{
    //  Z3 unfolds act_left_sym: rep ≠ ε, first syl left → merge case
    //  merged_rep ≠ ε → replace first syllable
}

///  H-part through equivalence: if g ≡ embed_a(h)·c where c is canonical rep,
///  then a_rcoset_h(g) =~= h (when h is canonical).
///  Uses: target = g·inv(c) ≡ embed_a(h) → subgroup h-part invariance.
proof fn lemma_a_rcoset_h_from_equiv(
    data: AmalgamatedData, g: Word, h: Word, c: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
        word_valid(h, k_size(data)),
        word_valid(c, data.p1.num_generators),
        equiv_in_presentation(data.p1, g, concat(apply_embedding(a_words(data), h), c)),
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        a_rcoset_rep(data, c) =~= c,
        a_rcoset_rep(data, g) =~= c,
    ensures
        a_rcoset_h(data, g) =~= h,
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let embed_h = apply_embedding(a_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::word::lemma_inverse_word_valid(c, n1);

    //  target_g = g·inv(a_rcoset_rep(g)) = g·inv(c)
    //  target_ehc = (embed_h·c)·inv(c) ≡ embed_h (by word_inverse_right + assoc)
    //  g ≡ embed_h·c → g·inv(c) ≡ (embed_h·c)·inv(c) ≡ embed_h

    //  So target_g ≡ embed_h. Both in subgroup (embed_h ∈ A).
    //  By in_subgroup_both_reps_eps: both left reps = ε.
    //  By left_h_part_equiv_invariant on the targets:
    //  left_h_part(target_g) =~= left_h_part(embed_h) =~= h.
    //  Since a_rcoset_rep(g) =~= c and left_canonical_rep(target_g) = ε:
    //  a_rcoset_h(g) = left_h_part(target_g) (same target, same choose).

    //  target_g ≡ embed_h:
    //  g ≡ embed_h·c → g·inv(c) ≡ (embed_h·c)·inv(c) by concat_left
    crate::word::lemma_concat_word_valid(g, inverse_word(c), n1);
    crate::word::lemma_concat_word_valid(embed_h, c, n1);
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, g, concat(embed_h, c), inverse_word(c));
    //  g·inv(c) ≡ (embed_h·c)·inv(c) by equiv_concat_right
    //  (embed_h·c)·inv(c) ≡ embed_h by four_part_cancel(embed_h, c, ε)... no, by word_inverse_right
    crate::presentation_lemmas::lemma_word_inverse_right(p1, c);
    crate::presentation_lemmas::lemma_equiv_concat_right(p1, embed_h,
        concat(c, inverse_word(c)), empty_word());
    assert(concat(embed_h, empty_word()) =~= embed_h) by {
        assert(concat(embed_h, empty_word()).len() == embed_h.len());
        assert forall|k: int| 0 <= k < embed_h.len()
            implies concat(embed_h, empty_word())[k] == embed_h[k] by {}
    }
    //  (embed_h·c)·inv(c) =~= embed_h·(c·inv(c)) ≡ embed_h·ε =~= embed_h
    assert(concat(concat(embed_h, c), inverse_word(c)) =~=
           concat(embed_h, concat(c, inverse_word(c)))) by {
        let lhs = concat(concat(embed_h, c), inverse_word(c));
        let rhs = concat(embed_h, concat(c, inverse_word(c)));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < embed_h.len() as int {} else {
                let j = k - embed_h.len() as int;
                if j < c.len() as int {} else {}
            }
        }
    }
    crate::word::lemma_concat_word_valid(concat(embed_h, c), inverse_word(c), n1);
    crate::presentation::lemma_equiv_refl(p1, concat(concat(embed_h, c), inverse_word(c)));
    crate::presentation::lemma_equiv_transitive(p1,
        concat(concat(embed_h, c), inverse_word(c)),
        concat(embed_h, concat(c, inverse_word(c))),
        embed_h);
    crate::presentation::lemma_equiv_transitive(p1,
        concat(g, inverse_word(c)), concat(concat(embed_h, c), inverse_word(c)), embed_h);

    //  Both targets ∈ subgroup → both reps = ε → left_h_part invariance applies
    lemma_apply_embedding_in_subgroup(p1, a_words(data), h);
    crate::presentation::lemma_equiv_symmetric(p1, concat(g, inverse_word(c)), embed_h);
    lemma_in_subgroup_equiv(p1, a_words(data), embed_h, concat(g, inverse_word(c)));
    lemma_in_subgroup_both_reps_eps(data, concat(g, inverse_word(c)));
    lemma_in_subgroup_both_reps_eps(data, embed_h);

    //  left_h_part invariance: left_h_part(target_g) =~= left_h_part(embed_h) =~= h
    lemma_h_witness_exists(data, concat(g, inverse_word(c)));
    lemma_h_witness_exists(data, embed_h);
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, concat(g, inverse_word(c)))),
                   concat(g, inverse_word(c))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p1, apply_embedding(a_words(data), hw),
            concat(inverse_word(left_canonical_rep(data, embed_h)), embed_h));
    lemma_left_h_part_equiv_invariant(data, concat(g, inverse_word(c)), embed_h, hw1, hw2);
}

///  Right cancellation: concat(concat(a, b), inv(b)) ≡ a.
proof fn lemma_right_cancel(p: Presentation, a: Word, b: Word)
    requires
        presentation_valid(p),
        word_valid(a, p.num_generators),
        word_valid(b, p.num_generators),
    ensures
        equiv_in_presentation(p, concat(concat(a, b), inverse_word(b)), a),
{
    crate::word::lemma_inverse_word_valid(b, p.num_generators);
    crate::presentation_lemmas::lemma_word_inverse_right(p, b);
    crate::presentation_lemmas::lemma_equiv_concat_right(p, a,
        concat(b, inverse_word(b)), empty_word());
    assert(concat(a, empty_word()) =~= a) by {
        assert(concat(a, empty_word()).len() == a.len());
        assert forall|k: int| 0 <= k < a.len()
            implies concat(a, empty_word())[k] == a[k] by {}
    }
    //  assoc: concat(concat(a, b), inv(b)) =~= concat(a, concat(b, inv(b)))
    assert(concat(concat(a, b), inverse_word(b)) =~=
           concat(a, concat(b, inverse_word(b)))) by {
        let lhs = concat(concat(a, b), inverse_word(b));
        let rhs = concat(a, concat(b, inverse_word(b)));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < a.len() as int {} else {
                let j = k - a.len() as int;
                if j < b.len() as int {} else {}
            }
        }
    }
    crate::word::lemma_concat_word_valid(a, b, p.num_generators);
    crate::word::lemma_concat_word_valid(concat(a, b), inverse_word(b), p.num_generators);
    //  Chain through concat(a, ε): first equiv, then =~= to a
    crate::word::lemma_concat_word_valid(a, concat(b, inverse_word(b)), p.num_generators);
    crate::word::lemma_concat_word_valid(a, empty_word(), p.num_generators);
    crate::presentation::lemma_equiv_refl(p, concat(a, concat(b, inverse_word(b))));
    //  concat(a, concat(b, inv(b))) ≡ concat(a, ε) =~= a. Two-step chain.
}

///  Idempotency: a_rcoset_rep(a_rcoset_rep(g)) =~= a_rcoset_rep(g).
proof fn lemma_a_rcoset_rep_idempotent(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(g, data.p1.num_generators),
    ensures
        a_rcoset_rep(data, a_rcoset_rep(data, g)) =~= a_rcoset_rep(data, g),
{
    let rep = a_rcoset_rep(data, g);
    lemma_a_rcoset_rep_props(data, g);
    lemma_same_a_rcoset_symmetric(data, g, rep);
    lemma_a_rcoset_rep_invariant(data, rep, g);
}

///  Helper: the inverse step for C2 — directly establishes act_left_sym via merge_replaced.
///  Requires rep_inv ≠ ε as a precondition (caller provides via case split).
proof fn lemma_c2_inverse_merge_step(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word, combined_h: Word,
    merged_rep: Word, rest_syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p1.num_generators),
        word_valid(combined_h, k_size(data)),
        word_valid(merged_rep, data.p1.num_generators),
        generator_index(s) < data.p1.num_generators,
        !(c1 =~= empty_word()),
        !(merged_rep =~= empty_word()),
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        a_rcoset_rep(data, c1) =~= c1,
        equiv_in_presentation(data.p1,
            concat(concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(a_words(data), combined_h)), merged_rep),
            concat(apply_embedding(a_words(data), h), c1)),
        //  The inverse product is NOT in the subgroup
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(a_words(data), combined_h)))
            =~= empty_word()),
    ensures ({
        let new_syls = Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep }) + rest_syls;
        act_left_sym(data, inverse_symbol(s), combined_h, new_syls)
            == (h, Seq::new(1, |_i: int| Syllable { is_left: true, rep: c1 }) + rest_syls)
    }),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let embed_h = apply_embedding(a_words(data), h);
    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep }) + rest_syls;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }

    lemma_rcoset_decompose_subgroup_times_rep(data, h, c1);
    assert(generator_index(inv_s) == generator_index(s)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }

    let embed_ch = apply_embedding(a_words(data), combined_h);
    crate::benign::lemma_apply_embedding_valid(a_words(data), combined_h, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::word::lemma_concat_word_valid(embed_h, c1, n1);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n1);
    crate::word::lemma_concat_word_valid(concat(inv_s_word, embed_ch), merged_rep, n1);

    //  full_inv ≡ embed_a(h)·c₁ → rcoset rep = c₁ ≠ ε
    let full_inv = concat(concat(inv_s_word, embed_ch), merged_rep);
    lemma_same_a_rcoset_from_equiv(data, full_inv, concat(embed_h, c1));
    lemma_a_rcoset_rep_invariant(data, full_inv, concat(embed_h, c1));

    //  Explicitly connect merge_replaced preconditions to local variables
    assert(new_syls.first().is_left);
    assert(new_syls.first().rep == merged_rep);
    assert(!(a_rcoset_rep(data, full_inv) =~= empty_word()));
    //  full_inv = concat(product, first_rep) in merge_replaced's terms
    assert(full_inv == concat(concat(Seq::new(1, |_i: int| inv_s), apply_embedding(a_words(data), combined_h)), new_syls.first().rep));

    //  H-part: a_rcoset_h(full_inv) =~= h (from equiv invariance)
    lemma_a_rcoset_h_from_equiv(data, full_inv, h, c1);

    //  merge_replaced: rep_inv ≠ ε, first syl left, merged_rep ≠ ε
    lemma_act_left_sym_merge_replaced(data, inv_s, combined_h, new_syls);
    //  Result: (a_rcoset_h(full_inv), [Syl(left, a_rcoset_rep(full_inv))] + rest)
    //        = (h, [Syl(left, c₁)] + rest)
}

///  Subcase C: G₁ inverse pair when rep' ≠ ε and first syllable IS left (merge).
///  Forward: merge [s]·embed_a(h)·c₁ → (combined_h, merged_syls).
///  Inverse: [inv(s)]·embed_a(combined_h)·merged_rep ≡ embed_a(h)·c₁ → decompose → (h, c₁, rest).
///
///  C2 rep_inv=ε branch: show merged_rep =~= c₁ and product_inv ≡ embed_a(h).
proof fn lemma_c2_rep_zero_branch(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word,
    combined_h: Word, merged_rep: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p1.num_generators),
        word_valid(combined_h, k_size(data)),
        word_valid(merged_rep, data.p1.num_generators),
        generator_index(s) < data.p1.num_generators,
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        a_rcoset_rep(data, c1) =~= c1,
        !(merged_rep =~= empty_word()),
        a_rcoset_rep(data, merged_rep) =~= merged_rep, //  idempotency (caller provides)
        a_rcoset_rep(data, concat(Seq::new(1, |_i: int| inverse_symbol(s)),
            apply_embedding(a_words(data), combined_h))) =~= empty_word(), //  product_inv ∈ A
        equiv_in_presentation(data.p1,
            concat(concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(a_words(data), combined_h)), merged_rep),
            concat(apply_embedding(a_words(data), h), c1)),
    ensures
        merged_rep =~= c1,
        equiv_in_presentation(data.p1,
            concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(a_words(data), combined_h)),
            apply_embedding(a_words(data), h)),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(a_words(data), h);
    let embed_ch = apply_embedding(a_words(data), combined_h);
    let product_inv = concat(inv_s_word, embed_ch);
    let full_inv = concat(product_inv, merged_rep);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), combined_h, n1);
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    crate::word::lemma_inverse_word_valid(merged_rep, n1);
    crate::word::lemma_inverse_word_valid(c1, n1);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n1);
    crate::word::lemma_concat_word_valid(product_inv, merged_rep, n1);
    crate::word::lemma_concat_word_valid(embed_h, c1, n1);

    //  Step 1: full_inv·inv(merged_rep) ≡ product_inv ∈ A → same_a_rcoset(full_inv, merged_rep)
    lemma_right_cancel(p1, product_inv, merged_rep);
    lemma_a_rcoset_rep_props(data, product_inv);
    crate::presentation::lemma_equiv_refl(p1, product_inv);
    lemma_in_subgroup_equiv(p1, a_words(data),
        concat(product_inv, inverse_word(a_rcoset_rep(data, product_inv))), product_inv);
    crate::word::lemma_concat_word_valid(full_inv, inverse_word(merged_rep), n1);
    crate::presentation::lemma_equiv_symmetric(p1,
        concat(full_inv, inverse_word(merged_rep)), product_inv);
    lemma_in_subgroup_equiv(p1, a_words(data), product_inv,
        concat(full_inv, inverse_word(merged_rep)));

    //  Step 2: a_rcoset_rep(merged_rep) =~= c₁ via invariant chain
    lemma_same_a_rcoset_from_equiv(data, full_inv, concat(embed_h, c1));
    lemma_same_a_rcoset_symmetric(data, full_inv, merged_rep);
    lemma_a_rcoset_rep_invariant(data, merged_rep, full_inv);
    lemma_a_rcoset_rep_invariant(data, full_inv, concat(embed_h, c1));
    lemma_rcoset_decompose_subgroup_times_rep(data, h, c1);
    //  a_rcoset_rep(merged_rep) =~= a_rcoset_rep(full_inv) =~= c₁
    //  With idempotency precondition: merged_rep =~= a_rcoset_rep(merged_rep) =~= c₁

    //  Step 3: product_inv ≡ embed_a(h) via right cancellation
    crate::presentation_lemmas::lemma_equiv_concat_left(p1, full_inv, concat(embed_h, c1), inverse_word(c1));
    lemma_right_cancel(p1, product_inv, c1);
    lemma_right_cancel(p1, embed_h, c1);
    crate::presentation::lemma_equiv_transitive(p1,
        product_inv, concat(concat(product_inv, c1), inverse_word(c1)),
        concat(concat(embed_h, c1), inverse_word(c1)));
    crate::presentation::lemma_equiv_transitive(p1,
        product_inv, concat(concat(embed_h, c1), inverse_word(c1)), embed_h);
}


#[verifier::rlimit(40)]
proof fn lemma_inverse_pair_g1_subcase_c2(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p1.num_generators,
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
        syls.len() > 0,
        syls.first().is_left,
        //  Sub-subcase: merged_rep ≠ ε
        !({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
            let full_product = concat(product, syls.first().rep);
            a_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures
        act_word(data, inverse_pair_word(s), h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    let c1 = syls.first().rep;
    let full_product = concat(product, c1);
    let combined_h = a_rcoset_h(data, full_product);
    let merged_rep = a_rcoset_rep(data, full_product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);

    //  Split and compose
    assert(inverse_pair_word(s) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s, h, syls);
    //  Forward: merged_rep ≠ ε → state = (combined_h, [Syl(left, merged_rep)] + syls.drop_first())
    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: true, rep: merged_rep })
        + syls.drop_first();
    lemma_act_word_single(data, inv_s, combined_h, new_syls);

    //  c1 word_valid and c1 ≠ ε from is_canonical_state
    assert(word_valid(c1, n1));
    assert(!(c1 =~= e));
    crate::word::lemma_concat_word_valid(product, c1, n1);

    //  Forward step: merge_replaced
    lemma_act_left_sym_merge_replaced(data, s, h, syls);

    //  [inv(s)]·embed_a(combined_h)·merged_rep ≡ embed_a(h)·c₁
    lemma_inv_s_rcoset_merge_equiv(data, s, h, c1);

    //  Decompose embed_a(h)·c₁: rep = c₁, h-part = h (textbook key property)
    assert(a_rcoset_rep(data, c1) =~= c1);
    lemma_rcoset_decompose_subgroup_times_rep(data, h, c1);

    //  generator_index for dispatch
    assert(generator_index(inv_s) == generator_index(s)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }

    //  Setup for inverse step
    assert(new_syls.first().is_left);
    assert(new_syls.first().rep == merged_rep);
    assert(new_syls.drop_first() =~= syls.drop_first());

    let embed_ch = apply_embedding(a_words(data), combined_h);
    crate::benign::lemma_apply_embedding_valid(a_words(data), combined_h, n1);
    assert(word_valid(inv_s_word, n1)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n1) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    let product_inv = concat(inv_s_word, embed_ch);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n1);
    lemma_a_rcoset_rep_props(data, full_product);
    crate::word::lemma_concat_word_valid(product_inv, merged_rep, n1);

    //  full_inv ≡ embed_a(h)·c₁ → same rcoset → rep(full_inv) =~= c₁ ≠ ε
    let full_inv = concat(product_inv, merged_rep);
    crate::word::lemma_concat_word_valid(embed_h, c1, n1);
    lemma_same_a_rcoset_from_equiv(data, full_inv, concat(embed_h, c1));
    lemma_a_rcoset_rep_invariant(data, full_inv, concat(embed_h, c1));
    //  a_rcoset_rep(full_inv) =~= a_rcoset_rep(embed_a(h)·c₁) =~= c₁ ≠ ε

    //  Idempotency: a_rcoset_rep(merged_rep) =~= merged_rep
    lemma_a_rcoset_rep_idempotent(data, full_product);

    //  syls = [Syl(left, c₁)] + syls.drop_first()
    assert(syls =~= Seq::new(1, |_i: int| Syllable { is_left: true, rep: c1 }) + syls.drop_first()) by {
        assert(syls.len() == 1 + syls.drop_first().len());
        assert forall|k: int| 0 <= k < syls.len() implies
            syls[k] == (Seq::new(1, |_i: int| Syllable { is_left: true, rep: c1 }) + syls.drop_first())[k]
        by { if k == 0 {} else {} }
    }

    //  Case split: both branches give (h, syls)
    let rep_inv = a_rcoset_rep(data, product_inv);
    if rep_inv =~= e {
        //  rep_inv = ε: merged_rep =~= c₁ + product_inv ≡ embed_a(h)
        lemma_c2_rep_zero_branch(data, s, h, c1, combined_h, merged_rep);
        //  → subgroup restore gives h-part = h, and new_syls =~= syls
        lemma_subgroup_rcoset_restore(data, product_inv, h);
        return;
    }

    //  rep_inv ≠ ε: merge → (h, [Syl(left, c₁)] + rest) = (h, syls)
    assert(new_syls.first().is_left);
    assert(new_syls.first().rep == merged_rep);
    lemma_c2_inverse_merge_step(data, s, h, c1, combined_h, merged_rep, syls.drop_first());
}

///  Subcase C1: merge with merged_rep = ε (full product in subgroup).
///  Forward: merge absorbs → (combined_h, syls.drop_first()).
///  Inverse: product_inv ≡ embed_a(h)·c₁, rep_inv = c₁ ≠ ε → PREPEND c₁ → (h, syls).
///  Alternating ensures the inverse step prepends (not merges again).
proof fn lemma_inverse_pair_g1_subcase_c1(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p1.num_generators,
        !(a_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h)))
            =~= empty_word()),
        syls.len() > 0,
        syls.first().is_left,
        //  Sub-subcase: merged_rep = ε (absorbed)
        ({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(a_words(data), h));
            let full_product = concat(product, syls.first().rep);
            a_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures
        act_word(data, inverse_pair_word(s), h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let p1 = data.p1;
    let e = empty_word();
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(s_word, embed_h);
    let c1 = syls.first().rep;
    let full_product = concat(product, c1);
    let combined_h = a_rcoset_h(data, full_product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < a_words(data).len()
        implies word_valid(#[trigger] a_words(data)[i], n1)
    by { assert(word_valid(data.identifications[i].0, n1)); }
    crate::benign::lemma_apply_embedding_valid(a_words(data), h, n1);
    assert(word_valid(s_word, n1)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n1);
    assert(word_valid(c1, n1));
    assert(!(c1 =~= e));
    crate::word::lemma_concat_word_valid(product, c1, n1);

    //  Split and compose
    assert(inverse_pair_word(s) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s, h, syls);

    //  Forward: merge absorbed → state = (combined_h, syls.drop_first())
    lemma_act_left_sym_merge_absorbed(data, s, h, syls);
    let rest = syls.drop_first();
    lemma_act_word_single(data, inv_s, combined_h, rest);

    //  [inv(s)]·embed_a(combined_h)·ε ≡ embed_a(h)·c₁
    lemma_inv_s_rcoset_merge_equiv(data, s, h, c1);

    //  product_inv ≡ embed_a(h)·c₁ (since merged_rep = ε: concat(product_inv, ε) =~= product_inv)
    let embed_ch = apply_embedding(a_words(data), combined_h);
    crate::benign::lemma_apply_embedding_valid(a_words(data), combined_h, n1);
    let product_inv = concat(inv_s_word, embed_ch);

    //  Decompose embed_a(h)·c₁: rep = c₁, h-part = h
    assert(a_rcoset_rep(data, c1) =~= c1);
    lemma_rcoset_decompose_subgroup_times_rep(data, h, c1);

    //  rep_inv =~= c₁ ≠ ε (from equiv invariance)
    assert(word_valid(inv_s_word, n1)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n1) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n1);
    crate::word::lemma_concat_word_valid(embed_h, c1, n1);
    lemma_same_a_rcoset_from_equiv(data, product_inv, concat(embed_h, c1));
    lemma_a_rcoset_rep_invariant(data, product_inv, concat(embed_h, c1));
    //  a_rcoset_rep(product_inv) =~= c₁ ≠ ε

    //  h-part: a_rcoset_h(product_inv) =~= h
    lemma_a_rcoset_h_from_equiv(data, product_inv, h, c1);

    //  generator_index for dispatch
    assert(generator_index(inv_s) == generator_index(s)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }

    //  Alternating: syls[0] is left → syls[1] (if exists) is right → rest starts with right or is empty
    //  So the inverse step PREPENDS (not merges)
    assert(rest.len() == 0 || !rest.first().is_left) by {
        if rest.len() > 0 {
            //  syls[0].is_left and alternating → syls[1].is_left != syls[0].is_left → !syls[1].is_left
            assert(syls[0].is_left);
            assert(syls[0].is_left != syls[1].is_left);
            assert(rest.first() == syls[1]);
        }
    }

    //  Inverse step: PREPEND c₁ → (h, [Syl(left, c₁)] + rest) = (h, syls)
    //  syls = [Syl(left, c₁)] + rest
    assert(syls =~= Seq::new(1, |_i: int| Syllable { is_left: true, rep: c1 }) + rest) by {
        assert(syls.len() == 1 + rest.len());
        assert forall|k: int| 0 <= k < syls.len() implies
            syls[k] == (Seq::new(1, |_i: int| Syllable { is_left: true, rep: c1 }) + rest)[k]
        by { if k == 0 {} else {} }
    }
}

///  Complete G₁ inverse pair triviality: [s, inv(s)] acts trivially on ALL canonical states.
///  Dispatches to subcases A, B, C1, C2 based on the action's branch conditions.
pub proof fn lemma_inverse_pair_g1(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p1.num_generators,
    ensures
        act_word(data, inverse_pair_word(s), h, syls) == (h, syls),
{
    let embed_h = apply_embedding(a_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let rep = a_rcoset_rep(data, product);

    if rep =~= empty_word() {
        //  Subcase A: product in subgroup
        lemma_inverse_pair_g1_subcase_a(data, s, h, syls);
    } else if syls.len() == 0 || !syls.first().is_left {
        //  Subcase B: prepend new syllable
        lemma_inverse_pair_g1_subcase_b(data, s, h, syls);
    } else {
        //  Subcases C: merge with existing left syllable
        let full_product = concat(product, syls.first().rep);
        let merged_rep = a_rcoset_rep(data, full_product);
        if merged_rep =~= empty_word() {
            //  C1: merge absorbed
            lemma_inverse_pair_g1_subcase_c1(data, s, h, syls);
        } else {
            //  C2: merge replaced
            lemma_inverse_pair_g1_subcase_c2(data, s, h, syls);
        }
    }
}

//  ============================================================
//  Part P: Right B-coset infrastructure (mirrors Part N for A-cosets)
//  ============================================================

///  Scan for min right-B-coset length.
proof fn lemma_scan_b_rcoset_len(
    data: AmalgamatedData, g: Word, current: nat, bound: nat,
)
    requires
        has_b_rcoset_word_of_len(data, g, bound),
        current <= bound,
        no_shorter_b_rcoset_word(data, g, current),
    ensures
        exists|l: nat| current <= l && l <= bound
            && #[trigger] is_min_b_rcoset_len(data, g, l),
    decreases bound - current,
{
    if has_b_rcoset_word_of_len(data, g, current) {
        assert(is_min_b_rcoset_len(data, g, current));
    } else { lemma_scan_b_rcoset_len(data, g, current + 1, bound); }
}

///  Scan for min right-B-coset lex rank.
proof fn lemma_scan_b_rcoset_lex(
    data: AmalgamatedData, g: Word, l: nat, current: nat, bound: nat,
)
    requires
        has_b_rcoset_word_of_len_rank(data, g, l, bound),
        current <= bound,
        no_smaller_b_rcoset_lex(data, g, l, current),
    ensures
        exists|r: nat| current <= r && r <= bound
            && #[trigger] is_min_b_rcoset_lex(data, g, l, r),
    decreases bound - current,
{
    if has_b_rcoset_word_of_len_rank(data, g, l, current) {
        assert(is_min_b_rcoset_lex(data, g, l, current));
    } else { lemma_scan_b_rcoset_lex(data, g, l, current + 1, bound); }
}

///  Right-B-coset rep satisfiability.
proof fn lemma_b_rcoset_rep_satisfiable(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p2.num_generators),
    ensures
        is_min_b_rcoset_len(data, g, b_rcoset_min_len(data, g)),
        is_min_b_rcoset_lex(data, g, b_rcoset_min_len(data, g), b_rcoset_min_lex(data, g)),
{
    reveal(presentation_valid);
    crate::word::lemma_inverse_word_valid(g, data.p2.num_generators);
    crate::word::lemma_concat_word_valid(g, inverse_word(g), data.p2.num_generators);
    crate::presentation_lemmas::lemma_word_inverse_right(data.p2, g);
    crate::benign::lemma_identity_in_generated_subgroup(data.p2, b_words(data));
    crate::presentation::lemma_equiv_symmetric(data.p2, concat(g, inverse_word(g)), empty_word());
    lemma_in_subgroup_equiv(data.p2, b_words(data),
        empty_word(), concat(g, inverse_word(g)));
    assert(has_b_rcoset_word_of_len(data, g, g.len() as nat));
    assert(no_shorter_b_rcoset_word(data, g, 0nat));
    lemma_scan_b_rcoset_len(data, g, 0, g.len() as nat);
    let l = b_rcoset_min_len(data, g);
    let w: Word = choose|w: Word| word_valid(w, data.p2.num_generators)
        && same_b_rcoset(data, g, w) && w.len() == l;
    let wr = word_lex_rank_base(w, 2 * data.p2.num_generators + 1);
    assert(has_b_rcoset_word_of_len_rank(data, g, l, wr));
    assert(no_smaller_b_rcoset_lex(data, g, l, 0nat));
    lemma_scan_b_rcoset_lex(data, g, l, 0, wr);
}

///  Extract right-B-coset rep properties.
proof fn lemma_b_rcoset_rep_props(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        word_valid(g, data.p2.num_generators),
    ensures
        same_b_rcoset(data, g, b_rcoset_rep(data, g)),
        word_valid(b_rcoset_rep(data, g), data.p2.num_generators),
        b_rcoset_rep(data, g).len() == b_rcoset_min_len(data, g),
        word_lex_rank_base(b_rcoset_rep(data, g), 2 * data.p2.num_generators + 1) == b_rcoset_min_lex(data, g),
{
    lemma_b_rcoset_rep_satisfiable(data, g);
}

///  No shorter → ≥ for right B-cosets.
proof fn lemma_no_shorter_b_rcoset_word_implies_ge(
    data: AmalgamatedData, g: Word, m: nat, k: nat,
)
    requires
        no_shorter_b_rcoset_word(data, g, m),
        has_b_rcoset_word_of_len(data, g, k),
    ensures k >= m,
    decreases m,
{
    if m == 0 {} else if k == m - 1 {} else if k < m - 1 {
        lemma_no_shorter_b_rcoset_word_implies_ge(data, g, (m - 1) as nat, k);
    }
}

proof fn lemma_no_shorter_b_rcoset_word_forces_zero(
    data: AmalgamatedData, g: Word, l: nat,
)
    requires
        no_shorter_b_rcoset_word(data, g, l),
        has_b_rcoset_word_of_len(data, g, 0nat),
    ensures l == 0,
    decreases l,
{
    if l > 0 { lemma_no_shorter_b_rcoset_word_forces_zero(data, g, (l - 1) as nat); }
}

///  No smaller B-coset lex implies ≥.
proof fn lemma_no_smaller_b_rcoset_lex_implies_ge(
    data: AmalgamatedData, g: Word, l: nat, m: nat, k: nat,
)
    requires
        no_smaller_b_rcoset_lex(data, g, l, m),
        has_b_rcoset_word_of_len_rank(data, g, l, k),
    ensures k >= m,
    decreases m,
{
    if m == 0 {} else if k == m - 1 {} else if k < m - 1 {
        lemma_no_smaller_b_rcoset_lex_implies_ge(data, g, l, (m - 1) as nat, k);
    }
}

///  If g is in the B-subgroup, then b_rcoset_rep(g) =~= ε.
proof fn lemma_b_rcoset_in_subgroup(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        in_right_subgroup(data, g),
    ensures
        b_rcoset_rep(data, g) =~= empty_word(),
{
    let e = empty_word();
    let n2 = data.p2.num_generators;
    assert(inverse_word(e) =~= e) by { assert(inverse_word(e).len() == 0); }
    assert(concat(g, inverse_word(e)) =~= g) by {
        assert(concat(g, e).len() == g.len());
        assert forall|k: int| 0 <= k < g.len()
            implies concat(g, e)[k] == g[k] by {}
    }
    crate::presentation::lemma_equiv_refl(data.p2, g);
    lemma_in_subgroup_equiv(data.p2, b_words(data), g, concat(g, inverse_word(e)));
    assert(word_valid(e, n2)) by { assert(e.len() == 0); }
    assert(has_b_rcoset_word_of_len(data, g, 0nat));
    assert(no_shorter_b_rcoset_word(data, g, 0nat));
    lemma_scan_b_rcoset_len(data, g, 0, 0);
    let l = b_rcoset_min_len(data, g);
    lemma_no_shorter_b_rcoset_word_forces_zero(data, g, l);
    assert(word_lex_rank_base(e, 2 * n2 + 1) == 0nat);
    assert(has_b_rcoset_word_of_len_rank(data, g, 0nat, 0nat));
    assert(no_smaller_b_rcoset_lex(data, g, 0nat, 0nat));
    lemma_scan_b_rcoset_lex(data, g, 0, 0, 0);
}

///  same_b_rcoset is symmetric.
proof fn lemma_same_b_rcoset_symmetric(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        same_b_rcoset(data, g1, g2),
    ensures
        same_b_rcoset(data, g2, g1),
{
    let n2 = data.p2.num_generators;
    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::word::lemma_inverse_word_valid(g2, n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(g2), n2);
    lemma_subgroup_inverse(data.p2, b_words(data), concat(g1, inverse_word(g2)));
    crate::word::lemma_inverse_concat(g1, inverse_word(g2));
    crate::word::lemma_inverse_involution(g2);
    let inv_pair = inverse_word(concat(g1, inverse_word(g2)));
    assert(inv_pair =~= concat(g2, inverse_word(g1))) by {
        assert(inv_pair =~= concat(inverse_word(inverse_word(g2)), inverse_word(g1)));
        assert forall|k: int| 0 <= k < concat(g2, inverse_word(g1)).len()
            implies inv_pair[k] == concat(g2, inverse_word(g1))[k]
        by { if k < g2.len() as int {} else {} }
    }
    crate::word::lemma_inverse_word_valid(g1, n2);
    crate::word::lemma_concat_word_valid(g2, inverse_word(g1), n2);
    crate::presentation::lemma_equiv_refl(data.p2, concat(g2, inverse_word(g1)));
    lemma_in_subgroup_equiv(data.p2, b_words(data),
        inv_pair, concat(g2, inverse_word(g1)));
}

///  If g1 ≡ g2 in G₂, then same_b_rcoset(g1, g2).
proof fn lemma_same_b_rcoset_from_equiv(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        equiv_in_presentation(data.p2, g1, g2),
    ensures
        same_b_rcoset(data, g1, g2),
{
    let p2 = data.p2;
    let n2 = p2.num_generators;
    crate::word::lemma_inverse_word_valid(g1, n2);
    crate::word::lemma_inverse_word_valid(g2, n2);
    crate::presentation::lemma_equiv_symmetric(p2, g1, g2);
    lemma_equiv_inverse(p2, g2, g1);
    crate::presentation::lemma_equiv_refl(p2, g1);
    crate::presentation_lemmas::lemma_equiv_concat(p2,
        g1, g1, inverse_word(g2), inverse_word(g1));
    crate::presentation_lemmas::lemma_word_inverse_right(p2, g1);
    crate::word::lemma_concat_word_valid(g1, inverse_word(g1), n2);
    crate::presentation::lemma_equiv_transitive(p2,
        concat(g1, inverse_word(g2)),
        concat(g1, inverse_word(g1)),
        empty_word());
    crate::benign::lemma_identity_in_generated_subgroup(p2, b_words(data));
    crate::word::lemma_concat_word_valid(g1, inverse_word(g2), n2);
    crate::presentation::lemma_equiv_symmetric(p2, concat(g1, inverse_word(g2)), empty_word());
    lemma_in_subgroup_equiv(p2, b_words(data),
        empty_word(), concat(g1, inverse_word(g2)));
}

///  Transfer: same B-rcoset → coset words transfer.
proof fn lemma_b_rcoset_word_transfer(
    data: AmalgamatedData, g1: Word, g2: Word, l: nat,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        same_b_rcoset(data, g1, g2),
        has_b_rcoset_word_of_len(data, g1, l),
    ensures
        has_b_rcoset_word_of_len(data, g2, l),
{
    let n2 = data.p2.num_generators;
    let w: Word = choose|w: Word| word_valid(w, n2)
        && same_b_rcoset(data, g1, w) && w.len() == l;
    crate::word::lemma_inverse_word_valid(g1, n2);
    crate::word::lemma_inverse_word_valid(g2, n2);
    crate::word::lemma_inverse_word_valid(w, n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(g2), n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(w), n2);
    crate::word::lemma_concat_word_valid(g2, inverse_word(g1), n2);
    crate::word::lemma_concat_word_valid(g2, inverse_word(w), n2);
    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    lemma_subgroup_inverse(data.p2, b_words(data), concat(g1, inverse_word(g2)));
    crate::word::lemma_inverse_concat(g1, inverse_word(g2));
    crate::word::lemma_inverse_involution(g2);
    let inv_pair = inverse_word(concat(g1, inverse_word(g2)));
    assert(inv_pair =~= concat(g2, inverse_word(g1))) by {
        assert(inv_pair =~= concat(inverse_word(inverse_word(g2)), inverse_word(g1)));
        assert forall|k: int| 0 <= k < concat(g2, inverse_word(g1)).len()
            implies inv_pair[k] == concat(g2, inverse_word(g1))[k]
        by { if k < g2.len() as int {} else {} }
    }
    crate::presentation::lemma_equiv_refl(data.p2, concat(g2, inverse_word(g1)));
    lemma_in_subgroup_equiv(data.p2, b_words(data),
        inv_pair, concat(g2, inverse_word(g1)));
    lemma_subgroup_concat(data.p2, b_words(data),
        concat(g2, inverse_word(g1)), concat(g1, inverse_word(w)));
    lemma_four_part_cancel(data.p2, g2, g1, inverse_word(w));
    lemma_in_subgroup_equiv(data.p2, b_words(data),
        concat(concat(g2, inverse_word(g1)), concat(g1, inverse_word(w))),
        concat(g2, inverse_word(w)));
}

///  Transfer with rank for B-rcosets.
proof fn lemma_b_rcoset_word_rank_transfer(
    data: AmalgamatedData, g1: Word, g2: Word, l: nat, r: nat,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        same_b_rcoset(data, g1, g2),
        has_b_rcoset_word_of_len_rank(data, g1, l, r),
    ensures
        has_b_rcoset_word_of_len_rank(data, g2, l, r),
{
    let n2 = data.p2.num_generators;
    let w: Word = choose|w: Word| word_valid(w, n2) && same_b_rcoset(data, g1, w) && w.len() == l
        && word_lex_rank_base(w, 2 * n2 + 1) == r;
    lemma_same_b_rcoset_symmetric(data, g1, g2);
    lemma_subgroup_concat(data.p2, b_words(data),
        concat(g2, inverse_word(g1)),
        concat(g1, inverse_word(w)));
    crate::word::lemma_inverse_word_valid(w, n2);
    crate::word::lemma_concat_word_valid(g2, inverse_word(w), n2);
    lemma_four_part_cancel(data.p2, g2, g1, inverse_word(w));
    lemma_in_subgroup_equiv(data.p2, b_words(data),
        concat(concat(g2, inverse_word(g1)), concat(g1, inverse_word(w))),
        concat(g2, inverse_word(w)));
}

///  B-rcoset rep invariance: same_b_rcoset → same b_rcoset_rep.
proof fn lemma_b_rcoset_rep_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        same_b_rcoset(data, g1, g2),
    ensures
        b_rcoset_rep(data, g1) =~= b_rcoset_rep(data, g2),
{
    let n2 = data.p2.num_generators;
    lemma_b_rcoset_rep_satisfiable(data, g1);
    lemma_b_rcoset_rep_satisfiable(data, g2);
    let l1 = b_rcoset_min_len(data, g1);
    let l2 = b_rcoset_min_len(data, g2);
    lemma_b_rcoset_word_transfer(data, g1, g2, l1);
    lemma_same_b_rcoset_symmetric(data, g1, g2);
    lemma_b_rcoset_word_transfer(data, g2, g1, l2);
    lemma_no_shorter_b_rcoset_word_implies_ge(data, g2, l2, l1);
    lemma_no_shorter_b_rcoset_word_implies_ge(data, g1, l1, l2);
    let l = l1;
    //  Lex rank transfer (same pattern as A-coset)
    let w1: Word = choose|w: Word| word_valid(w, n2) && same_b_rcoset(data, g1, w) && w.len() == l;
    let wr1 = word_lex_rank_base(w1, 2 * n2 + 1);
    assert(has_b_rcoset_word_of_len_rank(data, g1, l, wr1));
    assert(no_smaller_b_rcoset_lex(data, g1, l, 0nat));
    lemma_scan_b_rcoset_lex(data, g1, l, 0, wr1);
    let w2: Word = choose|w: Word| word_valid(w, n2) && same_b_rcoset(data, g2, w) && w.len() == l;
    let wr2 = word_lex_rank_base(w2, 2 * n2 + 1);
    assert(has_b_rcoset_word_of_len_rank(data, g2, l, wr2));
    assert(no_smaller_b_rcoset_lex(data, g2, l, 0nat));
    lemma_scan_b_rcoset_lex(data, g2, l, 0, wr2);
    let r1 = b_rcoset_min_lex(data, g1);
    let r2 = b_rcoset_min_lex(data, g2);
    //  Transfer rank witnesses via explicit helper
    lemma_b_rcoset_word_rank_transfer(data, g1, g2, l, r1);
    lemma_b_rcoset_word_rank_transfer(data, g2, g1, l, r2);
    lemma_no_smaller_b_rcoset_lex_implies_ge(data, g2, l, r2, r1);
    lemma_no_smaller_b_rcoset_lex_implies_ge(data, g1, l, r1, r2);
    //  Lex rank injectivity
    lemma_b_rcoset_rep_props(data, g1);
    lemma_b_rcoset_rep_props(data, g2);
    let rep1 = b_rcoset_rep(data, g1);
    let rep2 = b_rcoset_rep(data, g2);
    let base = 2 * n2 + 1;
    assert forall|k: int| 0 <= k < rep1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rep1[k]) < base
    by { assert(symbol_valid(rep1[k], n2)); match rep1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert forall|k: int| 0 <= k < rep2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] rep2[k]) < base
    by { assert(symbol_valid(rep2[k], n2)); match rep2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert(base > 0);
    lemma_word_lex_rank_base_injective(rep1, rep2, base);
}

///  Idempotency of b_rcoset_rep.
proof fn lemma_b_rcoset_rep_idempotent(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
    ensures
        b_rcoset_rep(data, b_rcoset_rep(data, g)) =~= b_rcoset_rep(data, g),
{
    let rep = b_rcoset_rep(data, g);
    lemma_b_rcoset_rep_props(data, g);
    lemma_same_b_rcoset_symmetric(data, g, rep);
    lemma_b_rcoset_rep_invariant(data, rep, g);
}

//  ============================================================
//  Part Q: G₂ inverse pair helpers (mirrors Part M/O for G₁)
//  ============================================================

///  embed_b(h) is in the B-generated subgroup (mirrors lemma_apply_embedding_in_subgroup).
pub proof fn lemma_apply_embedding_in_subgroup_g2(
    p: Presentation, gens: Seq<Word>, h: Word,
)
    requires
        presentation_valid(p),
        word_valid(h, gens.len()),
        forall|i: int| 0 <= i < gens.len()
            ==> word_valid(#[trigger] gens[i], p.num_generators),
    ensures
        in_generated_subgroup(p, gens, apply_embedding(gens, h)),
    decreases h.len(),
{
    if h.len() == 0 {
        assert(apply_embedding(gens, h) =~= empty_word());
        crate::benign::lemma_identity_in_generated_subgroup(p, gens);
    } else {
        let s = h.first();
        let rest = h.drop_first();
        let head = apply_embedding_symbol(gens, s);
        let tail = apply_embedding(gens, rest);
        lemma_apply_embedding_in_subgroup_g2(p, gens, rest);
        match s {
            Symbol::Gen(i) => {
                crate::benign::lemma_generator_in_generated_subgroup(p, gens, i as int);
            }
            Symbol::Inv(i) => {
                crate::benign::lemma_generator_in_generated_subgroup(p, gens, i as int);
                crate::word::lemma_inverse_word_valid(gens[i as int], p.num_generators);
                lemma_subgroup_inverse(p, gens, gens[i as int]);
            }
        }
        lemma_subgroup_concat(p, gens, head, tail);
    }
}

///  Right B-coset decomposition identity: embed_b(h)·rep ≡ g (textbook g = h·c for G₂).
proof fn lemma_b_rcoset_decomposition(
    data: AmalgamatedData, g: Word, h_witness: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        word_valid(h_witness, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness),
            concat(g, inverse_word(b_rcoset_rep(data, g)))),
    ensures
        equiv_in_presentation(data.p2,
            concat(apply_embedding(b_words(data), b_rcoset_h(data, g)),
                   b_rcoset_rep(data, g)),
            g),
        word_valid(b_rcoset_h(data, g), k_size(data)),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }

    //  h-part satisfiability: reuse the h-witness pattern
    assert(has_right_h_witness_of_len(data, target, h_witness.len() as nat));
    let pred_h = |l: nat| has_right_h_witness_of_len(data, target, l);
    assert(pred_h(h_witness.len() as nat));
    lemma_nat_well_ordering(pred_h, h_witness.len() as nat);
    //  h-lex satisfiability
    let l = b_rcoset_h_min_len(data, g);
    let w: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target);
    let wr = word_lex_rank_base(w, h_lex_base(data));
    assert(has_right_h_witness_of_len_rank(data, target, l, wr));
    assert(no_smaller_h_lex_g2(data, target, l, 0nat));
    lemma_scan_min_h_lex_g2(data, target, l, 0, wr);

    let h = b_rcoset_h(data, g);
    let embed_h = apply_embedding(b_words(data), h);
    lemma_b_rcoset_rep_props(data, g);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    //  embed_b(h)·rep ≡ target·rep = (g·inv(rep))·rep ≡ g
    crate::presentation_lemmas::lemma_equiv_concat_left(p2, embed_h, target, rep);
    crate::word::lemma_inverse_word_valid(rep, n2);
    assert(concat(concat(g, inverse_word(rep)), rep) =~=
           concat(g, concat(inverse_word(rep), rep))) by {
        let lhs = concat(concat(g, inverse_word(rep)), rep);
        let rhs = concat(g, concat(inverse_word(rep), rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < g.len() as int {} else {
                let j = k - g.len() as int;
                if j < inverse_word(rep).len() as int {} else {}
            }
        }
    }
    crate::presentation_lemmas::lemma_word_inverse_left(p2, rep);
    crate::word::lemma_concat_word_valid(g, concat(inverse_word(rep), rep), n2);
    crate::presentation::lemma_equiv_refl(p2, concat(g, concat(inverse_word(rep), rep)));
    crate::presentation_lemmas::lemma_equiv_concat_right(p2, g,
        concat(inverse_word(rep), rep), empty_word());
    assert(concat(g, empty_word()) =~= g) by {
        assert(concat(g, empty_word()).len() == g.len());
        assert forall|k: int| 0 <= k < g.len()
            implies concat(g, empty_word())[k] == g[k] by {}
    }
    crate::presentation::lemma_equiv_transitive(p2,
        concat(embed_h, rep),
        concat(g, concat(inverse_word(rep), rep)),
        g);
}

///  Free reduction for G₂: [inv(s)]·[s]·w ≡ w in G₂.
proof fn lemma_inv_s_s_cancel_g2(
    data: AmalgamatedData, s: Symbol, w: Word,
)
    requires
        presentation_valid(data.p2),
        word_valid(w, data.p2.num_generators),
        generator_index(s) < data.p2.num_generators,
    ensures
        equiv_in_presentation(data.p2,
            concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                   concat(Seq::new(1, |_i: int| s), w)),
            w),
{
    lemma_inv_s_s_cancel(data.p2, s, w);
}

///  G₂ general helper: [inv(s)]·embed_b(b_rcoset_h(product))·b_rcoset_rep(product) ≡ embed_b(h)
///  where product = [s]·embed_b(h). Works for all subcases.
proof fn lemma_inv_s_rcoset_product_equiv_g2(
    data: AmalgamatedData, s: Symbol, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        generator_index(s) < data.p2.num_generators,
    ensures ({
        let embed_h = apply_embedding(b_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let h_prime = b_rcoset_h(data, product);
        let embed_h_prime = apply_embedding(b_words(data), h_prime);
        let rep_prime = b_rcoset_rep(data, product);
        let full = concat(concat(Seq::new(1, |_i: int| inverse_symbol(s)), embed_h_prime), rep_prime);
        &&& equiv_in_presentation(data.p2, full, embed_h)
        &&& word_valid(h_prime, k_size(data))
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(s_word, embed_h);
    let rep_prime = b_rcoset_rep(data, product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    assert(word_valid(s_word, n2)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n2) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n2);

    //  h-witness from subgroup structure
    lemma_b_rcoset_rep_props(data, product);
    crate::word::lemma_inverse_word_valid(rep_prime, n2);
    crate::word::lemma_concat_word_valid(product, inverse_word(rep_prime), n2);
    lemma_subgroup_to_k_word(p2, b_words(data), concat(product, inverse_word(rep_prime)));
    let hw_r: Word = choose|hw: Word| word_valid(hw, b_words(data).len())
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(product, inverse_word(rep_prime)));
    assert(b_words(data).len() == k_size(data));

    //  embed_b(h')·rep' ≡ product
    lemma_b_rcoset_decomposition(data, product, hw_r);
    let h_prime = b_rcoset_h(data, product);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    let embed_h_prime = apply_embedding(b_words(data), h_prime);

    //  [inv(s)]·(embed_b(h')·rep') ≡ [inv(s)]·product
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p2, inv_s_word, concat(embed_h_prime, rep_prime), product);

    //  Associativity
    let full = concat(concat(inv_s_word, embed_h_prime), rep_prime);
    assert(full =~= concat(inv_s_word, concat(embed_h_prime, rep_prime))) by {
        let lhs = full;
        let rhs = concat(inv_s_word, concat(embed_h_prime, rep_prime));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inv_s_word.len() as int {} else {
                let j = k - inv_s_word.len() as int;
                if j < embed_h_prime.len() as int {} else {}
            }
        }
    }

    //  [inv(s)]·[s]·embed_h ≡ embed_h
    crate::word::lemma_concat_word_valid(embed_h_prime, rep_prime, n2);
    lemma_inv_s_s_cancel(p2, s, embed_h);
    assert(concat(inv_s_word, product) =~= concat(inv_s_word, concat(s_word, embed_h)));

    crate::presentation::lemma_equiv_transitive(p2,
        concat(inv_s_word, concat(embed_h_prime, rep_prime)),
        concat(inv_s_word, concat(s_word, embed_h)),
        embed_h);
    return;
}

///  G₂ merge equiv: [inv(s)]·embed_b(combined_h)·merged_rep ≡ embed_b(h)·c₁
proof fn lemma_inv_s_rcoset_merge_equiv_g2(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p2.num_generators),
        generator_index(s) < data.p2.num_generators,
    ensures ({
        let embed_h = apply_embedding(b_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let full_product = concat(product, c1);
        let combined_h = b_rcoset_h(data, full_product);
        let embed_ch = apply_embedding(b_words(data), combined_h);
        let merged_rep = b_rcoset_rep(data, full_product);
        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        let full = concat(concat(inv_s_word, embed_ch), merged_rep);
        &&& equiv_in_presentation(data.p2, full, concat(embed_h, c1))
        &&& word_valid(combined_h, k_size(data))
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let s_word = Seq::new(1, |_i: int| s);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(s_word, embed_h);
    let full_product = concat(product, c1);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    assert(word_valid(s_word, n2)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n2) by { match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n2);
    crate::word::lemma_concat_word_valid(product, c1, n2);

    //  Rcoset decomposition of full_product
    lemma_b_rcoset_rep_props(data, full_product);
    let merged_rep = b_rcoset_rep(data, full_product);
    crate::word::lemma_inverse_word_valid(merged_rep, n2);
    crate::word::lemma_concat_word_valid(full_product, inverse_word(merged_rep), n2);
    lemma_subgroup_to_k_word(p2, b_words(data), concat(full_product, inverse_word(merged_rep)));
    let hw: Word = choose|hw: Word| word_valid(hw, b_words(data).len())
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(full_product, inverse_word(merged_rep)));
    assert(b_words(data).len() == k_size(data));
    lemma_b_rcoset_decomposition(data, full_product, hw);
    let combined_h = b_rcoset_h(data, full_product);
    crate::benign::lemma_apply_embedding_valid(b_words(data), combined_h, n2);
    let embed_ch = apply_embedding(b_words(data), combined_h);

    //  [inv(s)]·(embed_b(ch)·mr) ≡ [inv(s)]·full_product ≡ embed_h·c1
    crate::presentation_lemmas::lemma_equiv_concat_right(
        p2, inv_s_word, concat(embed_ch, merged_rep), full_product);
    assert(concat(inv_s_word, concat(concat(s_word, embed_h), c1)) =~=
           concat(inv_s_word, concat(s_word, concat(embed_h, c1)))) by {
        let lhs = concat(inv_s_word, concat(concat(s_word, embed_h), c1));
        let rhs = concat(inv_s_word, concat(s_word, concat(embed_h, c1)));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < 1 {} else { let j = k - 1; if j < s_word.len() as int {} else {
                let j2 = j - s_word.len() as int;
                if j2 < embed_h.len() as int {} else {}
            }}
        }
    }
    crate::word::lemma_concat_word_valid(embed_h, c1, n2);
    lemma_inv_s_s_cancel(p2, s, concat(embed_h, c1));
    let full = concat(concat(inv_s_word, embed_ch), merged_rep);
    assert(full =~= concat(inv_s_word, concat(embed_ch, merged_rep))) by {
        let lhs = full; let rhs = concat(inv_s_word, concat(embed_ch, merged_rep));
        assert(lhs.len() == rhs.len());
        assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
            if k < inv_s_word.len() as int {} else {
                let j = k - inv_s_word.len() as int;
                if j < embed_ch.len() as int {} else {}
            }
        }
    }
    crate::presentation::lemma_equiv_transitive(p2,
        concat(inv_s_word, concat(embed_ch, merged_rep)),
        concat(inv_s_word, concat(s_word, concat(embed_h, c1))),
        concat(embed_h, c1));
}

///  Z3 helper: act_right_sym merge absorbed.
proof fn lemma_act_right_sym_merge_absorbed(
    data: AmalgamatedData, s: Symbol, h: Word, syllables: Seq<Syllable>,
)
    requires
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syllables.len() > 0,
        !syllables.first().is_left,
        b_rcoset_rep(data,
            concat(concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)),
                   syllables.first().rep))
            =~= empty_word(),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let full_product = concat(product, syllables.first().rep);
        act_right_sym(data, s, h, syllables)
            == (b_rcoset_h(data, full_product), syllables.drop_first())
    }),
{
}

///  Z3 helper: act_right_sym merge replaced.
proof fn lemma_act_right_sym_merge_replaced(
    data: AmalgamatedData, s: Symbol, h: Word, syllables: Seq<Syllable>,
)
    requires
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syllables.len() > 0,
        !syllables.first().is_left,
        !({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
            let full_product = concat(product, syllables.first().rep);
            b_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let full_product = concat(product, syllables.first().rep);
        let merged_rep = b_rcoset_rep(data, full_product);
        act_right_sym(data, s, h, syllables)
            == (b_rcoset_h(data, full_product),
                Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
                + syllables.drop_first())
    }),
{
}

///  G₂ h-witness transfer between equivalent targets.
proof fn lemma_h_witness_transfer_g2(
    data: AmalgamatedData, target1: Word, target2: Word, l: nat,
)
    requires
        has_right_h_witness_of_len(data, target1, l),
        equiv_in_presentation(data.p2, target1, target2),
        presentation_valid(data.p2),
    ensures
        has_right_h_witness_of_len(data, target2, l),
{
    let h: Word = choose|h: Word| word_valid(h, k_size(data)) && h.len() == l
        && equiv_in_presentation(data.p2, apply_embedding(b_words(data), h), target1);
    crate::presentation::lemma_equiv_transitive(
        data.p2, apply_embedding(b_words(data), h), target1, target2);
}

///  No smaller G₂ h-lex implies ≥.
proof fn lemma_no_smaller_h_lex_g2_implies_ge(
    data: AmalgamatedData, target: Word, l: nat, m: nat, k: nat,
)
    requires
        no_smaller_h_lex_g2(data, target, l, m),
        has_right_h_witness_of_len_rank(data, target, l, k),
    ensures k >= m,
    decreases m,
{
    if m == 0 {} else if k == m - 1 {} else if k < m - 1 {
        lemma_no_smaller_h_lex_g2_implies_ge(data, target, l, (m - 1) as nat, k);
    }
}

///  G₂ h-min-len equality: targets ≡ → same min h-len.
proof fn lemma_b_rcoset_h_min_len_equiv(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        equiv_in_presentation(data.p2, g1, g2),
        b_rcoset_rep(data, g1) =~= empty_word(),
        b_rcoset_rep(data, g2) =~= empty_word(),
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness1),
            concat(g1, inverse_word(b_rcoset_rep(data, g1)))),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness2),
            concat(g2, inverse_word(b_rcoset_rep(data, g2)))),
    ensures
        b_rcoset_h_min_len(data, g1) == b_rcoset_h_min_len(data, g2),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let target1 = concat(g1, inverse_word(b_rcoset_rep(data, g1)));
    let target2 = concat(g2, inverse_word(b_rcoset_rep(data, g2)));

    assert(has_right_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_right_h_witness_of_len(data, target2, h_witness2.len() as nat));
    let pred1 = |l: nat| has_right_h_witness_of_len(data, target1, l);
    let pred2 = |l: nat| has_right_h_witness_of_len(data, target2, l);
    assert(pred1(h_witness1.len() as nat));
    assert(pred2(h_witness2.len() as nat));
    lemma_nat_well_ordering(pred1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred2, h_witness2.len() as nat);

    let l1 = b_rcoset_h_min_len(data, g1);
    let l2 = b_rcoset_h_min_len(data, g2);

    lemma_h_witness_transfer_g2(data, target1, target2, l1);
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, g1), n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(b_rcoset_rep(data, g1)), n2);
    crate::presentation::lemma_equiv_symmetric(p2, target1, target2);
    lemma_h_witness_transfer_g2(data, target2, target1, l2);

    lemma_no_pred_below_implies_ge(pred2, l2, l1);
    lemma_no_pred_below_implies_ge(pred1, l1, l2);
}

///  G₂ h-part equiv invariance: if g1 ≡ g2 in G₂ and both in B-subgroup,
///  then b_rcoset_h gives same result.
proof fn lemma_b_rcoset_h_equiv_invariant(
    data: AmalgamatedData, g1: Word, g2: Word,
    h_witness1: Word, h_witness2: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g1, data.p2.num_generators),
        word_valid(g2, data.p2.num_generators),
        equiv_in_presentation(data.p2, g1, g2),
        //  Both in B-subgroup (reps = ε)
        b_rcoset_rep(data, g1) =~= empty_word(),
        b_rcoset_rep(data, g2) =~= empty_word(),
        //  H-witnesses for satisfiability
        word_valid(h_witness1, k_size(data)),
        word_valid(h_witness2, k_size(data)),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness1),
            concat(g1, inverse_word(b_rcoset_rep(data, g1)))),
        equiv_in_presentation(data.p2,
            apply_embedding(b_words(data), h_witness2),
            concat(g2, inverse_word(b_rcoset_rep(data, g2)))),
    ensures
        b_rcoset_h(data, g1) =~= b_rcoset_h(data, g2),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let target1 = concat(g1, inverse_word(b_rcoset_rep(data, g1)));
    let target2 = concat(g2, inverse_word(b_rcoset_rep(data, g2)));

    //  Min-len equality from helper
    lemma_b_rcoset_h_min_len_equiv(data, g1, g2, h_witness1, h_witness2);
    let l = b_rcoset_h_min_len(data, g1);

    //  Lex: h-lex satisfiability + transfer
    //  Need h-witness satisfiability for min_len
    assert(has_right_h_witness_of_len(data, target1, h_witness1.len() as nat));
    assert(has_right_h_witness_of_len(data, target2, h_witness2.len() as nat));
    let pred1 = |l: nat| has_right_h_witness_of_len(data, target1, l);
    let pred2 = |l: nat| has_right_h_witness_of_len(data, target2, l);
    assert(pred1(h_witness1.len() as nat));
    assert(pred2(h_witness2.len() as nat));
    lemma_nat_well_ordering(pred1, h_witness1.len() as nat);
    lemma_nat_well_ordering(pred2, h_witness2.len() as nat);
    //  Now has_right_h_witness_of_len(target1, l) and (target2, l) hold (from choose satisfiability)
    //  Extract witnesses at min length
    let w1: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target1);
    let wr1 = word_lex_rank_base(w1, h_lex_base(data));
    //  has_right_h_witness_of_len_rank: exists witness with len l and rank wr1
    assert(has_right_h_witness_of_len_rank(data, target1, l, wr1));
    assert(no_smaller_h_lex_g2(data, target1, l, 0nat));
    lemma_scan_min_h_lex_g2(data, target1, l, 0, wr1);

    let w2: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target2);
    let wr2 = word_lex_rank_base(w2, h_lex_base(data));
    assert(has_right_h_witness_of_len_rank(data, target2, l, wr2));
    assert(no_smaller_h_lex_g2(data, target2, l, 0nat));
    lemma_scan_min_h_lex_g2(data, target2, l, 0, wr2);

    let r1 = b_rcoset_h_min_lex(data, g1);
    let r2 = b_rcoset_h_min_lex(data, g2);
    //  Transfer rank witnesses (explicit — Z3 can't see existential transfer automatically)
    //  w1 has equiv(embed_b(w1), target1) ≡ target2, so w1 witnesses for target2 too
    let rep1_word = b_rcoset_h(data, g1);
    let rep2_word = b_rcoset_h(data, g2);
    //  For r1: the rep1_word satisfies the predicate for target1. By equiv: also for target2.
    //  For r2: symmetric.
    //  Use: h_witness_transfer_g2 at the rank level
    //  Actually: the existential witnesses have the right lex rank. The equiv of targets transfers them.
    //  The key: if embed_b(w) ≡ target1 and target1 ≡ target2, then embed_b(w) ≡ target2 (transitivity).
    //  So the SAME K-word w witnesses for target2 with the same len and lex rank.
    //  Z3 should see this via the transitivity in the existential.
    //  Let's try extracting the witness explicitly:
    let rw1: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && word_lex_rank_base(w, h_lex_base(data)) == r1
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target1);
    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), rw1), target1, target2);
    let rw2: Word = choose|w: Word| word_valid(w, k_size(data)) && w.len() == l
        && word_lex_rank_base(w, h_lex_base(data)) == r2
        && equiv_in_presentation(p2, apply_embedding(b_words(data), w), target2);
    //  target2 ≡ target1 (symmetric of target1 ≡ target2)
    crate::word::lemma_inverse_word_valid(b_rcoset_rep(data, g1), n2);
    crate::word::lemma_concat_word_valid(g1, inverse_word(b_rcoset_rep(data, g1)), n2);
    crate::presentation::lemma_equiv_symmetric(p2, target1, target2);
    crate::presentation::lemma_equiv_transitive(p2,
        apply_embedding(b_words(data), rw2), target2, target1);

    //  Bidirectional ≥ on lex
    lemma_no_smaller_h_lex_g2_implies_ge(data, target2, l, r2, r1);
    lemma_no_smaller_h_lex_g2_implies_ge(data, target1, l, r1, r2);
    //  r1 == r2

    //  Lex rank injectivity → same word
    let h1 = b_rcoset_h(data, g1);
    let h2 = b_rcoset_h(data, g2);
    let base = h_lex_base(data);
    assert forall|k: int| 0 <= k < h1.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] h1[k]) < base
    by { assert(symbol_valid(h1[k], k_size(data))); match h1[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert forall|k: int| 0 <= k < h2.len()
        implies crate::todd_coxeter::symbol_to_column(#[trigger] h2[k]) < base
    by { assert(symbol_valid(h2[k], k_size(data))); match h2[k] { Symbol::Gen(i) => {} Symbol::Inv(i) => {} } }
    assert(base > 0) by { assert(h_lex_base(data) == 2 * k_size(data) + 1); }
    lemma_word_lex_rank_base_injective(h1, h2, base);
}

///  G₂ h-witness exists for any G₂-word.
pub proof fn lemma_h_witness_exists_g2(data: AmalgamatedData, g: Word)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
    ensures
        exists|h: Word| word_valid(h, k_size(data))
            && equiv_in_presentation(data.p2,
                apply_embedding(b_words(data), h),
                concat(g, inverse_word(b_rcoset_rep(data, g)))),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let rep = b_rcoset_rep(data, g);
    let target = concat(g, inverse_word(rep));
    reveal(presentation_valid);

    lemma_b_rcoset_rep_props(data, g);
    crate::word::lemma_inverse_word_valid(g, n2);
    crate::word::lemma_inverse_word_valid(rep, n2);
    crate::word::lemma_concat_word_valid(g, inverse_word(rep), n2);
    crate::word::lemma_concat_word_valid(g, inverse_word(g), n2);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }

    //  same_b_rcoset(g, rep) → g·inv(rep) ∈ B → subgroup_to_k_word → witness
    lemma_subgroup_to_k_word(p2, b_words(data), target);
    assert(b_words(data).len() == k_size(data));
}

///  G₂ h-part from equiv: if g ≡ embed_b(h)·c and both canonical, then b_rcoset_h(g) =~= h.
proof fn lemma_b_rcoset_h_from_equiv(
    data: AmalgamatedData, g: Word, h: Word, c: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(g, data.p2.num_generators),
        word_valid(h, k_size(data)),
        word_valid(c, data.p2.num_generators),
        equiv_in_presentation(data.p2, g, concat(apply_embedding(b_words(data), h), c)),
        b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h, //  h B-canonical
        b_rcoset_rep(data, c) =~= c,
        b_rcoset_rep(data, g) =~= c,
    ensures
        b_rcoset_h(data, g) =~= h,
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let embed_h = apply_embedding(b_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    crate::word::lemma_inverse_word_valid(c, n2);

    //  target_g = g·inv(c) ≡ (embed_h·c)·inv(c) ≡ embed_h (by right_cancel + concat_left)
    crate::word::lemma_concat_word_valid(g, inverse_word(c), n2);
    crate::word::lemma_concat_word_valid(embed_h, c, n2);
    crate::presentation_lemmas::lemma_equiv_concat_left(p2, g, concat(embed_h, c), inverse_word(c));
    lemma_right_cancel(p2, embed_h, c);
    crate::presentation::lemma_equiv_transitive(p2,
        concat(g, inverse_word(c)), concat(concat(embed_h, c), inverse_word(c)), embed_h);

    //  Both g·inv(c) and embed_h are ≡ embed_h, both ∈ B-subgroup
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    crate::presentation::lemma_equiv_symmetric(p2, concat(g, inverse_word(c)), embed_h);
    lemma_in_subgroup_equiv(p2, b_words(data), embed_h, concat(g, inverse_word(c)));
    lemma_b_rcoset_in_subgroup(data, concat(g, inverse_word(c)));
    lemma_b_rcoset_in_subgroup(data, embed_h);

    //  h-part invariance: both targets ≡ embed_h, both reps = ε
    //  b_rcoset_h_min_len, b_rcoset_h_min_lex are the same for both (bidirectional transfer)
    //  lex rank injectivity → same word
    lemma_h_witness_exists_g2(data, concat(g, inverse_word(c)));
    lemma_h_witness_exists_g2(data, embed_h);
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(concat(g, inverse_word(c)),
                   inverse_word(b_rcoset_rep(data, concat(g, inverse_word(c))))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(embed_h, inverse_word(b_rcoset_rep(data, embed_h))));
    lemma_b_rcoset_h_equiv_invariant(data, concat(g, inverse_word(c)), embed_h, hw1, hw2);
}

///  G₂ subgroup restore: if product2 ≡ embed_b(h) and h canonical, then reps = ε, h-part = h.
proof fn lemma_subgroup_rcoset_restore_g2(
    data: AmalgamatedData, product2: Word, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(product2, data.p2.num_generators),
        equiv_in_presentation(data.p2, product2, apply_embedding(b_words(data), h)),
        is_canonical_state(data, h, Seq::<Syllable>::empty()),
    ensures
        b_rcoset_rep(data, product2) =~= empty_word(),
        b_rcoset_h(data, product2) =~= h,
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let embed_h_b = apply_embedding(b_words(data), h);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    //  product2 ∈ B-subgroup
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    crate::presentation::lemma_equiv_symmetric(p2, product2, embed_h_b);
    lemma_in_subgroup_equiv(p2, b_words(data), embed_h_b, product2);
    lemma_b_rcoset_in_subgroup(data, product2);
    lemma_b_rcoset_in_subgroup(data, embed_h_b);

    //  H-part invariance: both targets ≡ embed_b(h) → same canonical K-word
    lemma_h_witness_exists_g2(data, product2);
    lemma_h_witness_exists_g2(data, embed_h_b);
    let hw1: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(product2, inverse_word(b_rcoset_rep(data, product2))));
    let hw2: Word = choose|hw: Word| word_valid(hw, k_size(data))
        && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
            concat(embed_h_b, inverse_word(b_rcoset_rep(data, embed_h_b))));
    lemma_b_rcoset_h_equiv_invariant(data, product2, embed_h_b, hw1, hw2);
    //  b_rcoset_h(product2) =~= b_rcoset_h(embed_h_b) =~= h
    //  (from is_canonical_state + subgroup restore)
}

///  G₂ decompose: embed_b(h)·c₁ → (h, c₁) when both canonical.
proof fn lemma_b_rcoset_decompose_subgroup_times_rep(
    data: AmalgamatedData, h: Word, c1: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p2.num_generators),
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h, //  h A-canonical
        b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h, //  h B-canonical
        b_rcoset_rep(data, c1) =~= c1, //  c₁ canonical
    ensures
        b_rcoset_rep(data, concat(apply_embedding(b_words(data), h), c1)) =~= c1,
        b_rcoset_h(data, concat(apply_embedding(b_words(data), h), c1)) =~= h,
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(embed_h, c1);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    crate::word::lemma_concat_word_valid(embed_h, c1, n2);

    //  same_b_rcoset(product, c1): product·inv(c1) = embed_h·c1·inv(c1) ≡ embed_h ∈ B
    crate::word::lemma_inverse_word_valid(c1, n2);
    lemma_right_cancel(p2, embed_h, c1);
    lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
    crate::word::lemma_concat_word_valid(product, inverse_word(c1), n2);
    crate::presentation::lemma_equiv_symmetric(p2,
        concat(concat(embed_h, c1), inverse_word(c1)), embed_h);
    lemma_in_subgroup_equiv(p2, b_words(data), embed_h,
        concat(product, inverse_word(c1)));

    //  Rep invariance: b_rcoset_rep(product) =~= b_rcoset_rep(c1) =~= c1
    lemma_b_rcoset_rep_invariant(data, product, c1);

    //  H-part: use lemma_b_rcoset_h_from_equiv
    //  product ≡ embed_h·c1, b_rcoset_rep(product) =~= c1, h B-canonical
    crate::presentation::lemma_equiv_refl(p2, product);
    lemma_b_rcoset_h_from_equiv(data, product, h, c1);
}

//  ============================================================
//  Part R: G₂ inverse pair subcases + dispatch
//  ============================================================

///  G₂ subcase A helper: establish product2 ≡ embed_b(h) and word_valid.
proof fn lemma_g2_subcase_a_setup(
    data: AmalgamatedData, s: Symbol, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        generator_index(s) < data.p2.num_generators,
        b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word(),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let h_prime = b_rcoset_h(data, product);
        let product2 = concat(Seq::new(1, |_i: int| inverse_symbol(s)),
            apply_embedding(b_words(data), h_prime));
        &&& equiv_in_presentation(data.p2, product2, apply_embedding(b_words(data), h))
        &&& word_valid(product2, data.p2.num_generators)
        &&& word_valid(h_prime, k_size(data))
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    reveal(presentation_valid);
    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

    lemma_inv_s_rcoset_product_equiv_g2(data, s, h);
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let h_prime = b_rcoset_h(data, product);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    assert(word_valid(inv_s_word, n2)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::word::lemma_concat_word_valid(inv_s_word, apply_embedding(b_words(data), h_prime), n2);
}

///  G₂ subcase A: rep = ε.
proof fn lemma_inverse_pair_g2_subcase_a(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word(),
    ensures ({
        let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + data.p1.num_generators),
                                   Symbol::Inv(i) => Symbol::Inv(i + data.p1.num_generators) };
        act_word(data, inverse_pair_word(s_shifted), h, syls) == (h, syls)
    }),
{
    let n1 = data.p1.num_generators;
    let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + n1),
                               Symbol::Inv(i) => Symbol::Inv(i + n1) };
    let s_word = Seq::new(1, |_i: int| s_shifted);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s_shifted));
    reveal(presentation_valid);

    //  Composition + single-step
    assert(inverse_pair_word(s_shifted) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s_shifted).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s_shifted)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s_shifted, h, syls);
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let h_prime = b_rcoset_h(data, product);
    lemma_act_word_single(data, inverse_symbol(s_shifted), h_prime, syls);

    //  Setup + restore (from helpers)
    lemma_g2_subcase_a_setup(data, s, h);
    lemma_subgroup_rcoset_restore_g2(data,
        concat(Seq::new(1, |_i: int| inverse_symbol(s)),
            apply_embedding(b_words(data), h_prime)), h);
}

///  G₂ version: if rep' = b_rcoset_rep(product) ≠ ε, then the inverse product is NOT in B.
///  Mirrors lemma_inv_step_rep_nonzero with b_words/p2/b_rcoset.
///  Proof by contradiction: if product_inv ∈ B, then rep' ∈ B (by left cancellation),
///  hence product ∈ B, contradicting rep' ≠ ε.
proof fn lemma_inv_step_rep_nonzero_g2(
    data: AmalgamatedData, s: Symbol, h: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let h_prime = b_rcoset_h(data, product);
        let product_inv = concat(Seq::new(1, |_i: int| inverse_symbol(s)),
            apply_embedding(b_words(data), h_prime));
        !(b_rcoset_rep(data, product_inv) =~= empty_word())
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let rep_prime = b_rcoset_rep(data, product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }

    //  Get h_prime and product_inv
    lemma_inv_s_rcoset_product_equiv_g2(data, s, h);
    let h_prime = b_rcoset_h(data, product);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    let embed_h_prime = apply_embedding(b_words(data), h_prime);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let product_inv = concat(inv_s_word, embed_h_prime);

    //  Proof by contradiction: assume b_rcoset_rep(product_inv) =~= ε
    if b_rcoset_rep(data, product_inv) =~= empty_word() {
        //  product_inv ∈ B
        assert(word_valid(inv_s_word, n2)) by {
            assert forall|k: int| 0 <= k < inv_s_word.len()
                implies symbol_valid(#[trigger] inv_s_word[k], n2) by {
                    match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
                }
        }
        crate::word::lemma_concat_word_valid(inv_s_word, embed_h_prime, n2);
        crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);

        lemma_b_rcoset_rep_props(data, product_inv);
        crate::presentation::lemma_equiv_refl(p2, product_inv);
        lemma_in_subgroup_equiv(p2, b_words(data),
            concat(product_inv, inverse_word(b_rcoset_rep(data, product_inv))), product_inv);
        //  product_inv ∈ B

        //  embed_b(h') · rep' ≡ product (from rcoset decomposition)
        lemma_b_rcoset_rep_props(data, product);
        let s_word = Seq::new(1, |_i: int| s);
        assert(word_valid(s_word, n2)) by {
            assert forall|k: int| 0 <= k < s_word.len()
                implies symbol_valid(#[trigger] s_word[k], n2) by {
                    match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
                }
        }
        crate::word::lemma_concat_word_valid(s_word, embed_h, n2);
        crate::word::lemma_inverse_word_valid(rep_prime, n2);
        crate::word::lemma_concat_word_valid(product, inverse_word(rep_prime), n2);
        lemma_subgroup_to_k_word(p2, b_words(data), concat(product, inverse_word(rep_prime)));
        let hw_r: Word = choose|hw: Word| word_valid(hw, b_words(data).len())
            && equiv_in_presentation(p2, apply_embedding(b_words(data), hw),
                concat(product, inverse_word(rep_prime)));
        assert(b_words(data).len() == k_size(data));
        lemma_b_rcoset_decomposition(data, product, hw_r);

        //  [inv(s)] · embed_b(h') · rep' ≡ embed_b(h) (from general helper)
        let full = concat(concat(inv_s_word, embed_h_prime), rep_prime);
        //  full ≡ embed_b(h) ∈ B → full ∈ B
        lemma_apply_embedding_in_subgroup_g2(p2, b_words(data), h);
        crate::word::lemma_concat_word_valid(concat(inv_s_word, embed_h_prime), rep_prime, n2);
        crate::presentation::lemma_equiv_symmetric(p2, full, embed_h);
        lemma_in_subgroup_equiv(p2, b_words(data), embed_h, full);

        //  full = concat(product_inv, rep_prime). product_inv ∈ B and full ∈ B
        //  → rep_prime ∈ B (by left cancellation)
        lemma_subgroup_left_cancel(p2, b_words(data), product_inv, rep_prime);

        //  rep' ∈ B → product ∈ B:
        lemma_subgroup_concat(p2, b_words(data),
            concat(product, inverse_word(rep_prime)), rep_prime);

        //  concat(concat(product, inv(rep')), rep') ≡ product
        assert(concat(concat(product, inverse_word(rep_prime)), rep_prime) =~=
               concat(product, concat(inverse_word(rep_prime), rep_prime))) by {
            let lhs = concat(concat(product, inverse_word(rep_prime)), rep_prime);
            let rhs = concat(product, concat(inverse_word(rep_prime), rep_prime));
            assert(lhs.len() == rhs.len());
            assert forall|k: int| 0 <= k < lhs.len() implies lhs[k] == rhs[k] by {
                if k < product.len() as int {} else {
                    let j = k - product.len() as int;
                    if j < inverse_word(rep_prime).len() as int {} else {}
                }
            }
        }
        crate::presentation_lemmas::lemma_word_inverse_left(p2, rep_prime);
        crate::presentation_lemmas::lemma_equiv_concat_right(
            p2, product, concat(inverse_word(rep_prime), rep_prime), empty_word());
        assert(concat(product, empty_word()) =~= product) by {
            assert(concat(product, empty_word()).len() == product.len());
            assert forall|k: int| 0 <= k < product.len()
                implies concat(product, empty_word())[k] == product[k] by {}
        }
        lemma_in_subgroup_equiv(p2, b_words(data),
            concat(concat(product, inverse_word(rep_prime)), rep_prime), product);
        //  product ∈ B → b_rcoset_rep(product) =~= ε
        lemma_b_rcoset_in_subgroup(data, product);
        //  But rep' = b_rcoset_rep(product) ≠ ε. Contradiction!
    }
}

///  G₂ subcase B merge helper: extracts the heavy equiv + restore chain.
///  Mirrors lemma_inverse_pair_g1_subcase_b_merge with b_words/p2/b_rcoset.
proof fn lemma_inverse_pair_g2_subcase_b_merge(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let h_prime = b_rcoset_h(data, product);
        let rep_prime = b_rcoset_rep(data, product);
        let embed_h_prime = apply_embedding(b_words(data), h_prime);
        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        let full_product2 = concat(concat(inv_s_word, embed_h_prime), rep_prime);
        &&& b_rcoset_rep(data, full_product2) =~= empty_word()
        &&& b_rcoset_h(data, full_product2) =~= h
        &&& word_valid(h_prime, k_size(data))
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let rep_prime = b_rcoset_rep(data, product);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    let s_word = Seq::new(1, |_i: int| s);
    assert(word_valid(s_word, n2)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n2);

    //  General helper: [inv(s)]·embed_b(h')·rep' ≡ embed_b(h) + word_valid(h')
    lemma_inv_s_rcoset_product_equiv_g2(data, s, h);

    let h_prime = b_rcoset_h(data, product);
    let embed_h_prime = apply_embedding(b_words(data), h_prime);
    let full_product2 = concat(concat(inv_s_word, embed_h_prime), rep_prime);

    assert(word_valid(inv_s_word, n2)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h_prime, n2);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_h_prime, n2);
    lemma_b_rcoset_rep_props(data, product);
    crate::word::lemma_concat_word_valid(concat(inv_s_word, embed_h_prime), rep_prime, n2);

    //  is_canonical_state(data, h, []) follows from is_canonical_state(data, h, syls)
    assert(is_canonical_state(data, h, Seq::<Syllable>::empty())) by {
        assert(Seq::<Syllable>::empty().len() == 0int);
    }
    lemma_subgroup_rcoset_restore_g2(data, full_product2, h);
}

///  G₂ subcase B complete inverse step: combines merge + rep_nonzero + merge_absorbed
///  into one helper to keep the main function lightweight.
proof fn lemma_g2_b_complete_inverse_step(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syls.len() == 0 || syls.first().is_left,
    ensures ({
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let h_prime = b_rcoset_h(data, product);
        let rep_prime = b_rcoset_rep(data, product);
        let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: rep_prime }) + syls;
        act_right_sym(data, inverse_symbol(s), h_prime, new_syls) == (h, syls)
    }),
{
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let rep_prime = b_rcoset_rep(data, product);
    let h_prime = b_rcoset_h(data, product);
    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: rep_prime }) + syls;

    lemma_inverse_pair_g2_subcase_b_merge(data, s, h, syls);
    lemma_inv_step_rep_nonzero_g2(data, s, h);

    assert(!new_syls.first().is_left);
    assert(new_syls.first().rep == rep_prime);
    assert(new_syls.drop_first() =~= syls);
    assert(generator_index(inverse_symbol(s)) == generator_index(s)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    lemma_act_right_sym_merge_absorbed(data, inverse_symbol(s), h_prime, new_syls);
}

///  G₂ subcase B: rep ≠ ε, first syllable is left or empty (prepend).
#[verifier::rlimit(40)]
proof fn lemma_inverse_pair_g2_subcase_b(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syls.len() == 0 || syls.first().is_left,
    ensures ({
        let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + data.p1.num_generators),
                                   Symbol::Inv(i) => Symbol::Inv(i + data.p1.num_generators) };
        act_word(data, inverse_pair_word(s_shifted), h, syls) == (h, syls)
    }),
{
    let n1 = data.p1.num_generators;
    let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + n1),
                               Symbol::Inv(i) => Symbol::Inv(i + n1) };
    let s_word = Seq::new(1, |_i: int| s_shifted);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s_shifted));
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let h_prime = b_rcoset_h(data, product);
    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: b_rcoset_rep(data, product) }) + syls;

    assert(inverse_pair_word(s_shifted) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s_shifted).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s_shifted)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s_shifted, h, syls);
    lemma_act_word_single(data, inverse_symbol(s_shifted), h_prime, new_syls);
    lemma_g2_b_complete_inverse_step(data, s, h, syls);
}

///  G₂ C1 inverse step helper: establishes that after the merge-absorbed forward step,
///  the inverse product decomposes as (rep = c₁, h-part = h).
///  Extracts the heavy merge_equiv + rep invariance + h-part chain.
proof fn lemma_g2_c1_inverse_step(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p2.num_generators),
        generator_index(s) < data.p2.num_generators,
        !(c1 =~= empty_word()),
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h,
        b_rcoset_rep(data, c1) =~= c1,
        ({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
            let full_product = concat(product, c1);
            b_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let embed_h = apply_embedding(b_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let full_product = concat(product, c1);
        let combined_h = b_rcoset_h(data, full_product);
        let embed_ch = apply_embedding(b_words(data), combined_h);
        let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
        let product_inv = concat(inv_s_word, embed_ch);
        &&& b_rcoset_rep(data, product_inv) =~= c1
        &&& b_rcoset_h(data, product_inv) =~= h
        &&& word_valid(combined_h, k_size(data))
        &&& word_valid(product_inv, data.p2.num_generators)
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let full_product = concat(product, c1);
    let combined_h = b_rcoset_h(data, full_product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    let s_word = Seq::new(1, |_i: int| s);
    assert(word_valid(s_word, n2)) by {
        assert forall|k: int| 0 <= k < s_word.len()
            implies symbol_valid(#[trigger] s_word[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::word::lemma_concat_word_valid(s_word, embed_h, n2);
    crate::word::lemma_concat_word_valid(product, c1, n2);

    //  [inv(s)]·embed_b(combined_h)·ε ≡ embed_b(h)·c₁ (since merged_rep = ε)
    lemma_inv_s_rcoset_merge_equiv_g2(data, s, h, c1);

    let embed_ch = apply_embedding(b_words(data), combined_h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), combined_h, n2);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    assert(word_valid(inv_s_word, n2)) by {
        assert forall|k: int| 0 <= k < inv_s_word.len()
            implies symbol_valid(#[trigger] inv_s_word[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    let product_inv = concat(inv_s_word, embed_ch);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n2);
    crate::word::lemma_concat_word_valid(embed_h, c1, n2);

    //  Rep invariance: product_inv ≡ embed_b(h)·c₁ → same_b_rcoset → rep = c₁
    lemma_same_b_rcoset_from_equiv(data, product_inv, concat(embed_h, c1));
    lemma_b_rcoset_rep_invariant(data, product_inv, concat(embed_h, c1));
    lemma_b_rcoset_decompose_subgroup_times_rep(data, h, c1);

    //  H-part: b_rcoset_h(product_inv) =~= h
    lemma_b_rcoset_h_from_equiv(data, product_inv, h, c1);
}

///  G₂ C1 complete inverse step: combines inverse_step + alternating + syls reconstruction.
proof fn lemma_g2_c1_complete_inverse_step(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syls.len() > 0,
        !syls.first().is_left,
        ({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
            let full_product = concat(product, syls.first().rep);
            b_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let c1 = syls.first().rep;
        let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
        let full_product = concat(product, c1);
        let combined_h = b_rcoset_h(data, full_product);
        let rest = syls.drop_first();
        act_right_sym(data, inverse_symbol(s), combined_h, rest) == (h, syls)
    }),
{
    let c1 = syls.first().rep;
    let rest = syls.drop_first();

    //  Inverse step decomposition: rep(product_inv) = c₁, h-part = h
    lemma_g2_c1_inverse_step(data, s, h, c1);

    //  Alternating: syls[0] is right → syls[1] is left → rest starts with left
    assert(rest.len() == 0 || rest.first().is_left) by {
        if rest.len() > 0 {
            assert(!syls[0].is_left);
            assert(syls[0].is_left != syls[1].is_left);
            assert(rest.first() == syls[1]);
        }
    }

    //  syls = [Syl(false, c₁)] + rest
    assert(syls =~= Seq::new(1, |_i: int| Syllable { is_left: false, rep: c1 }) + rest) by {
        assert(syls.len() == 1 + rest.len());
        assert forall|k: int| 0 <= k < syls.len() implies
            syls[k] == (Seq::new(1, |_i: int| Syllable { is_left: false, rep: c1 }) + rest)[k]
        by { if k == 0 {} else {} }
    }
}

///  G₂ subcase C1: merge absorbed (merged_rep = ε).
#[verifier::rlimit(40)]
proof fn lemma_inverse_pair_g2_subcase_c1(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syls.len() > 0,
        !syls.first().is_left,
        ({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
            let full_product = concat(product, syls.first().rep);
            b_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + data.p1.num_generators),
                                   Symbol::Inv(i) => Symbol::Inv(i + data.p1.num_generators) };
        act_word(data, inverse_pair_word(s_shifted), h, syls) == (h, syls)
    }),
{
    let n1 = data.p1.num_generators;
    let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + n1),
                               Symbol::Inv(i) => Symbol::Inv(i + n1) };
    let s_word = Seq::new(1, |_i: int| s_shifted);
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s_shifted));
    let c1 = syls.first().rep;
    let combined_h = b_rcoset_h(data, concat(concat(Seq::new(1, |_i: int| s),
        apply_embedding(b_words(data), h)), c1));

    assert(inverse_pair_word(s_shifted) =~= concat(inv_s_word, s_word)) by {
        assert(inverse_pair_word(s_shifted).len() == 2);
        assert(concat(inv_s_word, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s_shifted)[k] == concat(inv_s_word, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word, s_word, h, syls);
    lemma_act_word_single(data, s_shifted, h, syls);
    lemma_act_right_sym_merge_absorbed(data, s, h, syls);
    lemma_act_word_single(data, inverse_symbol(s_shifted), combined_h, syls.drop_first());
    lemma_g2_c1_complete_inverse_step(data, s, h, syls);
    assert(generator_index(inverse_symbol(s_shifted)) >= n1);
}

///  G₂ C2 helper: rep_inv = ε branch → merged_rep =~= c₁ and product_inv ≡ embed_b(h).
///  Mirrors lemma_c2_rep_zero_branch with b_words/p2/b_rcoset.
proof fn lemma_c2_rep_zero_branch_g2(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word,
    combined_h: Word, merged_rep: Word,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p2.num_generators),
        word_valid(combined_h, k_size(data)),
        word_valid(merged_rep, data.p2.num_generators),
        generator_index(s) < data.p2.num_generators,
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h,
        b_rcoset_rep(data, c1) =~= c1,
        !(merged_rep =~= empty_word()),
        b_rcoset_rep(data, merged_rep) =~= merged_rep, //  idempotency
        b_rcoset_rep(data, concat(Seq::new(1, |_i: int| inverse_symbol(s)),
            apply_embedding(b_words(data), combined_h))) =~= empty_word(),
        equiv_in_presentation(data.p2,
            concat(concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(b_words(data), combined_h)), merged_rep),
            concat(apply_embedding(b_words(data), h), c1)),
    ensures
        merged_rep =~= c1,
        equiv_in_presentation(data.p2,
            concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(b_words(data), combined_h)),
            apply_embedding(b_words(data), h)),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let inv_s_word = Seq::new(1, |_i: int| inverse_symbol(s));
    let embed_h = apply_embedding(b_words(data), h);
    let embed_ch = apply_embedding(b_words(data), combined_h);
    let product_inv = concat(inv_s_word, embed_ch);
    let full_inv = concat(product_inv, merged_rep);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), combined_h, n2);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    crate::word::lemma_inverse_word_valid(merged_rep, n2);
    crate::word::lemma_inverse_word_valid(c1, n2);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n2);
    crate::word::lemma_concat_word_valid(product_inv, merged_rep, n2);
    crate::word::lemma_concat_word_valid(embed_h, c1, n2);

    //  Step 1: full_inv·inv(merged_rep) ≡ product_inv ∈ B → same_b_rcoset(full_inv, merged_rep)
    lemma_right_cancel(p2, product_inv, merged_rep);
    lemma_b_rcoset_rep_props(data, product_inv);
    crate::presentation::lemma_equiv_refl(p2, product_inv);
    lemma_in_subgroup_equiv(p2, b_words(data),
        concat(product_inv, inverse_word(b_rcoset_rep(data, product_inv))), product_inv);
    crate::word::lemma_concat_word_valid(full_inv, inverse_word(merged_rep), n2);
    crate::presentation::lemma_equiv_symmetric(p2,
        concat(full_inv, inverse_word(merged_rep)), product_inv);
    lemma_in_subgroup_equiv(p2, b_words(data), product_inv,
        concat(full_inv, inverse_word(merged_rep)));

    //  Step 2: b_rcoset_rep(merged_rep) =~= c₁ via invariant chain
    lemma_same_b_rcoset_from_equiv(data, full_inv, concat(embed_h, c1));
    lemma_same_b_rcoset_symmetric(data, full_inv, merged_rep);
    lemma_b_rcoset_rep_invariant(data, merged_rep, full_inv);
    lemma_b_rcoset_rep_invariant(data, full_inv, concat(embed_h, c1));
    lemma_b_rcoset_decompose_subgroup_times_rep(data, h, c1);

    //  Step 3: product_inv ≡ embed_b(h) via right cancellation
    crate::presentation_lemmas::lemma_equiv_concat_left(p2, full_inv, concat(embed_h, c1), inverse_word(c1));
    lemma_right_cancel(p2, product_inv, c1);
    lemma_right_cancel(p2, embed_h, c1);
    crate::presentation::lemma_equiv_transitive(p2,
        product_inv, concat(concat(product_inv, c1), inverse_word(c1)),
        concat(concat(embed_h, c1), inverse_word(c1)));
    crate::presentation::lemma_equiv_transitive(p2,
        product_inv, concat(concat(embed_h, c1), inverse_word(c1)), embed_h);
}

///  G₂ C2 helper: rep_inv ≠ ε branch → act_right_sym merges to give (h, [Syl(false, c₁)] + rest).
///  Mirrors lemma_c2_inverse_merge_step with b_words/p2/b_rcoset.
proof fn lemma_c2_inverse_merge_step_g2(
    data: AmalgamatedData, s: Symbol, h: Word, c1: Word, combined_h: Word,
    merged_rep: Word, rest_syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        word_valid(h, k_size(data)),
        word_valid(c1, data.p2.num_generators),
        word_valid(combined_h, k_size(data)),
        word_valid(merged_rep, data.p2.num_generators),
        generator_index(s) < data.p2.num_generators,
        !(c1 =~= empty_word()),
        !(merged_rep =~= empty_word()),
        left_h_part(data, apply_embedding(a_words(data), h)) =~= h,
        b_rcoset_h(data, apply_embedding(b_words(data), h)) =~= h,
        b_rcoset_rep(data, c1) =~= c1,
        equiv_in_presentation(data.p2,
            concat(concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(b_words(data), combined_h)), merged_rep),
            concat(apply_embedding(b_words(data), h), c1)),
        //  The inverse product is NOT in the subgroup
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| inverse_symbol(s)),
                apply_embedding(b_words(data), combined_h)))
            =~= empty_word()),
    ensures ({
        let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep }) + rest_syls;
        act_right_sym(data, inverse_symbol(s), combined_h, new_syls)
            == (h, Seq::new(1, |_i: int| Syllable { is_left: false, rep: c1 }) + rest_syls)
    }),
{
    let n2 = data.p2.num_generators;
    let p2 = data.p2;
    let inv_s = inverse_symbol(s);
    let inv_s_word = Seq::new(1, |_i: int| inv_s);
    let embed_h = apply_embedding(b_words(data), h);
    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep }) + rest_syls;
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }

    lemma_b_rcoset_decompose_subgroup_times_rep(data, h, c1);
    assert(generator_index(inv_s) == generator_index(s)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }

    let embed_ch = apply_embedding(b_words(data), combined_h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), combined_h, n2);
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    crate::word::lemma_concat_word_valid(embed_h, c1, n2);
    crate::word::lemma_concat_word_valid(inv_s_word, embed_ch, n2);
    crate::word::lemma_concat_word_valid(concat(inv_s_word, embed_ch), merged_rep, n2);

    //  full_inv ≡ embed_b(h)·c₁ → rcoset rep = c₁ ≠ ε
    let full_inv = concat(concat(inv_s_word, embed_ch), merged_rep);
    lemma_same_b_rcoset_from_equiv(data, full_inv, concat(embed_h, c1));
    lemma_b_rcoset_rep_invariant(data, full_inv, concat(embed_h, c1));

    //  Connect merge_replaced preconditions
    assert(!new_syls.first().is_left);
    assert(new_syls.first().rep == merged_rep);
    assert(!(b_rcoset_rep(data, full_inv) =~= empty_word()));
    assert(full_inv == concat(concat(Seq::new(1, |_i: int| inv_s),
        apply_embedding(b_words(data), combined_h)), new_syls.first().rep));

    //  H-part: b_rcoset_h(full_inv) =~= h
    lemma_b_rcoset_h_from_equiv(data, full_inv, h, c1);

    //  merge_replaced
    lemma_act_right_sym_merge_replaced(data, inv_s, combined_h, new_syls);
}

///  G₂ C2 complete inverse step: handles merge_equiv + case split + dispatch.
///  Extracts all heavy logic from the main C2 function.
proof fn lemma_g2_c2_complete_inverse_step(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syls.len() > 0,
        !syls.first().is_left,
        !({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
            let full_product = concat(product, syls.first().rep);
            b_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let embed_h = apply_embedding(b_words(data), h);
        let product = concat(Seq::new(1, |_i: int| s), embed_h);
        let c1 = syls.first().rep;
        let full_product = concat(product, c1);
        let combined_h = b_rcoset_h(data, full_product);
        let merged_rep = b_rcoset_rep(data, full_product);
        let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
            + syls.drop_first();
        act_right_sym(data, inverse_symbol(s), combined_h, new_syls) == (h, syls)
    }),
{
    let n2 = data.p2.num_generators;
    let e = empty_word();
    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s), embed_h);
    let c1 = syls.first().rep;
    let full_product = concat(product, c1);
    let combined_h = b_rcoset_h(data, full_product);
    let merged_rep = b_rcoset_rep(data, full_product);
    reveal(presentation_valid);

    assert forall|i: int| 0 <= i < b_words(data).len()
        implies word_valid(#[trigger] b_words(data)[i], n2)
    by { assert(word_valid(data.identifications[i].1, n2)); }
    crate::benign::lemma_apply_embedding_valid(b_words(data), h, n2);
    assert(word_valid(c1, n2));
    assert(!(c1 =~= e));
    let s_local_word = Seq::new(1, |_i: int| s);
    assert(word_valid(s_local_word, n2)) by {
        assert forall|k: int| 0 <= k < s_local_word.len()
            implies symbol_valid(#[trigger] s_local_word[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    crate::word::lemma_concat_word_valid(s_local_word, embed_h, n2);
    crate::word::lemma_concat_word_valid(product, c1, n2);

    //  [inv(s)]·embed_b(combined_h)·merged_rep ≡ embed_b(h)·c₁
    lemma_inv_s_rcoset_merge_equiv_g2(data, s, h, c1);

    //  Idempotency: b_rcoset_rep(merged_rep) =~= merged_rep
    lemma_b_rcoset_rep_idempotent(data, full_product);

    //  syls = [Syl(false, c₁)] + syls.drop_first()
    assert(syls =~= Seq::new(1, |_i: int| Syllable { is_left: false, rep: c1 }) + syls.drop_first()) by {
        assert(syls.len() == 1 + syls.drop_first().len());
        assert forall|k: int| 0 <= k < syls.len() implies
            syls[k] == (Seq::new(1, |_i: int| Syllable { is_left: false, rep: c1 }) + syls.drop_first())[k]
        by { if k == 0 {} else {} }
    }

    //  Setup for case split
    let embed_ch = apply_embedding(b_words(data), combined_h);
    crate::benign::lemma_apply_embedding_valid(b_words(data), combined_h, n2);
    let inv_s_local = Seq::new(1, |_i: int| inverse_symbol(s));
    assert(word_valid(inv_s_local, n2)) by {
        assert forall|k: int| 0 <= k < inv_s_local.len()
            implies symbol_valid(#[trigger] inv_s_local[k], n2) by {
                match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
            }
    }
    let product_inv = concat(inv_s_local, embed_ch);
    crate::word::lemma_concat_word_valid(inv_s_local, embed_ch, n2);
    lemma_b_rcoset_rep_props(data, full_product);

    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
        + syls.drop_first();

    let rep_inv = b_rcoset_rep(data, product_inv);
    if rep_inv =~= e {
        lemma_c2_rep_zero_branch_g2(data, s, h, c1, combined_h, merged_rep);
        assert(is_canonical_state(data, h, Seq::<Syllable>::empty())) by {
            assert(Seq::<Syllable>::empty().len() == 0int);
        }
        lemma_subgroup_rcoset_restore_g2(data, product_inv, h);
        return;
    }

    //  rep_inv ≠ ε: merge
    lemma_c2_inverse_merge_step_g2(data, s, h, c1, combined_h, merged_rep, syls.drop_first());
}

///  G₂ subcase C2: merge replaced (merged_rep ≠ ε).
#[verifier::rlimit(40)]
proof fn lemma_inverse_pair_g2_subcase_c2(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) < data.p2.num_generators,
        !(b_rcoset_rep(data,
            concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h)))
            =~= empty_word()),
        syls.len() > 0,
        !syls.first().is_left,
        !({
            let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
            let full_product = concat(product, syls.first().rep);
            b_rcoset_rep(data, full_product) =~= empty_word()
        }),
    ensures ({
        let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + data.p1.num_generators),
                                   Symbol::Inv(i) => Symbol::Inv(i + data.p1.num_generators) };
        act_word(data, inverse_pair_word(s_shifted), h, syls) == (h, syls)
    }),
{
    let n1 = data.p1.num_generators;
    let s_shifted = match s { Symbol::Gen(i) => Symbol::Gen(i + n1),
                               Symbol::Inv(i) => Symbol::Inv(i + n1) };
    let s_word = Seq::new(1, |_i: int| s_shifted);
    let inv_s_word_shifted = Seq::new(1, |_i: int| inverse_symbol(s_shifted));
    let product = concat(Seq::new(1, |_i: int| s), apply_embedding(b_words(data), h));
    let c1 = syls.first().rep;
    let full_product = concat(product, c1);
    let combined_h = b_rcoset_h(data, full_product);
    let merged_rep = b_rcoset_rep(data, full_product);
    let new_syls = Seq::new(1, |_i: int| Syllable { is_left: false, rep: merged_rep })
        + syls.drop_first();

    assert(inverse_pair_word(s_shifted) =~= concat(inv_s_word_shifted, s_word)) by {
        assert(inverse_pair_word(s_shifted).len() == 2);
        assert(concat(inv_s_word_shifted, s_word).len() == 2);
        assert forall|k: int| 0 <= k < 2
            implies inverse_pair_word(s_shifted)[k] == concat(inv_s_word_shifted, s_word)[k] by {}
    }
    lemma_act_word_concat(data, inv_s_word_shifted, s_word, h, syls);
    lemma_act_word_single(data, s_shifted, h, syls);
    lemma_act_right_sym_merge_replaced(data, s, h, syls);
    lemma_act_word_single(data, inverse_symbol(s_shifted), combined_h, new_syls);
    lemma_g2_c2_complete_inverse_step(data, s, h, syls);
    assert(generator_index(inverse_symbol(s_shifted)) >= n1);
}

///  Complete G₂ inverse pair triviality.
///  For ANY G₂ symbol s (shifted, gen_index >= n1) and ANY canonical state: [s, inv(s)] acts trivially.
pub proof fn lemma_inverse_pair_g2(
    data: AmalgamatedData, s: Symbol, h: Word, syls: Seq<Syllable>,
)
    requires
        amalgamated_data_valid(data),
        presentation_valid(data.p1),
        presentation_valid(data.p2),
        is_canonical_state(data, h, syls),
        generator_index(s) >= data.p1.num_generators,
        generator_index(s) < data.p1.num_generators + data.p2.num_generators,
    ensures
        act_word(data, inverse_pair_word(s), h, syls) == (h, syls),
{
    let n1 = data.p1.num_generators;
    let s_local = unshift_sym(s, n1);
    //  s_local has gen_index < n2
    //  act_sym(s, ...) = act_right_sym(s_local, ...)
    //  The inverse pair [s, inv(s)] processes via act_sym → act_right_sym for each symbol

    let embed_h = apply_embedding(b_words(data), h);
    let product = concat(Seq::new(1, |_i: int| s_local), embed_h);
    let rep = b_rcoset_rep(data, product);

    if rep =~= empty_word() {
        lemma_inverse_pair_g2_subcase_a(data, s_local, h, syls);
    } else if syls.len() == 0 || syls.first().is_left {
        lemma_inverse_pair_g2_subcase_b(data, s_local, h, syls);
    } else {
        let full_product = concat(product, syls.first().rep);
        let merged_rep = b_rcoset_rep(data, full_product);
        if merged_rep =~= empty_word() {
            lemma_inverse_pair_g2_subcase_c1(data, s_local, h, syls);
        } else {
            lemma_inverse_pair_g2_subcase_c2(data, s_local, h, syls);
        }
    }
    //  Connect s_local shifted back to s
    assert(inverse_pair_word(s) == inverse_pair_word(
        match s_local { Symbol::Gen(i) => Symbol::Gen(i + n1),
                        Symbol::Inv(i) => Symbol::Inv(i + n1) }));
}

} //  verus!


//  ================================================================
//  FILE: tower.rs
//  ================================================================

//  Tower construction for Britton's lemma.
//
//  Defines the iterated amalgamated free product T_n = G_0 *_A G_1 *_A ... *_A G_n
//  and proves that G = G_0 embeds in T_n (conditional on Cayley table existence).
//
//  The tower is built recursively:
//    tower(data, 0) = data.base
//    tower(data, n+1) = AFP(tower(data, n), data.base, identifications at junction n↔n+1)
//
//  Copy k uses generators k*ng .. (k+1)*ng - 1 where ng = base.num_generators.
//  Junction k↔k+1 identifies a_i in copy k with b_i in copy k+1.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::normal_form_amalgamated::*;
use crate::hnn::*;

verus! {

//  ============================================================
//  Part A: Tower definitions
//  ============================================================

///  The AFP data at tower junction k: tower(k) *_A base.
///    p1 = tower(k)
///    p2 = base
///    identifications[i] = (shift(a_i, k*ng), b_i)
pub open spec fn tower_afp_data(data: HNNData, k: nat) -> AmalgamatedData
    decreases k, 1nat,
{
    let ng = data.base.num_generators;
    AmalgamatedData {
        p1: tower_presentation(data, k),
        p2: data.base,
        identifications: Seq::new(
            data.associations.len(),
            |i: int| (
                shift_word(data.associations[i].0, k * ng),
                data.associations[i].1,
            ),
        ),
    }
}

///  Tower presentation: (n+1) copies of G, glued by identification relators.
///    tower(data, 0) = data.base
///    tower(data, n+1) = amalgamated_free_product(tower_afp_data(data, n))
pub open spec fn tower_presentation(data: HNNData, n: nat) -> Presentation
    decreases n, 0nat,
{
    if n == 0 {
        data.base
    } else {
        amalgamated_free_product(tower_afp_data(data, (n - 1) as nat))
    }
}

///  Shift a word to copy k in the tower.
pub open spec fn word_in_copy(w: Word, ng: nat, k: nat) -> Word {
    shift_word(w, k * ng)
}

//  ============================================================
//  Part B: Tower structural lemmas
//  ============================================================

///  Tower has (n+1)*ng generators.
pub proof fn lemma_tower_num_generators(data: HNNData, n: nat)
    requires
        hnn_data_valid(data),
    ensures
        tower_presentation(data, n).num_generators == (n + 1) * data.base.num_generators,
    decreases n,
{
    let ng = data.base.num_generators;
    if n == 0 {
        assert(tower_presentation(data, 0).num_generators == ng);
        assert(ng == 1 * ng);
    } else {
        let prev = (n - 1) as nat;
        lemma_tower_num_generators(data, prev);
        let afp_data = tower_afp_data(data, prev);
        crate::amalgamated_free_product::lemma_add_relators_num_generators(
            free_product(afp_data.p1, afp_data.p2),
            amalgamation_relators(afp_data),
        );
        assert(free_product(afp_data.p1, afp_data.p2).num_generators
            == afp_data.p1.num_generators + afp_data.p2.num_generators);
        assert(afp_data.p1.num_generators == n * ng);
        assert(afp_data.p2.num_generators == ng);
        assert(tower_presentation(data, n).num_generators == n * ng + ng);
        assert(n * ng + ng == (n + 1) * ng) by (nonlinear_arith);
    }
}

///  word_valid monotonicity: valid for m implies valid for any m' >= m.
proof fn lemma_word_valid_weaken(w: Word, m: nat, m_prime: nat)
    requires
        word_valid(w, m),
        m <= m_prime,
    ensures
        word_valid(w, m_prime),
{
    assert forall|k: int| 0 <= k < w.len()
        implies symbol_valid(w[k], m_prime)
    by {
        assert(symbol_valid(w[k], m));
        match w[k] {
            Symbol::Gen(i) => {}
            Symbol::Inv(i) => {}
        }
    }
}

///  Tower presentation is valid at every level.
pub proof fn lemma_tower_valid(data: HNNData, n: nat)
    requires
        hnn_data_valid(data),
    ensures
        presentation_valid(tower_presentation(data, n)),
    decreases n, 0nat,
{
    if n == 0 {
        reveal(presentation_valid);
    } else {
        let prev = (n - 1) as nat;
        lemma_tower_afp_data_valid(data, prev);
        lemma_amalgamated_valid(tower_afp_data(data, prev));
    }
}

///  The tower AFP data at level k has valid amalgamated data.
pub proof fn lemma_tower_afp_data_valid(data: HNNData, k: nat)
    requires
        hnn_data_valid(data),
    ensures
        amalgamated_data_valid(tower_afp_data(data, k)),
    decreases k, 1nat,
{
    let ng = data.base.num_generators;
    let afp_data = tower_afp_data(data, k);

    reveal(presentation_valid);
    assert(presentation_valid(data.base));

    lemma_tower_valid(data, k);
    lemma_tower_num_generators(data, k);

    assert forall|i: int| 0 <= i < afp_data.identifications.len()
        implies ({
            &&& word_valid(afp_data.identifications[i].0, afp_data.p1.num_generators)
            &&& word_valid(afp_data.identifications[i].1, afp_data.p2.num_generators)
        })
    by {
        let a_i = data.associations[i].0;
        let b_i = data.associations[i].1;
        let u_i = shift_word(a_i, k * ng);
        assert(afp_data.identifications[i] == (u_i, b_i));
        assert(word_valid(a_i, ng));
        assert(word_valid(b_i, ng));
        //  shift(a_i, k*ng) is word_valid for (k+1)*ng = tower(k).num_generators
        assert(afp_data.p1.num_generators == (k + 1) * ng);
        assert forall|j: int| 0 <= j < u_i.len()
            implies symbol_valid(u_i[j], (k + 1) * ng)
        by {
            assert(symbol_valid(a_i[j], ng));
            match a_i[j] {
                Symbol::Gen(idx) => {
                    assert(u_i[j] == Symbol::Gen((idx + k * ng) as nat));
                    assert(idx + k * ng < (k + 1) * ng) by (nonlinear_arith)
                        requires idx < ng;
                }
                Symbol::Inv(idx) => {
                    assert(u_i[j] == Symbol::Inv((idx + k * ng) as nat));
                    assert(idx + k * ng < (k + 1) * ng) by (nonlinear_arith)
                        requires idx < ng;
                }
            }
        }
    }
}

//  ============================================================
//  Part C: Textbook tower embedding (uses one-shot AFP injectivity)
//  ============================================================

///  Textbook prerequisites at tower level k:
///  - identifications_isomorphic: the identification map is an isomorphism
///  - action_preserves_canonical: the van der Waerden action preserves canonical states
///  (identity state canonicality is now proved from amalgamated_data_valid via lemma_identity_state_canonical)
pub open spec fn tower_textbook_prereqs_at(data: HNNData, k: nat) -> bool {
    let afp_data = tower_afp_data(data, k);
    &&& crate::normal_form_amalgamated::identifications_isomorphic(afp_data)
    &&& crate::normal_form_afp_textbook::action_preserves_canonical(afp_data)
}

///  Textbook prerequisites hold at all tower levels 0..n-1.
pub open spec fn tower_textbook_chain(data: HNNData, n: nat) -> bool {
    forall|k: nat| k < n ==> #[trigger] tower_textbook_prereqs_at(data, k)
}

///  Textbook tower embedding: G_0 embeds in tower(n) via one-shot AFP injectivity.
///  Same structure as lemma_g0_embeds_in_tower but with simpler prerequisites.
pub proof fn lemma_g0_embeds_in_tower_textbook(
    data: HNNData, n: nat, w: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(tower_presentation(data, n), w, empty_word()),
        tower_textbook_chain(data, n),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
    decreases n,
{
    if n == 0 {
    } else {
        let prev = (n - 1) as nat;
        let ng = data.base.num_generators;
        let afp_data = tower_afp_data(data, prev);

        lemma_tower_num_generators(data, prev);
        assert(ng <= n * ng) by (nonlinear_arith) requires n >= 1;
        lemma_word_valid_weaken(w, ng, n * ng);

        lemma_tower_valid(data, prev);
        lemma_tower_afp_data_valid(data, prev);

        //  Textbook AFP injectivity at level prev
        assert(tower_textbook_prereqs_at(data, prev));
        crate::normal_form_afp_textbook::lemma_afp_injectivity(afp_data, w);

        //  IH
        assert(tower_textbook_chain(data, prev)) by {
            assert forall|k: nat| k < prev
                implies #[trigger] tower_textbook_prereqs_at(data, k)
            by { assert(k < n); }
        }
        lemma_g0_embeds_in_tower_textbook(data, prev, w);
    }
}

} //  verus!


//  ================================================================
//  FILE: britton_via_tower.rs
//  ================================================================

//  Britton's Lemma via Tower Construction
//
//  Translates HNN extension derivations to tower derivations.
//  Faithful to Lyndon-Schupp Chapter IV: the tower unfolds the HNN extension
//  by replacing the stable letter with explicit copies of the base group.
//
//  Key insight: the HNN relator t⁻¹·a_i·t·inv(b_i) at level k corresponds
//  exactly to the AFP identification relator shift(a_i, (k-1)·ng)·inv(shift(b_i, k·ng))
//  at tower junction (k-1)↔k.

use vstd::prelude::*;
use crate::symbol::*;
use crate::word::*;
use crate::presentation::*;
use crate::presentation_lemmas::*;
use crate::free_product::*;
use crate::amalgamated_free_product::*;
use crate::reduction::*;
use crate::benign::*;
use crate::hnn::*;
use crate::tower::*;

verus! {

///  The HNN presentation is a valid presentation.
///  (Inlined from britton_proof.rs to avoid pulling in the 14k-line file.)
proof fn lemma_hnn_presentation_valid(data: HNNData)
    requires
        hnn_data_valid(data),
    ensures
        presentation_valid(hnn_presentation(data)),
{
    reveal(presentation_valid);
    let hp = hnn_presentation(data);
    let n = data.base.num_generators;

    assert forall|i: int| #![trigger hp.relators[i]]
        0 <= i < hp.relators.len()
        implies word_valid(hp.relators[i], hp.num_generators)
    by {
        let base_len = data.base.relators.len() as int;
        if i < base_len {
            assert(hp.relators[i] == data.base.relators[i]);
            assert(word_valid(data.base.relators[i], n));
            assert forall|j: int| 0 <= j < hp.relators[i].len()
                implies symbol_valid(#[trigger] hp.relators[i][j], hp.num_generators)
            by {
                assert(symbol_valid(hp.relators[i][j], n));
                match hp.relators[i][j] {
                    Symbol::Gen(idx) => {}
                    Symbol::Inv(idx) => {}
                }
            }
        } else {
            let k = (i - base_len);
            let (a_k, b_k) = data.associations[k];
            assert(word_valid(a_k, n));
            assert(word_valid(b_k, n));
            lemma_inverse_word_valid(b_k, n);
            let r = hp.relators[i];
            assert forall|j: int| 0 <= j < r.len()
                implies symbol_valid(#[trigger] r[j], n + 1)
            by {
                if j == 0 {
                } else if (j as int) < 1 + a_k.len() {
                    let aj = (j - 1) as int;
                    assert(symbol_valid(a_k[aj], n));
                    match a_k[aj] { Symbol::Gen(idx) => {} Symbol::Inv(idx) => {} }
                } else if j == 1 + a_k.len() {
                } else {
                    let inv_bk = inverse_word(b_k);
                    let bj = (j - 2 - a_k.len()) as int;
                    assert(symbol_valid(inv_bk[bj], n));
                    match inv_bk[bj] { Symbol::Gen(idx) => {} Symbol::Inv(idx) => {} }
                }
            }
        }
    }
}

//  ============================================================
//  Part A: Level tracking and word translation
//  ============================================================

///  Whether symbol s is the stable letter t or t⁻¹.
pub open spec fn is_stable(data: HNNData, s: Symbol) -> bool {
    let ng = data.base.num_generators;
    s == Symbol::Gen(ng) || s == Symbol::Inv(ng)
}

///  Net level change of a word: count of t minus count of t⁻¹.
pub open spec fn net_level(data: HNNData, w: Word) -> int
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
        0
    } else {
        let s = w.first();
        let rest_level = net_level(data, w.drop_first());
        if s == Symbol::Gen(ng) {
            1 + rest_level
        } else if s == Symbol::Inv(ng) {
            -1 + rest_level
        } else {
            rest_level
        }
    }
}

///  Translate an HNN word to a tower word, starting at a given base level.
///  - Stable letters are REMOVED (encode level changes)
///  - Base symbol at current level k becomes shifted by k·ng
///  - base_level tracks the accumulated level from earlier context
pub open spec fn translate_word_at(data: HNNData, w: Word, base_level: int) -> Word
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
        empty_word()
    } else {
        let s = w.first();
        let rest = w.drop_first();
        if s == Symbol::Gen(ng) {
            //  t: level +1, skip symbol
            translate_word_at(data, rest, base_level + 1)
        } else if s == Symbol::Inv(ng) {
            //  t⁻¹: level -1, skip symbol
            translate_word_at(data, rest, base_level - 1)
        } else {
            //  Base symbol: shift by base_level · ng, include in output
            let shifted_s = match s {
                Symbol::Gen(i) => Symbol::Gen((i + base_level * ng) as nat),
                Symbol::Inv(i) => Symbol::Inv((i + base_level * ng) as nat),
            };
            concat(Seq::new(1, |_j: int| shifted_s),
                translate_word_at(data, rest, base_level))
        }
    }
}

///  Top-level translation: start at level 0.
pub open spec fn translate_word(data: HNNData, w: Word) -> Word {
    translate_word_at(data, w, 0)
}

//  ============================================================
//  Part B: Base word translation = identity
//  ============================================================

///  A base word has net level 0.
proof fn lemma_base_word_net_level_zero(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        net_level(data, w) == 0,
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
        lemma_base_word_net_level_zero(data, w.drop_first());
    }
}

///  A base word translates to itself at level 0.
pub proof fn lemma_translate_base_word(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        translate_word(data, w) =~= w,
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); assert(!is_stable(data, s)); }
            Symbol::Inv(i) => { assert(i < ng); assert(!is_stable(data, s)); }
        }
        assert(word_valid(w.drop_first(), ng));
        lemma_translate_base_word(data, w.drop_first());
    }
}

///  The empty word translates to the empty word.
pub proof fn lemma_translate_empty(data: HNNData)
    ensures translate_word(data, empty_word()) =~= empty_word(),
{
}

//  ============================================================
//  Part C: Concat decomposition for translate_word_at
//  ============================================================

///  translate_word_at distributes over concat (with level offset).
pub proof fn lemma_translate_concat(data: HNNData, w1: Word, w2: Word, base_level: int)
    ensures
        translate_word_at(data, concat(w1, w2), base_level)
            =~= concat(translate_word_at(data, w1, base_level),
                        translate_word_at(data, w2, base_level + net_level(data, w1))),
    decreases w1.len(),
{
    let ng = data.base.num_generators;
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
        assert(net_level(data, w1) == 0);
        assert(translate_word_at(data, w1, base_level) =~= empty_word());
    } else {
        let s = w1.first();
        let rest1 = w1.drop_first();
        assert(concat(w1, w2).first() == s);
        assert(concat(w1, w2).drop_first() =~= concat(rest1, w2));

        if s == Symbol::Gen(ng) {
            lemma_translate_concat(data, rest1, w2, base_level + 1);
        } else if s == Symbol::Inv(ng) {
            lemma_translate_concat(data, rest1, w2, base_level - 1);
        } else {
            lemma_translate_concat(data, rest1, w2, base_level);
        }
    }
}

//  ============================================================
//  Part D: Derivation lifting — equiv in p1 → equiv in free_product(p1, p2)
//  ============================================================

///  A single derivation step valid in p1 is also valid in free_product(p1, p2).
proof fn lemma_step_valid_in_fp_left(
    p1: Presentation, p2: Presentation,
    w: Word, step: DerivationStep,
)
    requires
        apply_step(p1, w, step) is Some,
    ensures
        apply_step(free_product(p1, p2), w, step) == apply_step(p1, w, step),
{
    let fp = free_product(p1, p2);
    match step {
        DerivationStep::FreeReduce { position } => {},
        DerivationStep::FreeExpand { position, symbol } => {
            assert(symbol_valid(symbol, fp.num_generators)) by {
                match symbol {
                    Symbol::Gen(i) => {}
                    Symbol::Inv(i) => {}
                }
            }
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            assert(fp.relators[relator_index as int] == p1.relators[relator_index as int]);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            assert(fp.relators[relator_index as int] == p1.relators[relator_index as int]);
        },
    }
}

///  A full derivation valid in p1 is also valid in free_product(p1, p2).
proof fn lemma_derivation_valid_in_fp_left(
    p1: Presentation, p2: Presentation,
    steps: Seq<DerivationStep>, w1: Word, w2: Word,
)
    requires
        derivation_produces(p1, steps, w1) == Some(w2),
    ensures
        derivation_produces(free_product(p1, p2), steps, w1) == Some(w2),
    decreases steps.len(),
{
    if steps.len() == 0 {
    } else {
        let w_mid = apply_step(p1, w1, steps.first()).unwrap();
        lemma_step_valid_in_fp_left(p1, p2, w1, steps.first());
        lemma_derivation_valid_in_fp_left(p1, p2, steps.drop_first(), w_mid, w2);
    }
}

///  Equivalence in p1 implies equivalence in free_product(p1, p2).
pub proof fn lemma_left_embeds_in_fp(
    p1: Presentation, p2: Presentation, w1: Word, w2: Word,
)
    requires
        equiv_in_presentation(p1, w1, w2),
    ensures
        equiv_in_presentation(free_product(p1, p2), w1, w2),
{
    let d: Derivation = choose|d: Derivation| derivation_valid(p1, d, w1, w2);
    lemma_derivation_valid_in_fp_left(p1, p2, d.steps, w1, w2);
    let d_fp = Derivation { steps: d.steps };
    assert(derivation_valid(free_product(p1, p2), d_fp, w1, w2));
}

///  Equivalence in tower(k) implies equivalence in tower(m) for k ≤ m.
pub proof fn lemma_tower_monotone(
    data: HNNData, k: nat, m: nat, w1: Word, w2: Word,
)
    requires
        hnn_data_valid(data),
        k <= m,
        equiv_in_presentation(tower_presentation(data, k), w1, w2),
    ensures
        equiv_in_presentation(tower_presentation(data, m), w1, w2),
    decreases m - k,
{
    if k == m {
    } else {
        let afp_data = tower_afp_data(data, k);
        lemma_left_embeds_in_fp(afp_data.p1, afp_data.p2, w1, w2);
        crate::quotient::lemma_add_relators_preserves_equiv(
            free_product(afp_data.p1, afp_data.p2),
            amalgamation_relators(afp_data), w1, w2);
        lemma_tower_monotone(data, k + 1, m, w1, w2);
    }
}

//  ============================================================
//  Part E: Tower relator correspondence
//  ============================================================

///  A base relator at copy k is equiv to ε in tower(m) when k ≤ m.
pub proof fn lemma_base_relator_in_tower(
    data: HNNData, m: nat, k: nat, r: int,
)
    requires
        hnn_data_valid(data),
        k <= m,
        0 <= r < data.base.relators.len(),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            shift_word(data.base.relators[r], k * data.base.num_generators),
            empty_word()),
    decreases m,
{
    let ng = data.base.num_generators;
    if k == 0 && m == 0 {
        assert(shift_word(data.base.relators[r], 0) =~= data.base.relators[r]);
        lemma_relator_is_identity(data.base, r);
    } else if k < m {
        if k == 0 {
            assert(shift_word(data.base.relators[r], 0) =~= data.base.relators[r]);
            lemma_relator_is_identity(data.base, r);
            lemma_tower_monotone(data, 0, m, data.base.relators[r], empty_word());
        } else {
            lemma_base_relator_in_tower(data, (m - 1) as nat, k, r);
            lemma_tower_monotone(data, (m - 1) as nat, m,
                shift_word(data.base.relators[r], k * ng), empty_word());
        }
    } else {
        //  k == m > 0: relator in the new copy (right factor)
        let prev = (m - 1) as nat;
        let afp_data = tower_afp_data(data, prev);
        let fp = free_product(afp_data.p1, afp_data.p2);
        lemma_tower_num_generators(data, prev);
        let fp_idx = (afp_data.p1.relators.len() + r) as nat;
        assert(fp.relators[fp_idx as int]
            == shift_word(data.base.relators[r], m * ng));
        lemma_relator_is_identity(fp, fp_idx as int);
        crate::quotient::lemma_add_relators_preserves_equiv(
            fp, amalgamation_relators(afp_data),
            shift_word(data.base.relators[r], m * ng), empty_word());
    }
}

///  An identification relator at junction k↔k+1 is equiv to ε in tower(m) when k+1 ≤ m.
pub proof fn lemma_ident_relator_in_tower(
    data: HNNData, m: nat, k: nat, i: int,
)
    requires
        hnn_data_valid(data),
        k + 1 <= m,
        0 <= i < data.associations.len() as int,
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            amalgamation_relator(tower_afp_data(data, k), i),
            empty_word()),
    decreases m,
{
    let prev = (m - 1) as nat;
    let afp_data = tower_afp_data(data, prev);
    let fp = free_product(afp_data.p1, afp_data.p2);

    if k == prev {
        crate::quotient::lemma_each_added_relator_is_identity(
            fp, amalgamation_relators(afp_data), i);
    } else {
        lemma_ident_relator_in_tower(data, prev, k, i);
        lemma_tower_monotone(data, prev, m,
            amalgamation_relator(tower_afp_data(data, k), i), empty_word());
    }
}

//  ============================================================
//  Part F: Context insertion — if r ≡ ε, then prefix·suffix ≡ prefix·r·suffix
//  ============================================================

///  If r ≡ ε, then prefix·r·suffix ≡ prefix·suffix (deletion direction).
pub proof fn lemma_delete_equiv_empty(
    p: Presentation, prefix: Word, r: Word, suffix: Word,
)
    requires
        equiv_in_presentation(p, r, empty_word()),
    ensures
        equiv_in_presentation(p, concat(prefix, concat(r, suffix)),
            concat(prefix, suffix)),
{
    //  r ≡ ε → concat(r, suffix) ≡ concat(ε, suffix) =~= suffix
    lemma_equiv_concat_left(p, r, empty_word(), suffix);
    //  concat(prefix, concat(r, suffix)) ≡ concat(prefix, suffix)
    lemma_equiv_concat_right(p, prefix, concat(r, suffix), suffix);
}

///  If r ≡ ε, then prefix·suffix ≡ prefix·r·suffix (insertion direction).
///  Requires symmetry infrastructure (word_valid + presentation_valid).
pub proof fn lemma_insert_equiv_empty(
    p: Presentation, prefix: Word, r: Word, suffix: Word,
)
    requires
        equiv_in_presentation(p, r, empty_word()),
        presentation_valid(p),
        word_valid(r, p.num_generators),
    ensures
        equiv_in_presentation(p, concat(prefix, suffix),
            concat(prefix, concat(r, suffix))),
{
    //  ε ≡ r (by symmetry)
    crate::presentation::lemma_equiv_symmetric(p, r, empty_word());
    //  concat(ε, suffix) ≡ concat(r, suffix) → suffix ≡ concat(r, suffix)
    lemma_equiv_concat_left(p, empty_word(), r, suffix);
    //  concat(prefix, suffix) ≡ concat(prefix, concat(r, suffix))
    lemma_equiv_concat_right(p, prefix, suffix, concat(r, suffix));
}

//  ============================================================
//  Part G: Translation of base words at arbitrary level
//  ============================================================

///  A base word at level L translates to shift_word(w, L * ng).
pub proof fn lemma_translate_base_word_at(data: HNNData, w: Word, base_level: nat)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        translate_word_at(data, w, base_level as int)
            =~= shift_word(w, base_level * data.base.num_generators),
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
        lemma_translate_base_word_at(data, w.drop_first(), base_level);
    }
}

///  A single stable letter translates to empty at any level.
proof fn lemma_translate_stable_empty(data: HNNData, s: Symbol, base_level: int)
    requires is_stable(data, s),
    ensures
        translate_word_at(data, Seq::new(1, |_j: int| s), base_level) =~= empty_word(),
{
    let w = Seq::new(1, |_j: int| s);
    assert(w.first() == s);
    assert(w.drop_first() =~= Seq::<Symbol>::empty());
    reveal_with_fuel(translate_word_at, 2);
}

///  Net level of a base word is 0.
proof fn lemma_net_level_base_word(data: HNNData, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        net_level(data, w) == 0,
    decreases w.len(),
{
    let ng = data.base.num_generators;
    if w.len() == 0 {
    } else {
        let s = w.first();
        assert(symbol_valid(s, ng));
        match s {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
        lemma_net_level_base_word(data, w.drop_first());
    }
}

///  Net level of a single stable letter.
proof fn lemma_net_level_stable(data: HNNData, s: Symbol)
    requires is_stable(data, s),
    ensures
        net_level(data, Seq::new(1, |_j: int| s)) ==
            (if s == Symbol::Gen(data.base.num_generators) { 1int } else { -1int }),
{
    let w = Seq::new(1, |_j: int| s);
    assert(w.first() == s);
    assert(w.drop_first() =~= Seq::<Symbol>::empty());
    reveal_with_fuel(net_level, 2);
}

///  Net level distributes over concat.
pub proof fn lemma_net_level_concat(data: HNNData, w1: Word, w2: Word)
    ensures
        net_level(data, concat(w1, w2)) == net_level(data, w1) + net_level(data, w2),
    decreases w1.len(),
{
    if w1.len() == 0 {
        assert(concat(w1, w2) =~= w2);
    } else {
        assert(concat(w1, w2).first() == w1.first());
        assert(concat(w1, w2).drop_first() =~= concat(w1.drop_first(), w2));
        lemma_net_level_concat(data, w1.drop_first(), w2);
    }
}

//  ============================================================
//  Part H: HNN relator translates to identification relator
//  ============================================================

///  The HNN relator t⁻¹·a_i·t·inv(b_i) at level k translates to
///  the AFP identification relator at junction (k-1)↔k.
///
///  This is the textbook correspondence (Lyndon-Schupp Ch. IV):
///  each HNN relation at level k becomes an identification relation
///  between copy k-1 and copy k in the tower.
pub proof fn lemma_translate_hnn_relator(
    data: HNNData, i: int, k: int,
)
    requires
        hnn_data_valid(data),
        0 <= i < data.associations.len() as int,
        k >= 1,
    ensures ({
        let ng = data.base.num_generators;
        let r = hnn_relator(data, i);
        let afp_data = tower_afp_data(data, (k - 1) as nat);
        translate_word_at(data, r, k)
            =~= amalgamation_relator(afp_data, i)
    }),
{
    let ng = data.base.num_generators;
    let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
    let t_inv = Seq::new(1, |_j: int| Symbol::Inv(ng));
    let t_gen = Seq::new(1, |_j: int| Symbol::Gen(ng));

    //  r = concat(part1, part2) where part1 = concat(t_inv, a_i), part2 = concat(t_gen, inv(b_i))
    let part1 = concat(t_inv, a_i);
    let part2 = concat(t_gen, inverse_word(b_i));

    //  Step 1: decompose r = concat(part1, part2)
    lemma_translate_concat(data, part1, part2, k);

    //  Step 2: net_level(part1) = -1 (t⁻¹ contributes -1, a_i contributes 0)
    lemma_net_level_concat(data, t_inv, a_i);
    lemma_net_level_stable(data, Symbol::Inv(ng));
    lemma_net_level_base_word(data, a_i);
    assert(net_level(data, part1) == -1);

    //  Step 3: translate(part1, k) =~= shift(a_i, (k-1)*ng)
    lemma_translate_concat(data, t_inv, a_i, k);
    lemma_net_level_stable(data, Symbol::Inv(ng));
    lemma_translate_stable_empty(data, Symbol::Inv(ng), k);
    lemma_translate_base_word_at(data, a_i, (k - 1) as nat);

    //  Step 4: translate(part2, k-1) =~= shift(inv(b_i), k*ng)
    lemma_translate_concat(data, t_gen, inverse_word(b_i), k - 1);
    lemma_net_level_stable(data, Symbol::Gen(ng));
    lemma_translate_stable_empty(data, Symbol::Gen(ng), k - 1);
    crate::word::lemma_inverse_word_valid(b_i, ng);
    lemma_translate_base_word_at(data, inverse_word(b_i), k as nat);

    //  Intermediate assertions to chain the =~= results
    assert(translate_word_at(data, part1, k)
        =~= shift_word(a_i, ((k - 1) as nat) * ng));
    assert(translate_word_at(data, part2, k - 1)
        =~= shift_word(inverse_word(b_i), k as nat * ng));

    //  Step 5: shift(inv(b_i), k*ng) =~= inv(shift(b_i, k*ng))
    crate::free_product::lemma_shift_inverse_word(b_i, k as nat * ng);

    //  Step 6: connect to amalgamation_relator
    lemma_tower_num_generators(data, (k - 1) as nat);
    assert(translate_word_at(data, part2, k - 1)
        =~= inverse_word(shift_word(b_i, k as nat * ng)));

    //  Connect hnn_relator to concat(part1, part2)
    assert(hnn_relator(data, i) =~= concat(part1, part2));

    //  Final chain
    assert(translate_word_at(data, concat(part1, part2), k)
        =~= concat(shift_word(a_i, ((k - 1) as nat) * ng),
                    inverse_word(shift_word(b_i, k as nat * ng))));
}

//  ============================================================
//  Part I: General middle-deletion lemma for translation
//  ============================================================

///  If the translated middle ≡ ε in tower and net_level(middle) == 0,
///  then translate(prefix · middle · suffix) ≡ translate(prefix · suffix) in tower.
///
///  This handles ALL step types uniformly:
///  - FreeReduce/Delete: w = prefix · middle · suffix → w' = prefix · suffix
///  - FreeExpand/Insert: w = prefix · suffix → w' = prefix · middle · suffix (reverse direction)
pub proof fn lemma_translate_delete_middle(
    data: HNNData, m: nat, base_level: int,
    prefix: Word, middle: Word, suffix: Word,
)
    requires
        hnn_data_valid(data),
        net_level(data, middle) == 0,
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, middle, base_level + net_level(data, prefix)),
            empty_word()),
        presentation_valid(tower_presentation(data, m)),
        word_valid(translate_word_at(data, middle, base_level + net_level(data, prefix)),
            tower_presentation(data, m).num_generators),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, concat(prefix, concat(middle, suffix)), base_level),
            translate_word_at(data, concat(prefix, suffix), base_level)),
{
    let tp = tower_presentation(data, m);
    let lp = base_level + net_level(data, prefix);

    //  Decompose translate of w = prefix · middle · suffix
    lemma_translate_concat(data, prefix, concat(middle, suffix), base_level);
    lemma_translate_concat(data, middle, suffix, lp);
    lemma_net_level_concat(data, prefix, concat(middle, suffix));
    lemma_net_level_concat(data, middle, suffix);

    //  Decompose translate of w' = prefix · suffix
    lemma_translate_concat(data, prefix, suffix, base_level);

    let tr_prefix = translate_word_at(data, prefix, base_level);
    let tr_middle = translate_word_at(data, middle, lp);
    let tr_suffix = translate_word_at(data, suffix, lp);

    lemma_delete_equiv_empty(tp, tr_prefix, tr_middle, tr_suffix);
}

///  Reverse direction: translate(prefix · suffix) ≡ translate(prefix · middle · suffix).
///  Needs symmetry infrastructure.
pub proof fn lemma_translate_insert_middle(
    data: HNNData, m: nat, base_level: int,
    prefix: Word, middle: Word, suffix: Word,
)
    requires
        hnn_data_valid(data),
        net_level(data, middle) == 0,
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, middle, base_level + net_level(data, prefix)),
            empty_word()),
        presentation_valid(tower_presentation(data, m)),
        word_valid(translate_word_at(data, middle, base_level + net_level(data, prefix)),
            tower_presentation(data, m).num_generators),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, concat(prefix, suffix), base_level),
            translate_word_at(data, concat(prefix, concat(middle, suffix)), base_level)),
{
    let tp = tower_presentation(data, m);
    let lp = base_level + net_level(data, prefix);

    lemma_translate_concat(data, prefix, concat(middle, suffix), base_level);
    lemma_translate_concat(data, middle, suffix, lp);
    lemma_net_level_concat(data, prefix, concat(middle, suffix));
    lemma_net_level_concat(data, middle, suffix);
    lemma_translate_concat(data, prefix, suffix, base_level);

    let tr_prefix = translate_word_at(data, prefix, base_level);
    let tr_middle = translate_word_at(data, middle, lp);
    let tr_suffix = translate_word_at(data, suffix, lp);

    lemma_insert_equiv_empty(tp, tr_prefix, tr_middle, tr_suffix);
}

//  ============================================================
//  Part J: Specific middle ≡ ε results
//  ============================================================

///  A stable inverse pair translates to ε (=~=, not just ≡).
proof fn lemma_translate_stable_pair(data: HNNData, s: Symbol, base_level: int)
    requires
        is_stable(data, s),
    ensures
        translate_word_at(data,
            concat(Seq::new(1, |_j: int| s), Seq::new(1, |_j: int| inverse_symbol(s))),
            base_level)
            =~= empty_word(),
        net_level(data,
            concat(Seq::new(1, |_j: int| s), Seq::new(1, |_j: int| inverse_symbol(s))))
            == 0,
{
    let s_word = Seq::new(1, |_j: int| s);
    let inv_s_word = Seq::new(1, |_j: int| inverse_symbol(s));
    let pair = concat(s_word, inv_s_word);

    lemma_translate_concat(data, s_word, inv_s_word, base_level);
    lemma_net_level_concat(data, s_word, inv_s_word);
    lemma_net_level_stable(data, s);

    //  inverse_symbol of stable is also stable
    let ng = data.base.num_generators;
    assert(is_stable(data, inverse_symbol(s))) by {
        if s == Symbol::Gen(ng) {
            assert(inverse_symbol(s) == Symbol::Inv(ng));
        } else {
            assert(inverse_symbol(s) == Symbol::Gen(ng));
        }
    }
    lemma_translate_stable_empty(data, s, base_level);
    lemma_net_level_stable(data, inverse_symbol(s));

    if s == Symbol::Gen(ng) {
        lemma_translate_stable_empty(data, inverse_symbol(s), base_level + 1);
    } else {
        lemma_translate_stable_empty(data, inverse_symbol(s), base_level - 1);
    }
}

//  ============================================================
//  Part G2: Base at copy k embeds in tower via shift homomorphism
//  ============================================================

///  Shift homomorphism: base → tower(m), mapping Gen(i) → [Gen(i + k*ng)].
pub open spec fn shift_hom(data: HNNData, m: nat, k: nat) -> crate::homomorphism::HomomorphismData {
    let ng = data.base.num_generators;
    crate::homomorphism::HomomorphismData {
        source: data.base,
        target: tower_presentation(data, m),
        generator_images: Seq::new(ng, |i: int| Seq::new(1, |_j: int| Symbol::Gen((i + k * ng) as nat))),
    }
}

///  The shift homomorphism maps words to their shifted versions.
#[verifier::rlimit(200)]
proof fn lemma_shift_hom_applies(data: HNNData, k: nat, m: nat, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
    ensures
        crate::homomorphism::apply_hom(shift_hom(data, m, k), w)
            =~= shift_word(w, k * data.base.num_generators),
    decreases w.len(),
{
    let h = shift_hom(data, m, k);
    let ng = data.base.num_generators;
    let result = crate::homomorphism::apply_hom(h, w);
    let shifted = shift_word(w, k * ng);
    if w.len() == 0 {
        assert(result.len() == 0);
        assert(shifted.len() == 0);
    } else {
        lemma_shift_hom_applies(data, k, m, w.drop_first());
        //  IH: apply_hom(h, rest) =~= shift_word(rest, k*ng)
        //  result = concat(apply_hom_symbol(h, w.first()), apply_hom(h, rest))
        //  shifted = Seq::new(w.len(), |j| shift_symbol(w[j], k*ng))
        //  Element-wise: result[0] == shifted[0] and result[j] == shifted[j] for j > 0

        //  The result has same length as shifted
        let s = w.first();
        assert(symbol_valid(s, ng));
        let sym_img = crate::homomorphism::apply_hom_symbol(h, s);
        //  For both Gen and Inv: sym_img is a 1-element word = [shift_symbol(s, k*ng)]
        match s {
            Symbol::Gen(i) => {
                assert(sym_img.len() == 1);
                assert(sym_img[0] == shift_symbol(s, k * ng));
            }
            Symbol::Inv(i) => {
                //  sym_img = inverse_word([Gen(i+k*ng)]) = [Inv(i+k*ng)]
                let gen_img = h.generator_images[i as int];
                assert(gen_img.len() == 1);
                assert(gen_img[0] == Symbol::Gen((i + k * ng) as nat));
                //  inverse_word definition: Seq::new(w.len(), |j| inverse_symbol(w[w.len()-1-j]))
                //  For len=1: Seq::new(1, |j| inverse_symbol(gen_img[0])) = [Inv(i+k*ng)]
                crate::word::lemma_inverse_word_len(gen_img);
                assert(sym_img.len() == 1);
                assert(sym_img[0] == shift_symbol(s, k * ng));
            }
        }
    }
}

///  The shift homomorphism is valid: relator images ≡ ε in tower(m).
proof fn lemma_shift_hom_valid(data: HNNData, m: nat, k: nat)
    requires
        hnn_data_valid(data),
        k <= m,
    ensures
        crate::homomorphism::is_valid_homomorphism(shift_hom(data, m, k)),
{
    let h = shift_hom(data, m, k);
    let ng = data.base.num_generators;
    reveal(presentation_valid);
    lemma_tower_valid(data, m);
    lemma_tower_num_generators(data, m);

    //  Generator images are word_valid for tower(m)
    assert forall|i: int| 0 <= i < h.generator_images.len()
        implies word_valid(h.generator_images[i], h.target.num_generators)
    by {
        assert(h.generator_images[i].len() == 1);
        assert((i + k * ng) < (m + 1) * ng) by (nonlinear_arith)
            requires i < ng as int, k <= m;
    }

    //  Relator images ≡ ε: shift(relator, k*ng) ≡ ε in tower(m)
    assert forall|i: int| 0 <= i < h.source.relators.len()
        implies equiv_in_presentation(h.target,
            crate::homomorphism::apply_hom(h, h.source.relators[i]), empty_word())
    by {
        lemma_shift_hom_applies(data, k, m, h.source.relators[i]);
        //  apply_hom(h, relator) =~= shift(relator, k*ng)
        lemma_base_relator_in_tower(data, m, k, i);
        //  shift(relator, k*ng) ≡ ε in tower(m)
    }
}

///  Base at copy k embeds in tower(m): equiv(base, w1, w2) → equiv(tower(m), shift(w1, k*ng), shift(w2, k*ng)).
pub proof fn lemma_base_at_copy_k_embeds(
    data: HNNData, m: nat, k: nat, w1: Word, w2: Word,
)
    requires
        hnn_data_valid(data),
        k <= m,
        word_valid(w1, data.base.num_generators),
        word_valid(w2, data.base.num_generators),
        equiv_in_presentation(data.base, w1, w2),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            shift_word(w1, k * data.base.num_generators),
            shift_word(w2, k * data.base.num_generators)),
{
    lemma_shift_hom_valid(data, m, k);
    crate::homomorphism::lemma_hom_preserves_equiv(shift_hom(data, m, k), w1, w2);
    lemma_shift_hom_applies(data, k, m, w1);
    lemma_shift_hom_applies(data, k, m, w2);
}

//  Tower identifications_isomorphic from hnn_associations_isomorphic.
//
//  Proof uses:
//  - Backward: base_at_copy_k_embeds (shift homomorphism)
//  - Forward: lemma_afp_injectivity_right (G₂ one-shot)
//  - shift-embedding distributivity for Seq::new closure matching

///  Shift-embedding distributivity: embedding with shifted images = shift of embedding.
///  apply_embedding(shift_each(images, offset), w) =~= shift(apply_embedding(images, w), offset)
///  Shift-embedding distributivity: embedding with shifted images = shift of embedding.
///  Takes shifted_images as parameter to avoid Seq::new closure mismatch in ensures.
proof fn lemma_shift_embedding_distributes(
    images: Seq<Word>, shifted_images: Seq<Word>, w: Word, offset: nat,
)
    requires
        shifted_images.len() == images.len(),
        word_valid(w, images.len()),
        forall|i: int| 0 <= i < images.len() ==>
            #[trigger] shifted_images[i] =~= shift_word(images[i], offset),
    ensures
        apply_embedding(shifted_images, w)
            =~= shift_word(apply_embedding(images, w), offset),
    decreases w.len(),
{
    if w.len() == 0 {
    } else {
        lemma_shift_embedding_distributes(images, shifted_images, w.drop_first(), offset);
        let s = w.first();
        crate::free_product::lemma_shift_concat(
            apply_embedding_symbol(images, s),
            apply_embedding(images, w.drop_first()), offset);
        //  Trigger the forall for the specific symbol index and establish symbol-level =~=
        match s {
            Symbol::Gen(i) => {
                assert(shifted_images[i as int] =~= shift_word(images[i as int], offset));
            }
            Symbol::Inv(i) => {
                assert(shifted_images[i as int] =~= shift_word(images[i as int], offset));
                crate::free_product::lemma_shift_inverse_word(images[i as int], offset);
            }
        }
    }
}

///  Tower identifications_isomorphic from hnn_associations_isomorphic.
///  Uses shift-embedding distributivity + AFP right-injectivity + base_at_copy_k_embeds.
#[verifier::rlimit(300)]
///  Forward: tower(k) equiv → base equiv for embed_a_hnn.
proof fn lemma_tower_iso_forward_mid(
    data: HNNData, k: nat, embed_a_hnn: Word,
)
    requires
        hnn_data_valid(data),
        tower_textbook_chain(data, k),
        word_valid(embed_a_hnn, data.base.num_generators),
        equiv_in_presentation(tower_presentation(data, k),
            shift_word(embed_a_hnn, k * data.base.num_generators), empty_word()),
    ensures
        equiv_in_presentation(data.base, embed_a_hnn, empty_word()),
{
    let ng = data.base.num_generators;
    reveal(presentation_valid);
    if k == 0 {
        //  tower(0) = base, shift by 0 = identity
        assert(k * ng == 0) by (nonlinear_arith) requires k == 0;
        assert(shift_word(embed_a_hnn, 0nat) =~= embed_a_hnn);
    } else {
        assert(tower_textbook_prereqs_at(data, (k - 1) as nat));
        lemma_tower_afp_data_valid(data, (k - 1) as nat);
        lemma_tower_valid(data, (k - 1) as nat);
        lemma_tower_num_generators(data, (k - 1) as nat);
        crate::normal_form_afp_textbook::lemma_afp_injectivity_right(
            tower_afp_data(data, (k - 1) as nat), embed_a_hnn);
    }
}

///  Backward: base equiv → tower(k) equiv for embed_a_hnn.
proof fn lemma_tower_iso_backward_mid(
    data: HNNData, k: nat, embed_a_hnn: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(embed_a_hnn, data.base.num_generators),
        equiv_in_presentation(data.base, embed_a_hnn, empty_word()),
    ensures
        equiv_in_presentation(tower_presentation(data, k),
            shift_word(embed_a_hnn, k * data.base.num_generators), empty_word()),
{
    //  shift(ε, k*ng) =~= ε
    assert(shift_word(empty_word(), k * data.base.num_generators) =~= empty_word());
    lemma_base_at_copy_k_embeds(data, k, k, embed_a_hnn, empty_word());
}

//  lemma_tower_iso_per_word: per-word biconditional for tower isomorphism.
//  Logic complete (forward via AFP right-injectivity + hnn_iso, backward via base_at_copy_k_embeds + hnn_iso).
//  Z3 engineering: needs explicit assertion chain connecting AFP right-injectivity output
//  (equiv(tower_afp_data(k-1).p2, embed_a_hnn, ε)) to equiv(data.base, embed_a_hnn, ε)
//  and shift(embed_a_hnn, k*ng) to embed_a_tower. ~10 more lines of intermediate assertions.
//
//  All building blocks verified (0 assumes):
//  - lemma_afp_injectivity_right ✓
//  - lemma_base_at_copy_k_embeds ✓ (shift homomorphism)
//  - lemma_shift_embedding_distributes ✓
//  - hnn_associations_isomorphic ✓ (precondition)

///  Helper: per-word proof of the tower isomorphism biconditional.
#[verifier::rlimit(1000)]
proof fn lemma_tower_iso_per_word(
    data: HNNData, k: nat, w: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        tower_textbook_chain(data, k),
        word_valid(w, data.associations.len() as nat),
    ensures ({
        let afp_data = tower_afp_data(data, k);
        let a_words_tower = Seq::new(afp_data.identifications.len(), |i: int| afp_data.identifications[i].0);
        let b_words_tower = Seq::new(afp_data.identifications.len(), |i: int| afp_data.identifications[i].1);
        equiv_in_presentation(afp_data.p1, apply_embedding(a_words_tower, w), empty_word())
        <==>
        equiv_in_presentation(afp_data.p2, apply_embedding(b_words_tower, w), empty_word())
    }),
{
    let ng = data.base.num_generators;
    let afp_data = tower_afp_data(data, k);
    let kk = data.associations.len();
    reveal(presentation_valid);

    assert(afp_data.identifications.len() == kk);
    let a_words_hnn = Seq::new(kk, |i: int| data.associations[i].0);
    let b_words_hnn = Seq::new(kk, |i: int| data.associations[i].1);
    //  EXACTLY match ensures clause's Seq::new (same length expression)
    let a_words_tower = Seq::new(afp_data.identifications.len(), |i: int| afp_data.identifications[i].0);
    let b_words_tower = Seq::new(afp_data.identifications.len(), |i: int| afp_data.identifications[i].1);

    //  Element-wise: a_words_tower[i] = shift(a_words_hnn[i], k*ng) and b_words_tower[i] = b_words_hnn[i]
    assert forall|i: int| 0 <= i < kk implies
        afp_data.identifications[i].1 == data.associations[i].1 by {}
    assert forall|i: int| 0 <= i < kk implies
        #[trigger] b_words_tower[i] =~= b_words_hnn[i] by {}
    assert(b_words_tower =~= b_words_hnn);

    //  Shift-embedding distributivity
    assert forall|i: int| 0 <= i < a_words_hnn.len() implies
        #[trigger] a_words_tower[i] =~= shift_word(a_words_hnn[i], k * ng) by {}
    lemma_shift_embedding_distributes(a_words_hnn, a_words_tower, w, k * ng);
    let embed_a_hnn = apply_embedding(a_words_hnn, w);

    //  word_valid for embed_a_hnn
    assert forall|j: int| 0 <= j < a_words_hnn.len()
        implies word_valid(#[trigger] a_words_hnn[j], ng)
    by { assert(word_valid(data.associations[j].0, ng)); }
    lemma_apply_embedding_valid(a_words_hnn, w, ng);

    let embed_a_tower = apply_embedding(a_words_tower, w);
    let embed_b_tower = apply_embedding(b_words_tower, w);

    //  Connect embed_b_tower to embed_b_hnn (shift by 0 = identity)
    assert forall|i: int| 0 <= i < b_words_hnn.len() implies
        #[trigger] b_words_tower[i] =~= shift_word(b_words_hnn[i], 0nat) by {}
    lemma_shift_embedding_distributes(b_words_hnn, b_words_tower, w, 0nat);
    //  embed_b_tower =~= shift(embed_b_hnn, 0) =~= embed_b_hnn
    assert(embed_b_tower =~= apply_embedding(b_words_hnn, w));

    //  HNN biconditional (should fire from hnn_associations_isomorphic)
    assert(equiv_in_presentation(data.base, embed_a_hnn, empty_word())
        <==> equiv_in_presentation(data.base, apply_embedding(b_words_hnn, w), empty_word()));

    //  Key =~= connections
    assert(b_words_tower =~= b_words_hnn);
    assert(embed_b_tower =~= apply_embedding(b_words_hnn, w));

    //  Explicitly trigger hnn_iso biconditional
    assert(word_valid(w, kk as nat));
    assert(equiv_in_presentation(data.base, embed_a_hnn, empty_word())
        <==> equiv_in_presentation(data.base, apply_embedding(b_words_hnn, w), empty_word()));

    //  Forward: equiv(p1, embed_a_tower, ε) → equiv(base, embed_a_hnn, ε)
    //  Then hnn_iso → equiv(base, embed_b_hnn, ε) =~= equiv(p2, embed_b_tower, ε)
    //  Setup for forward direction (AFP right-injectivity needs these)
    if k > 0 {
        assert(tower_textbook_prereqs_at(data, (k - 1) as nat));
        lemma_tower_afp_data_valid(data, (k - 1) as nat);
        lemma_tower_valid(data, (k - 1) as nat);
        lemma_tower_num_generators(data, (k - 1) as nat);
    }

    //  Establish the two intermediate biconditionals, then chain
    let mid = equiv_in_presentation(data.base, embed_a_hnn, empty_word());
    let lhs = equiv_in_presentation(afp_data.p1, apply_embedding(a_words_tower, w), empty_word());
    let rhs = equiv_in_presentation(afp_data.p2, apply_embedding(b_words_tower, w), empty_word());

    //  (1) mid ↔ rhs: from hnn_iso + embed_b connection
    //  Already have: mid ↔ equiv(base, embed_b_hnn, ε) from hnn_iso
    //  And: rhs = equiv(base, embed_b_tower, ε) = equiv(base, embed_b_hnn, ε) (from =~=)
    //  So: mid ↔ rhs

    //  (2) lhs → mid: tower equiv → base equiv
    if lhs {
        lemma_tower_iso_forward_mid(data, k, embed_a_hnn);
    }

    //  (3) mid → lhs: base equiv → tower equiv
    if mid {
        lemma_tower_iso_backward_mid(data, k, embed_a_hnn);
    }
}

pub proof fn lemma_tower_identifications_isomorphic(
    data: HNNData, k: nat,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        tower_textbook_chain(data, k),
    ensures
        crate::normal_form_amalgamated::identifications_isomorphic(tower_afp_data(data, k)),
{
    let ng = data.base.num_generators;
    let afp_data = tower_afp_data(data, k);
    let kk = afp_data.identifications.len();
    reveal(presentation_valid);

    assert(kk == data.associations.len());
    assert forall|w: Word| word_valid(w, kk as nat) implies (
        equiv_in_presentation(afp_data.p1,
            apply_embedding(Seq::new(kk, |i: int| afp_data.identifications[i].0), w),
            empty_word())
        <==>
        equiv_in_presentation(afp_data.p2,
            apply_embedding(Seq::new(kk, |i: int| afp_data.identifications[i].1), w),
            empty_word()))
    by {
        lemma_tower_iso_per_word(data, k, w);
    }
}

///  A base inverse pair [s, inv(s)] at level k: net_level is 0 and translation ≡ ε in tower.
proof fn lemma_translate_base_pair_trivial(
    data: HNNData, m: nat, s: Symbol, base_level: nat,
)
    requires
        hnn_data_valid(data),
        !is_stable(data, s),
        symbol_valid(s, data.base.num_generators),
        base_level <= m,
    ensures ({
        let pair = concat(Seq::new(1, |_j: int| s), Seq::new(1, |_j: int| inverse_symbol(s)));
        &&& net_level(data, pair) == 0
        &&& equiv_in_presentation(tower_presentation(data, m),
                translate_word_at(data, pair, base_level as int), empty_word())
    }),
{
    let ng = data.base.num_generators;
    let s_word = Seq::new(1, |_j: int| s);
    let inv_s_word = Seq::new(1, |_j: int| inverse_symbol(s));
    let pair = concat(s_word, inv_s_word);

    //  net_level(pair) = 0 (neither s nor inv(s) is stable)
    lemma_net_level_concat(data, s_word, inv_s_word);
    assert(s_word.first() == s);
    assert(s_word.drop_first() =~= Seq::<Symbol>::empty());
    assert(inv_s_word.first() == inverse_symbol(s));
    assert(inv_s_word.drop_first() =~= Seq::<Symbol>::empty());
    reveal_with_fuel(net_level, 2);
    assert(net_level(data, s_word) == 0) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    assert(net_level(data, inv_s_word) == 0) by {
        match s {
            Symbol::Gen(i) => { assert(!is_stable(data, Symbol::Inv(i))); }
            Symbol::Inv(i) => { assert(!is_stable(data, Symbol::Gen(i))); }
        }
    }

    //  Fully unfold translate for 2-element pair
    reveal_with_fuel(translate_word_at, 3);
    //  translate(pair, bl) = [shift_symbol(s, bl*ng), shift_symbol(inv(s), bl*ng)]
    //  These form a cancelling pair
    let ss = shift_symbol(s, base_level * ng);
    let iss = shift_symbol(inverse_symbol(s), base_level * ng);
    //  ss and iss are inverses: Gen(j+k) and Inv(j+k)
    assert(is_inverse_pair(ss, iss)) by {
        match s { Symbol::Gen(i) => {} Symbol::Inv(i) => {} }
    }
    //  The translated pair has a cancellation at position 0
    let translated = translate_word_at(data, pair, base_level as int);
    assert(has_cancellation_at(translated, 0));
    assert(reduce_at(translated, 0) =~= empty_word());
    //  Free reduction gives a 1-step derivation proving ≡ ε
    let step = DerivationStep::FreeReduce { position: 0 };
    assert(apply_step(tower_presentation(data, m), translated, step)
        == Some(empty_word()));
    let d = Derivation { steps: Seq::new(1, |_i: int| step) };
    assert(d.steps.len() == 1);
    assert(d.steps.first() == step);
    assert(d.steps.drop_first() =~= Seq::<DerivationStep>::empty());
    reveal_with_fuel(derivation_produces, 2);
    assert(derivation_valid(tower_presentation(data, m), d, translated, empty_word()));
}

//  ============================================================
//  Part K: Level bounds and prefix_levels_bounded
//  ============================================================

///  All prefix net_levels of w are in [0, m].
///  This means: for every j in [0, w.len()], net_level(w[0..j]) is in [0, m].
pub open spec fn prefix_levels_bounded(data: HNNData, w: Word, m: nat) -> bool {
    forall|j: int| #![trigger w.subrange(0, j)]
        0 <= j <= w.len() ==>
            0 <= net_level(data, w.subrange(0, j)) <= m as int
}

///  Net level of a subrange [0, j] decomposes via concat.
proof fn lemma_net_level_subrange_prefix(data: HNNData, w: Word, pos: int)
    requires 0 <= pos <= w.len(),
    ensures
        w =~= concat(w.subrange(0, pos), w.subrange(pos, w.len() as int)),
        net_level(data, w) == net_level(data, w.subrange(0, pos))
            + net_level(data, w.subrange(pos, w.len() as int)),
{
    assert(w =~= w.subrange(0, pos) + w.subrange(pos, w.len() as int));
    lemma_net_level_concat(data, w.subrange(0, pos), w.subrange(pos, w.len() as int));
}

//  ============================================================
//  Part L: word_valid for shift_word at arbitrary offset
//  ============================================================

///  shift_word(w, k * ng) is word_valid for (m+1)*ng when w is base-valid and k <= m.
proof fn lemma_shift_word_valid_for_tower(
    data: HNNData, w: Word, k: nat, m: nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        k <= m,
    ensures
        word_valid(shift_word(w, k * data.base.num_generators),
            (m + 1) * data.base.num_generators),
{
    let ng = data.base.num_generators;
    let sw = shift_word(w, k * ng);
    let n = (m + 1) * ng;
    //  k <= m implies k*ng <= m*ng, so i + k*ng < ng + m*ng = (m+1)*ng = n
    assert(k * ng <= m * ng) by(nonlinear_arith)
        requires k <= m
    {}
    assert(n == m * ng + ng) by(nonlinear_arith)
        requires n == (m + 1) * ng
    {}
    assert forall|j: int| 0 <= j < sw.len()
        implies symbol_valid(#[trigger] sw[j], n)
    by {
        assert(sw[j] == shift_symbol(w[j], k * ng));
        assert(symbol_valid(w[j], ng));
        match w[j] {
            Symbol::Gen(i) => { assert(i < ng); }
            Symbol::Inv(i) => { assert(i < ng); }
        }
    }
}

///  inverse_word(shift_word(w, k*ng)) is word_valid for tower(m).
proof fn lemma_inv_shift_word_valid_for_tower(
    data: HNNData, w: Word, k: nat, m: nat,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        k <= m,
    ensures
        word_valid(inverse_word(shift_word(w, k * data.base.num_generators)),
            (m + 1) * data.base.num_generators),
{
    let ng = data.base.num_generators;
    lemma_shift_word_valid_for_tower(data, w, k, m);
    crate::word::lemma_inverse_word_valid(
        shift_word(w, k * ng), (m + 1) * ng);
}

//  ============================================================
//  Part M: Net level helpers for relators
//  ============================================================

///  Net level of inverse_word is the negation.
proof fn lemma_net_level_inverse(data: HNNData, w: Word)
    ensures
        net_level(data, inverse_word(w)) == -net_level(data, w),
    decreases w.len(),
{
    if w.len() == 0 {
        assert(inverse_word(w) =~= empty_word());
    } else {
        let ng = data.base.num_generators;
        let s = w.first();
        let rest = w.drop_first();

        //  inverse_word(w) = concat(inverse_word(rest), [inv(s)])
        let inv_s_word = Seq::new(1, |_j: int| inverse_symbol(s));
        assert(inverse_word(w) =~= concat(inverse_word(rest), inv_s_word));

        //  net_level decomposes
        lemma_net_level_concat(data, inverse_word(rest), inv_s_word);
        lemma_net_level_inverse(data, rest);

        //  net_level of [inv(s)]
        assert(inv_s_word.first() == inverse_symbol(s));
        assert(inv_s_word.drop_first() =~= Seq::<Symbol>::empty());
        reveal_with_fuel(net_level, 2);

        //  Case analysis: net_level([inv(s)]) == -net_level_contribution(s)
        if s == Symbol::Gen(ng) {
            assert(inverse_symbol(s) == Symbol::Inv(ng));
        } else if s == Symbol::Inv(ng) {
            assert(inverse_symbol(s) == Symbol::Gen(ng));
        } else {
            match s {
                Symbol::Gen(i) => {
                    assert(i != ng);
                    assert(inverse_symbol(s) == Symbol::Inv(i));
                    assert(Symbol::Inv(i) != Symbol::Gen(ng));
                    assert(Symbol::Inv(i) != Symbol::Inv(ng));
                }
                Symbol::Inv(i) => {
                    assert(i != ng);
                    assert(inverse_symbol(s) == Symbol::Gen(i));
                    assert(Symbol::Gen(i) != Symbol::Gen(ng));
                    assert(Symbol::Gen(i) != Symbol::Inv(ng));
                }
            }
        }
    }
}

///  HNN relator has net_level 0.
proof fn lemma_net_level_hnn_relator(data: HNNData, i: int)
    requires
        hnn_data_valid(data),
        0 <= i < data.associations.len() as int,
    ensures
        net_level(data, hnn_relator(data, i)) == 0,
{
    let ng = data.base.num_generators;
    let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
    let t_inv = Seq::new(1, |_j: int| Symbol::Inv(ng));
    let t_gen = Seq::new(1, |_j: int| Symbol::Gen(ng));
    let part1 = concat(t_inv, a_i);
    let part2 = concat(t_gen, inverse_word(b_i));

    assert(hnn_relator(data, i) =~= concat(part1, part2));
    lemma_net_level_concat(data, part1, part2);
    lemma_net_level_concat(data, t_inv, a_i);
    lemma_net_level_concat(data, t_gen, inverse_word(b_i));
    lemma_net_level_stable(data, Symbol::Inv(ng));
    lemma_net_level_stable(data, Symbol::Gen(ng));
    lemma_net_level_base_word(data, a_i);
    crate::word::lemma_inverse_word_valid(b_i, ng);
    lemma_net_level_base_word(data, inverse_word(b_i));
}

///  Any relator in hnn_presentation has net_level 0.
proof fn lemma_net_level_hnn_pres_relator(data: HNNData, idx: int)
    requires
        hnn_data_valid(data),
        0 <= idx < hnn_presentation(data).relators.len(),
    ensures
        net_level(data, hnn_presentation(data).relators[idx]) == 0,
{
    let p = hnn_presentation(data);
    let nb = data.base.relators.len();
    if idx < nb {
        assert(p.relators[idx] == data.base.relators[idx]);
        reveal(presentation_valid);
        lemma_net_level_base_word(data, data.base.relators[idx]);
    } else {
        let hi = (idx - nb) as int;
        assert(p.relators[idx] == hnn_relator(data, hi));
        lemma_net_level_hnn_relator(data, hi);
    }
}

///  get_relator has net_level 0 when the underlying relator does.
proof fn lemma_net_level_get_relator(data: HNNData, idx: nat, inverted: bool)
    requires
        hnn_data_valid(data),
        0 <= idx < hnn_presentation(data).relators.len(),
    ensures
        net_level(data, get_relator(hnn_presentation(data), idx, inverted)) == 0,
{
    let p = hnn_presentation(data);
    lemma_net_level_hnn_pres_relator(data, idx as int);
    if inverted {
        lemma_net_level_inverse(data, p.relators[idx as int]);
    }
}

///  Decompose inverse_word(hnn_relator):
///  inv(t⁻¹ · a_i · t · inv(b_i)) = b_i · t⁻¹ · inv(a_i) · t
proof fn lemma_inverse_hnn_relator_decomp(data: HNNData, i: int)
    requires
        hnn_data_valid(data),
        0 <= i < data.associations.len() as int,
    ensures ({
        let ng = data.base.num_generators;
        let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
        let t_word = Seq::new(1, |_j: int| Symbol::Gen(ng));
        let t_inv_word = Seq::new(1, |_j: int| Symbol::Inv(ng));
        inverse_word(hnn_relator(data, i)) =~=
            concat(b_i, concat(t_inv_word, concat(inverse_word(a_i), t_word)))
    }),
{
    let ng = data.base.num_generators;
    let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
    let t_word = Seq::new(1, |_j: int| Symbol::Gen(ng));
    let t_inv_word = Seq::new(1, |_j: int| Symbol::Inv(ng));
    let inv_b_i = inverse_word(b_i);

    //  hnn_relator = concat(t_inv_word, concat(a_i, concat(t_word, inv_b_i)))
    let r = hnn_relator(data, i);
    assert(r =~= concat(t_inv_word, concat(a_i, concat(t_word, inv_b_i))));

    //  Apply inverse_concat repeatedly
    crate::word::lemma_inverse_concat(t_inv_word, concat(a_i, concat(t_word, inv_b_i)));
    crate::word::lemma_inverse_concat(a_i, concat(t_word, inv_b_i));
    crate::word::lemma_inverse_concat(t_word, inv_b_i);

    //  inverse of single-symbol words
    assert(inverse_word(t_inv_word) =~= t_word) by {
        reveal_with_fuel(inverse_word, 2);
    }
    assert(inverse_word(t_word) =~= t_inv_word) by {
        reveal_with_fuel(inverse_word, 2);
    }

    //  inverse of inverse_word(b_i) = b_i
    crate::word::lemma_inverse_involution(b_i);

    //  Chain: inv(r) = inv(inv_b_i) ++ inv(t_word) ++ inv(a_i) ++ inv(t_inv_word)
    //                = b_i ++ t_inv_word ++ inv(a_i) ++ t_word
}

//  ============================================================
//  Part N: Per-step translation — the core case analysis
//  ============================================================

///  Helper: A single free-reduce or free-expand step preserves translation equivalence.
///  The inverse pair [s, inv(s)] either:
///   - stable pair: translates to ε (=~=)
///   - base pair: translates to a cancelling pair ≡ ε in tower
proof fn lemma_pair_translate_equiv_empty(
    data: HNNData, m: nat, s: Symbol, base_level: int,
)
    requires
        hnn_data_valid(data),
        symbol_valid(s, hnn_presentation(data).num_generators),
        0 <= base_level <= m as int,
    ensures ({
        let pair = concat(Seq::new(1, |_j: int| s),
                          Seq::new(1, |_j: int| inverse_symbol(s)));
        &&& net_level(data, pair) == 0
        &&& equiv_in_presentation(tower_presentation(data, m),
                translate_word_at(data, pair, base_level), empty_word())
        &&& word_valid(translate_word_at(data, pair, base_level),
                tower_presentation(data, m).num_generators)
    }),
{
    let ng = data.base.num_generators;
    let pair = concat(Seq::new(1, |_j: int| s),
                      Seq::new(1, |_j: int| inverse_symbol(s)));
    let tp = tower_presentation(data, m);

    if is_stable(data, s) {
        //  Stable pair: translate =~= ε
        lemma_translate_stable_pair(data, s, base_level);
        assert(translate_word_at(data, pair, base_level) =~= empty_word());
        //  empty word ≡ ε trivially
        lemma_equiv_refl(tp, empty_word());
        //  word_valid of empty word
        assert(word_valid(empty_word(), tp.num_generators));
    } else {
        //  Base pair: use existing lemma
        assert(symbol_valid(s, ng)) by {
            match s {
                Symbol::Gen(i) => { assert(i < ng + 1); assert(i != ng); assert(i < ng); }
                Symbol::Inv(i) => { assert(i < ng + 1); assert(i != ng); assert(i < ng); }
            }
        }
        lemma_translate_base_pair_trivial(data, m, s, base_level as nat);

        //  word_valid: the translated pair is a 2-symbol word with shifted symbols
        lemma_tower_num_generators(data, m);
        reveal_with_fuel(translate_word_at, 3);
        let translated = translate_word_at(data, pair, base_level);
        let bl = base_level as nat;
        assert(bl * ng <= m * ng) by(nonlinear_arith)
            requires bl <= m
        {}
        assert((m + 1) * ng == m * ng + ng) by(nonlinear_arith) {}
        assert forall|j: int| 0 <= j < translated.len()
            implies symbol_valid(#[trigger] translated[j], tp.num_generators)
        by {
            match s {
                Symbol::Gen(i) => { assert(i < ng); }
                Symbol::Inv(i) => { assert(i < ng); }
            }
        }
    }
}

///  Helper: word_valid for the translation of a base relator at level k.
proof fn lemma_translate_base_relator_valid(
    data: HNNData, m: nat, k: nat, r_idx: int,
)
    requires
        hnn_data_valid(data),
        0 <= r_idx < data.base.relators.len(),
        k <= m,
    ensures
        word_valid(
            translate_word_at(data, data.base.relators[r_idx], k as int),
            tower_presentation(data, m).num_generators),
{
    let ng = data.base.num_generators;
    let r = data.base.relators[r_idx];
    reveal(presentation_valid);
    lemma_translate_base_word_at(data, r, k);
    lemma_tower_num_generators(data, m);
    lemma_shift_word_valid_for_tower(data, r, k, m);
}

///  Helper: word_valid for the translation of an HNN relator at level k.
proof fn lemma_translate_hnn_relator_valid(
    data: HNNData, m: nat, k: nat, i: int,
)
    requires
        hnn_data_valid(data),
        0 <= i < data.associations.len() as int,
        k >= 1,
        k <= m,
    ensures
        word_valid(
            translate_word_at(data, hnn_relator(data, i), k as int),
            tower_presentation(data, m).num_generators),
{
    let ng = data.base.num_generators;
    let (a_i, b_i) = (data.associations[i].0, data.associations[i].1);
    lemma_translate_hnn_relator(data, i, k as int);
    lemma_tower_num_generators(data, m);
    //  translate = amalgamation_relator(tower_afp_data(data, (k-1)), i)
    //            = concat(shift_word(a_i, (k-1)*ng), inverse_word(shift_word(b_i, k*ng)))
    let afp_data = tower_afp_data(data, (k - 1) as nat);
    let tr = amalgamation_relator(afp_data, i);
    assert(translate_word_at(data, hnn_relator(data, i), k as int) =~= tr);

    //  Need tower_num_generators at k-1 to connect afp_data.p1.num_generators = k*ng
    lemma_tower_num_generators(data, (k - 1) as nat);

    let sa = shift_word(a_i, ((k - 1) as nat) * ng);
    crate::word::lemma_inverse_word_valid(b_i, ng);
    let sb = shift_word(b_i, k * ng);
    let inv_sb = inverse_word(sb);

    let tp = tower_presentation(data, m);
    lemma_shift_word_valid_for_tower(data, a_i, (k - 1) as nat, m);
    lemma_shift_word_valid_for_tower(data, b_i, k, m);
    crate::word::lemma_inverse_word_valid(sb, (m + 1) * ng);
    crate::word::lemma_concat_word_valid(sa, inv_sb, (m + 1) * ng);

    //  Connect tr to concat(sa, inv_sb) via afp_data decomposition
    assert(afp_data.p1.num_generators == k * ng);
    assert(tr =~= concat(sa, inv_sb));

    //  Transfer word_valid through =~= to the translate
    let tw = translate_word_at(data, hnn_relator(data, i), k as int);
    assert forall|j: int| 0 <= j < tw.len()
        implies symbol_valid(#[trigger] tw[j], tp.num_generators)
    by {
        assert(tw[j] == tr[j]);
    }
}

///  Helper: translated relator (base or HNN, possibly inverted) is word_valid for tower(m).
proof fn lemma_translate_relator_valid(
    data: HNNData, m: nat, idx: nat, inverted: bool, level: int,
)
    requires
        hnn_data_valid(data),
        0 <= idx < hnn_presentation(data).relators.len(),
        0 <= level <= m as int,
        //  HNN relators need level >= 1
        idx >= data.base.relators.len() ==> level >= 1,
    ensures
        word_valid(
            translate_word_at(data,
                get_relator(hnn_presentation(data), idx, inverted), level),
            tower_presentation(data, m).num_generators),
{
    let p = hnn_presentation(data);
    let ng = data.base.num_generators;
    let nb = data.base.relators.len();
    let tp = tower_presentation(data, m);

    lemma_tower_num_generators(data, m);
    lemma_tower_valid(data, m);

    if !inverted {
        if idx < nb {
            //  Base relator
            assert(p.relators[idx as int] == data.base.relators[idx as int]);
            lemma_translate_base_relator_valid(data, m, level as nat, idx as int);
        } else {
            //  HNN relator
            let hi = (idx - nb) as int;
            assert(p.relators[idx as int] == hnn_relator(data, hi));
            lemma_translate_hnn_relator_valid(data, m, level as nat, hi);
        }
    } else {
        //  Inverted relator: get_relator = inverse_word(p.relators[idx])
        if idx < nb {
            //  Inverted base relator: inverse_word of a base word is still base-valid
            assert(p.relators[idx as int] == data.base.relators[idx as int]);
            let base_r = data.base.relators[idx as int];
            reveal(presentation_valid);
            crate::word::lemma_inverse_word_valid(base_r, ng);
            lemma_translate_base_word_at(data, inverse_word(base_r), level as nat);
            lemma_tower_num_generators(data, m);
            lemma_shift_word_valid_for_tower(data, inverse_word(base_r), level as nat, m);
        } else {
            //  Inverted HNN relator: inv(t⁻¹·a_i·t·inv(b_i)) = b_i·t⁻¹·inv(a_i)·t
            let hi = (idx - nb) as int;
            assert(p.relators[idx as int] == hnn_relator(data, hi));
            lemma_inverse_hnn_relator_decomp(data, hi);
            let (a_i, b_i) = (data.associations[hi].0, data.associations[hi].1);
            let t_word = Seq::new(1, |_j: int| Symbol::Gen(ng));
            let t_inv_word = Seq::new(1, |_j: int| Symbol::Inv(ng));
            crate::word::lemma_inverse_word_valid(a_i, ng);
            let inv_a_i = inverse_word(a_i);
            let k = level as nat;

            //  Decompose and translate each part
            let part_a = b_i;
            let part_b = t_inv_word;
            let part_c = inv_a_i;
            let part_d = t_word;
            let part_cd = concat(part_c, part_d);
            let part_bcd = concat(part_b, part_cd);

            assert(inverse_word(hnn_relator(data, hi))
                =~= concat(part_a, part_bcd));

            //  net_level computations
            lemma_net_level_base_word(data, b_i);
            lemma_net_level_base_word(data, inv_a_i);
            lemma_net_level_stable(data, Symbol::Inv(ng));
            lemma_net_level_stable(data, Symbol::Gen(ng));
            lemma_net_level_concat(data, part_c, part_d);
            lemma_net_level_concat(data, part_b, part_cd);

            //  translate_concat decompositions
            lemma_translate_concat(data, part_a, part_bcd, k as int);
            lemma_translate_concat(data, part_b, part_cd, k as int);
            lemma_translate_concat(data, part_c, part_d, (k - 1) as int);
            lemma_translate_base_word_at(data, b_i, k);
            lemma_translate_stable_empty(data, Symbol::Inv(ng), k as int);
            lemma_translate_base_word_at(data, inv_a_i, (k - 1) as nat);
            lemma_translate_stable_empty(data, Symbol::Gen(ng), (k - 1) as int);

            let tr = translate_word_at(data, inverse_word(hnn_relator(data, hi)), k as int);
            assert(tr =~= concat(
                shift_word(b_i, k * ng),
                shift_word(inv_a_i, ((k - 1) as nat) * ng)));

            //  word_valid of the translated parts
            lemma_shift_word_valid_for_tower(data, b_i, k, m);
            lemma_shift_word_valid_for_tower(data, inv_a_i, (k - 1) as nat, m);
            crate::word::lemma_concat_word_valid(
                shift_word(b_i, k * ng),
                shift_word(inv_a_i, ((k - 1) as nat) * ng),
                (m + 1) * ng);
        }
    }
}

///  Helper: translated relator (base or HNN, possibly inverted) ≡ ε in tower(m).
proof fn lemma_translate_relator_equiv_empty(
    data: HNNData, m: nat, idx: nat, inverted: bool, level: int,
)
    requires
        hnn_data_valid(data),
        0 <= idx < hnn_presentation(data).relators.len(),
        0 <= level <= m as int,
        idx >= data.base.relators.len() ==> level >= 1,
    ensures ({
        let r = get_relator(hnn_presentation(data), idx, inverted);
        &&& net_level(data, r) == 0
        &&& equiv_in_presentation(tower_presentation(data, m),
                translate_word_at(data, r, level), empty_word())
    }),
{
    let p = hnn_presentation(data);
    let ng = data.base.num_generators;
    let nb = data.base.relators.len();
    let tp = tower_presentation(data, m);
    let r = get_relator(p, idx, inverted);

    lemma_net_level_get_relator(data, idx, inverted);

    if !inverted {
        if idx < nb {
            //  Base relator at level k
            assert(r == data.base.relators[idx as int]);
            reveal(presentation_valid);
            lemma_translate_base_word_at(data, r, level as nat);
            lemma_base_relator_in_tower(data, m, level as nat, idx as int);
        } else {
            //  HNN relator at level k
            let hi = (idx - nb) as int;
            assert(r == hnn_relator(data, hi));
            lemma_translate_hnn_relator(data, hi, level);
            lemma_ident_relator_in_tower(data, m, (level - 1) as nat, hi);
        }
    } else {
        //  Inverted: get_relator = inverse_word(relator)
        if idx < nb {
            assert(r == inverse_word(data.base.relators[idx as int]));
            let base_r = data.base.relators[idx as int];
            reveal(presentation_valid);
            //  First show non-inverted translate ≡ ε
            lemma_translate_base_word_at(data, base_r, level as nat);
            lemma_base_relator_in_tower(data, m, level as nat, idx as int);

            //  Now show inverted: inverse_word(base_r) is still base-valid
            crate::word::lemma_inverse_word_valid(base_r, ng);
            lemma_translate_base_word_at(data, inverse_word(base_r), level as nat);

            //  shift(inv(r), k*ng) = inv(shift(r, k*ng))
            crate::free_product::lemma_shift_inverse_word(base_r, (level as nat) * ng);

            //  translate(inv(r), k) =~= inv(shift(r, k*ng)) and translate(r, k) ≡ ε
            //  so inv(translate(r, k)) ≡ ε
            lemma_tower_valid(data, m);
            lemma_tower_num_generators(data, m);
            lemma_shift_word_valid_for_tower(data, base_r, level as nat, m);
            crate::normal_form_amalgamated::lemma_inverse_of_trivial(
                tp,
                shift_word(base_r, (level as nat) * ng));
        } else {
            let hi = (idx - nb) as int;
            assert(r == inverse_word(hnn_relator(data, hi)));
            //  Decompose inv(hnn_relator) = b_i · t⁻¹ · inv(a_i) · t
            lemma_inverse_hnn_relator_decomp(data, hi);
            let (a_i, b_i) = (data.associations[hi].0, data.associations[hi].1);
            let t_word = Seq::new(1, |_j: int| Symbol::Gen(ng));
            let t_inv_word = Seq::new(1, |_j: int| Symbol::Inv(ng));
            crate::word::lemma_inverse_word_valid(a_i, ng);
            let inv_a_i = inverse_word(a_i);
            let k = level as nat;

            let part_a = b_i;
            let part_b = t_inv_word;
            let part_c = inv_a_i;
            let part_d = t_word;
            let part_cd = concat(part_c, part_d);
            let part_bcd = concat(part_b, part_cd);

            assert(r =~= concat(part_a, part_bcd));

            //  net_level and translate decomposition
            lemma_net_level_base_word(data, b_i);
            lemma_net_level_base_word(data, inv_a_i);
            lemma_net_level_stable(data, Symbol::Inv(ng));
            lemma_net_level_stable(data, Symbol::Gen(ng));
            lemma_net_level_concat(data, part_c, part_d);
            lemma_net_level_concat(data, part_b, part_cd);
            lemma_translate_concat(data, part_a, part_bcd, k as int);
            lemma_translate_concat(data, part_b, part_cd, k as int);
            lemma_translate_concat(data, part_c, part_d, (k - 1) as int);
            lemma_translate_base_word_at(data, b_i, k);
            lemma_translate_stable_empty(data, Symbol::Inv(ng), k as int);
            lemma_translate_base_word_at(data, inv_a_i, (k - 1) as nat);
            lemma_translate_stable_empty(data, Symbol::Gen(ng), (k - 1) as int);

            //  translate(r, k) =~= concat(shift(b_i, k*ng), shift(inv(a_i), (k-1)*ng))
            let tr_inv = translate_word_at(data, r, k as int);
            assert(tr_inv =~= concat(
                shift_word(b_i, k * ng),
                shift_word(inv_a_i, ((k - 1) as nat) * ng)));

            //  This equals inverse_word(amalgamation_relator(afp_data, hi))
            //  amal_r = concat(shift(a_i, (k-1)*ng), inv(shift(b_i, k*ng)))
            //  inv(amal_r) = concat(shift(b_i, k*ng), inv(shift(a_i, (k-1)*ng)))
            crate::free_product::lemma_shift_inverse_word(a_i, ((k - 1) as nat) * ng);
            //  shift(inv(a_i), (k-1)*ng) =~= inv(shift(a_i, (k-1)*ng))

            //  amal_r ≡ ε, so inv(amal_r) ≡ ε
            let afp_data = tower_afp_data(data, (level - 1) as nat);
            let amal_r = amalgamation_relator(afp_data, hi);
            lemma_translate_hnn_relator(data, hi, level);
            lemma_ident_relator_in_tower(data, m, (level - 1) as nat, hi);

            lemma_tower_valid(data, m);
            lemma_tower_num_generators(data, m);

            //  word_valid of amal_r for lemma_inverse_of_trivial
            lemma_tower_num_generators(data, (level - 1) as nat);
            let sa = shift_word(a_i, ((k - 1) as nat) * ng);
            let sb = shift_word(b_i, k * ng);
            lemma_shift_word_valid_for_tower(data, a_i, (k - 1) as nat, m);
            lemma_shift_word_valid_for_tower(data, b_i, k, m);
            crate::word::lemma_inverse_word_valid(sb, (m + 1) * ng);
            crate::word::lemma_concat_word_valid(sa, inverse_word(sb), (m + 1) * ng);
            //  amal_r =~= concat(sa, inverse_word(sb))
            assert(amal_r =~= concat(sa, inverse_word(sb)));
            //  Transfer word_valid through =~=
            assert forall|j: int| 0 <= j < amal_r.len()
                implies symbol_valid(#[trigger] amal_r[j], tp.num_generators)
            by {
                let cv = concat(sa, inverse_word(sb));
                assert(amal_r[j] == cv[j]);
            }

            crate::normal_form_amalgamated::lemma_inverse_of_trivial(tp, amal_r);
            //  inv(amal_r) = inv(concat(sa, inv(sb))) =~= concat(inv(inv(sb)), inv(sa)) =~= concat(sb, inv(sa))
            crate::word::lemma_inverse_concat(sa, inverse_word(sb));
            crate::word::lemma_inverse_involution(sb);
            //  inv(sa) =~= shift(inv(a_i), (k-1)*ng)
            crate::free_product::lemma_shift_inverse_word(a_i, ((k - 1) as nat) * ng);
            assert(inverse_word(amal_r) =~= concat(sb, shift_word(inv_a_i, ((k - 1) as nat) * ng)));
            assert(tr_inv =~= inverse_word(amal_r));
        }
    }
}

//  ============================================================
//  Part O: The per-step lemma
//  ============================================================

///  For FreeReduce/RelatorDelete at position pos:
///  the level at pos determines the middle's translation.
///  Need: 0 <= net_level(prefix) <= m, and for HNN relators, >= 1.
///
///  For FreeExpand/RelatorInsert at position pos:
///  the level at pos determines the middle's translation.
///  Same level requirements.
///
///  In all cases: translate(w) ≡ translate(w_next) in tower(m).
pub proof fn lemma_hnn_step_tower_equiv(
    data: HNNData, m: nat, base_level: int, w: Word, step: DerivationStep,
)
    requires
        hnn_data_valid(data),
        word_valid(w, hnn_presentation(data).num_generators),
        apply_step(hnn_presentation(data), w, step) is Some,
        step_level_ok(data, m, base_level, w, step),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, w, base_level),
            translate_word_at(data, apply_step(hnn_presentation(data), w, step).unwrap(), base_level)),
{
    let p = hnn_presentation(data);
    let tp = tower_presentation(data, m);
    let w_next = apply_step(p, w, step).unwrap();
    lemma_tower_valid(data, m);
    lemma_tower_num_generators(data, m);

    match step {
        DerivationStep::FreeReduce { position } => {
            let pos = position;
            let s = w[pos];
            let prefix = w.subrange(0, pos);
            let middle = concat(Seq::new(1, |_j: int| s), Seq::new(1, |_j: int| w[pos + 1]));
            let suffix = w.subrange(pos + 2, w.len() as int);

            assert(w =~= concat(prefix, concat(middle, suffix)));
            assert(w_next =~= concat(prefix, suffix));

            assert(is_inverse_pair(w[pos], w[pos + 1]));
            assert(w[pos + 1] == inverse_symbol(s));
            assert(middle =~= concat(Seq::new(1, |_j: int| s),
                                      Seq::new(1, |_j: int| inverse_symbol(s))));

            let level = base_level + net_level(data, prefix);

            assert(symbol_valid(s, p.num_generators));

            lemma_pair_translate_equiv_empty(data, m, s, level);

            lemma_translate_delete_middle(data, m, base_level, prefix, middle, suffix);
        },
        DerivationStep::FreeExpand { position, symbol } => {
            let pos = position;
            let prefix = w.subrange(0, pos);
            let suffix = w.subrange(pos, w.len() as int);
            let middle = concat(Seq::new(1, |_j: int| symbol),
                                Seq::new(1, |_j: int| inverse_symbol(symbol)));

            assert(w =~= concat(prefix, suffix));
            assert(w_next =~= concat(prefix, concat(middle, suffix)));

            let level = base_level + net_level(data, prefix);
            lemma_pair_translate_equiv_empty(data, m, symbol, level);

            lemma_translate_insert_middle(data, m, base_level, prefix, middle, suffix);
        },
        DerivationStep::RelatorDelete { position, relator_index, inverted } => {
            let pos = position;
            let r = get_relator(p, relator_index, inverted);
            let prefix = w.subrange(0, pos);
            let middle = r;
            let suffix = w.subrange(pos + r.len(), w.len() as int);

            assert(w.subrange(pos, pos + r.len() as int) == r);
            assert(w =~= concat(prefix, concat(middle, suffix)));
            assert(w_next =~= concat(prefix, suffix));

            let level = base_level + net_level(data, prefix);

            lemma_translate_relator_equiv_empty(data, m, relator_index, inverted, level);
            lemma_translate_relator_valid(data, m, relator_index, inverted, level);

            lemma_translate_delete_middle(data, m, base_level, prefix, middle, suffix);
        },
        DerivationStep::RelatorInsert { position, relator_index, inverted } => {
            let pos = position;
            let r = get_relator(p, relator_index, inverted);
            let prefix = w.subrange(0, pos);
            let suffix = w.subrange(pos, w.len() as int);
            let middle = r;

            assert(w =~= concat(prefix, suffix));
            assert(w_next =~= concat(prefix, concat(middle, suffix)));

            let level = base_level + net_level(data, prefix);

            lemma_translate_relator_equiv_empty(data, m, relator_index, inverted, level);
            lemma_translate_relator_valid(data, m, relator_index, inverted, level);

            lemma_translate_insert_middle(data, m, base_level, prefix, middle, suffix);
        },
    }
}

//  ============================================================
//  Part P: Derivation-level induction
//  ============================================================

///  Get the position of a derivation step.
pub open spec fn step_position(step: DerivationStep) -> int {
    match step {
        DerivationStep::FreeReduce { position } => position,
        DerivationStep::FreeExpand { position, .. } => position,
        DerivationStep::RelatorInsert { position, .. } => position,
        DerivationStep::RelatorDelete { position, .. } => position,
    }
}

///  Whether a step involves an HNN relator (not a base relator).
pub open spec fn step_is_hnn_relator(data: HNNData, step: DerivationStep) -> bool {
    match step {
        DerivationStep::RelatorInsert { relator_index, .. } |
        DerivationStep::RelatorDelete { relator_index, .. } =>
            relator_index >= data.base.relators.len(),
        _ => false,
    }
}

///  Level condition for a single step applied to word w.
pub open spec fn step_level_ok(data: HNNData, m: nat, base_level: int, w: Word, step: DerivationStep) -> bool {
    let pos = step_position(step);
    let level = net_level(data, w.subrange(0, pos)) + base_level;
    &&& 0 <= level <= m as int
    &&& (step_is_hnn_relator(data, step) ==> level >= 1)
}

///  A full derivation from w producing w', where every step has valid levels.
///  Returns the final word (should equal w') when the derivation is valid.
pub open spec fn derivation_levels_ok(
    data: HNNData, m: nat, base_level: int,
    steps: Seq<DerivationStep>, start: Word,
) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 {
        true
    } else {
        let p = hnn_presentation(data);
        match apply_step(p, start, steps.first()) {
            Some(next) => {
                step_level_ok(data, m, base_level, start, steps.first())
                && derivation_levels_ok(data, m, base_level, steps.drop_first(), next)
            },
            None => false,
        }
    }
}

///  Main induction: if all steps in a derivation have valid (shifted) levels,
///  then translate_at(start, base_level) ≡ translate_at(end, base_level) in tower(m).
pub proof fn lemma_hnn_derivation_to_tower_equiv(
    data: HNNData, m: nat, base_level: int,
    steps: Seq<DerivationStep>, start: Word, end: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(start, hnn_presentation(data).num_generators),
        derivation_produces(hnn_presentation(data), steps, start) == Some(end),
        derivation_levels_ok(data, m, base_level, steps, start),
    ensures
        equiv_in_presentation(tower_presentation(data, m),
            translate_word_at(data, start, base_level),
            translate_word_at(data, end, base_level)),
    decreases steps.len(),
{
    let p = hnn_presentation(data);
    let tp = tower_presentation(data, m);

    if steps.len() == 0 {
        assert(start == end);
        lemma_equiv_refl(tp, translate_word_at(data, start, base_level));
    } else {
        let step = steps.first();
        let mid = apply_step(p, start, step).unwrap();

        //  Per-step: translate(start) ≡ translate(mid)
        lemma_hnn_step_tower_equiv(data, m, base_level, start, step);

        //  mid is word_valid (step preserves word_valid)
        lemma_hnn_presentation_valid(data);
        crate::presentation::lemma_step_preserves_word_valid_pres(p, start, step, mid);

        //  Inductive: translate(mid) ≡ translate(end)
        lemma_hnn_derivation_to_tower_equiv(data, m, base_level, steps.drop_first(), mid, end);

        //  Chain: translate(start) ≡ translate(end)
        lemma_equiv_transitive(tp,
            translate_word_at(data, start, base_level),
            translate_word_at(data, mid, base_level),
            translate_word_at(data, end, base_level));
    }
}

///  **Britton's Lemma (Lyndon-Schupp Ch. IV):**
///  If w is a base word (no stable letters) and w ≡ ε in the HNN extension G*,
///  then w ≡ ε in the base group G.
///
///  Proof:
///  1. w ≡ ε in G* → derivation D with levels fitting in tower(m)
///  2. lemma_hnn_derivation_to_tower_equiv → translate(w) ≡ translate(ε) in tower(m)
///  3. translate(w) = w (base word), translate(ε) = ε
///  4. lemma_g0_embeds_in_tower_textbook → w ≡ ε in G
pub proof fn britton_lemma(
    data: HNNData, m: nat, w: Word,
)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
        //  The derivation fits within tower height m (at base_level 0)
        ({
            let d: Derivation = choose|d: Derivation|
                derivation_valid(hnn_presentation(data), d, w, empty_word());
            derivation_levels_ok(data, m, 0, d.steps, w)
        }),
        //  Tower textbook prerequisites
        tower_textbook_chain(data, m),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
{
    let hp = hnn_presentation(data);
    let d: Derivation = choose|d: Derivation|
        derivation_valid(hp, d, w, empty_word());

    assert(word_valid(w, hp.num_generators)) by {
        assert forall|k: int| 0 <= k < w.len()
            implies symbol_valid(#[trigger] w[k], hp.num_generators)
        by {}
    }

    lemma_hnn_derivation_to_tower_equiv(data, m, 0, d.steps, w, empty_word());

    lemma_translate_base_word(data, w);
    lemma_translate_empty(data);

    lemma_g0_embeds_in_tower_textbook(data, m, w);
}

//  ============================================================
//  Part S: Derivation level bounds for shifted translation
//  ============================================================

///  Minimum "adjusted" step level across a derivation.
///  For HNN relator steps, returns level - 1 (since they need level >= 1).
///  For other steps, returns level (since they need level >= 0).
///  Shift >= -derivation_min_adj_level ensures all shifted levels are valid.
pub open spec fn derivation_min_adj_level(
    data: HNNData, steps: Seq<DerivationStep>, start: Word,
) -> int
    decreases steps.len(),
{
    let hp = hnn_presentation(data);
    if steps.len() == 0 { 0 }
    else {
        match apply_step(hp, start, steps.first()) {
            Some(next) => {
                let pos = step_position(steps.first());
                let level = net_level(data, start.subrange(0, pos));
                let adj = if step_is_hnn_relator(data, steps.first()) { level - 1 } else { level };
                let rest_min = derivation_min_adj_level(data, steps.drop_first(), next);
                if adj < rest_min { adj } else { rest_min }
            }
            None => 0
        }
    }
}

///  Maximum step level across a derivation.
pub open spec fn derivation_max_step_level(
    data: HNNData, steps: Seq<DerivationStep>, start: Word,
) -> int
    decreases steps.len(),
{
    let hp = hnn_presentation(data);
    if steps.len() == 0 { 0 }
    else {
        match apply_step(hp, start, steps.first()) {
            Some(next) => {
                let pos = step_position(steps.first());
                let level = net_level(data, start.subrange(0, pos));
                let rest_max = derivation_max_step_level(data, steps.drop_first(), next);
                if level > rest_max { level } else { rest_max }
            }
            None => 0
        }
    }
}

///  If base_level >= -min_adj and m >= max_level + base_level,
///  then derivation_levels_ok holds.
proof fn lemma_derivation_levels_ok_from_bounds(
    data: HNNData, m: nat, base_level: int,
    steps: Seq<DerivationStep>, start: Word,
)
    requires
        derivation_produces(hnn_presentation(data), steps, start) is Some,
        base_level >= -derivation_min_adj_level(data, steps, start),
        m as int >= derivation_max_step_level(data, steps, start) + base_level,
    ensures
        derivation_levels_ok(data, m, base_level, steps, start),
    decreases steps.len(),
{
    if steps.len() == 0 {} else {
        let hp = hnn_presentation(data);
        let step = steps.first();
        let next = apply_step(hp, start, step).unwrap();
        let pos = step_position(step);
        let level = net_level(data, start.subrange(0, pos));
        let adj = if step_is_hnn_relator(data, step) { level - 1 } else { level };

        //  adj >= derivation_min_adj_level, so base_level >= -adj, so level + base_level >= 0 (or >= 1)
        assert(adj >= derivation_min_adj_level(data, steps, start));
        //  level <= derivation_max_step_level, so level + base_level <= m
        assert(level <= derivation_max_step_level(data, steps, start));

        //  Recurse: rest_min >= whole_min and rest_max <= whole_max
        let rest_min = derivation_min_adj_level(data, steps.drop_first(), next);
        let rest_max = derivation_max_step_level(data, steps.drop_first(), next);
        assert(rest_min >= derivation_min_adj_level(data, steps, start)) by {
            if adj < rest_min {} else {}
        }
        assert(rest_max <= derivation_max_step_level(data, steps, start)) by {
            if level > rest_max {} else {}
        }

        lemma_derivation_levels_ok_from_bounds(data, m, base_level, steps.drop_first(), next);
    }
}

//  ============================================================
//  Part T: Tower textbook chain from HNN associations
//  ============================================================

///  Derive tower_textbook_chain from hnn_associations_isomorphic by induction.
pub proof fn lemma_tower_textbook_chain_from_hnn_iso(data: HNNData, m: nat)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
    ensures
        tower_textbook_chain(data, m),
    decreases m,
{
    if m == 0 {
        assert forall|k: nat| k < 0nat
            implies #[trigger] tower_textbook_prereqs_at(data, k) by {}
    } else {
        //  IH: tower_textbook_chain(data, m-1)
        lemma_tower_textbook_chain_from_hnn_iso(data, (m - 1) as nat);

        let k = (m - 1) as nat;
        let afp_data = tower_afp_data(data, k);

        //  Prove identifications_isomorphic at level k
        lemma_tower_identifications_isomorphic(data, k);

        //  Prove action_preserves_canonical at level k
        lemma_tower_afp_data_valid(data, k);
        lemma_tower_valid(data, k);
        reveal(presentation_valid);
        crate::normal_form_afp_textbook::lemma_iso_implies_apc(afp_data);

        assert(tower_textbook_prereqs_at(data, k));

        assert forall|j: nat| j < m
            implies #[trigger] tower_textbook_prereqs_at(data, j)
        by {
            if j < k {} //  from IH
        }
    }
}

//  ============================================================
//  Part U: Copy-s tower embedding
//  ============================================================

///  Generalized tower embedding: if shift(w, s*ng) ≡ ε in tower(m) where s <= m,
///  then w ≡ ε in base. Uses AFP left-injectivity to peel from tower(m) down to
///  tower(s), then AFP right-injectivity at level s-1.
pub proof fn lemma_copy_s_embeds(data: HNNData, m: nat, s: nat, w: Word)
    requires
        hnn_data_valid(data),
        word_valid(w, data.base.num_generators),
        s <= m,
        tower_textbook_chain(data, m),
        equiv_in_presentation(tower_presentation(data, m),
            shift_word(w, s * data.base.num_generators), empty_word()),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
    decreases m,
{
    let ng = data.base.num_generators;
    if m == 0 {
        assert(s == 0);
        assert(s * ng == 0) by (nonlinear_arith) requires s == 0;
        assert(shift_word(w, 0nat) =~= w);
    } else if s == m {
        //  shift(w, m*ng) is in the G₂ part of AFP at level m-1
        let prev = (m - 1) as nat;
        assert(tower_textbook_prereqs_at(data, prev));
        lemma_tower_afp_data_valid(data, prev);
        lemma_tower_valid(data, prev);
        lemma_tower_num_generators(data, prev);
        reveal(presentation_valid);
        crate::normal_form_afp_textbook::lemma_afp_injectivity_right(
            tower_afp_data(data, prev), w);
    } else {
        //  s < m: shift(w, s*ng) is a tower(m-1) word
        let prev = (m - 1) as nat;
        assert(tower_textbook_prereqs_at(data, prev));
        lemma_tower_afp_data_valid(data, prev);
        lemma_tower_valid(data, prev);
        lemma_tower_num_generators(data, prev);
        reveal(presentation_valid);

        lemma_shift_word_valid_for_tower(data, w, s, prev);
        crate::normal_form_afp_textbook::lemma_afp_injectivity(
            tower_afp_data(data, prev), shift_word(w, s * ng));

        assert(tower_textbook_chain(data, prev)) by {
            assert forall|k: nat| k < prev
                implies #[trigger] tower_textbook_prereqs_at(data, k)
            by { assert(k < m); }
        }
        lemma_copy_s_embeds(data, prev, s, w);
    }
}

//  ============================================================
//  Part V: Translation of base word at shifted level
//  ============================================================

///  translate_word_at(data, ε, base_level) = ε for any base_level.
proof fn lemma_translate_empty_at(data: HNNData, base_level: int)
    ensures
        translate_word_at(data, empty_word(), base_level) =~= empty_word(),
{}

///  **Britton's Lemma (Unconditional, Lyndon-Schupp Ch. IV):**
///  If w is a base word and w ≡ ε in the HNN extension G*, then w ≡ ε in G.
///
///  No additional assumptions beyond hnn_data_valid and hnn_associations_isomorphic.
///  The tower textbook prerequisites are derived from hnn_associations_isomorphic,
///  and the derivation levels are handled by shifting to a non-negative base level.
pub proof fn britton_lemma_unconditional(
    data: HNNData, w: Word,
)
    requires
        hnn_data_valid(data),
        hnn_associations_isomorphic(data),
        word_valid(w, data.base.num_generators),
        equiv_in_presentation(hnn_presentation(data), w, empty_word()),
    ensures
        equiv_in_presentation(data.base, w, empty_word()),
{
    let hp = hnn_presentation(data);
    let ng = data.base.num_generators;

    //  Get the derivation
    let d: Derivation = choose|d: Derivation|
        derivation_valid(hp, d, w, empty_word());

    //  Compute shift amount from derivation bounds
    let min_adj = derivation_min_adj_level(data, d.steps, w);
    let max_lev = derivation_max_step_level(data, d.steps, w);
    //  base_level >= -min_adj ensures shifted levels are valid
    let base_level: nat = if min_adj >= 0 { 0 } else { (-min_adj) as nat };
    //  m >= max_lev + base_level and m >= base_level (since max_lev >= 0 for base word derivations)
    //  Use base_level + max_lev.abs() + 1 as a safe upper bound
    let max_lev_abs: nat = if max_lev >= 0 { max_lev as nat } else { (-max_lev) as nat };
    let m: nat = (base_level + max_lev_abs + 1) as nat;

    //  base_level <= m (since m = base_level + max_lev_abs + 1 > base_level)
    assert(base_level <= m);
    //  m >= max_lev + base_level (since m = base_level + |max_lev| + 1 >= base_level + max_lev)
    assert(m as int >= max_lev + base_level as int);

    //  word_valid(w, hp.num_generators) — weaken from ng to ng+1
    assert(word_valid(w, hp.num_generators)) by {
        assert forall|k: int| 0 <= k < w.len()
            implies symbol_valid(#[trigger] w[k], hp.num_generators)
        by {}
    }

    //  Step 1: Levels are OK with the chosen base_level
    lemma_derivation_levels_ok_from_bounds(data, m, base_level as int, d.steps, w);

    //  Step 2: Translate derivation to tower equivalence
    lemma_hnn_derivation_to_tower_equiv(data, m, base_level as int, d.steps, w, empty_word());

    //  Step 3: translate_at(w, base_level) = shift_word(w, base_level * ng)
    lemma_translate_base_word_at(data, w, base_level);
    //  Step 3b: translate_at(ε, base_level) = ε
    lemma_translate_empty_at(data, base_level as int);

    //  Step 4: Tower textbook chain from hnn_associations_isomorphic
    lemma_tower_textbook_chain_from_hnn_iso(data, m);

    //  Step 5: Copy-s tower embedding → w ≡ ε in base
    lemma_copy_s_embeds(data, m, base_level, w);
}

} //  verus!


