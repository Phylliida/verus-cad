use vstd::prelude::*;
use verus_algebra::traits::ring::Ring;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::archimedean::{nat_mul, lemma_nat_mul_zero, lemma_nat_mul_one, lemma_nat_mul_succ, lemma_nat_mul_add};
use verus_algebra::inequalities;

verus! {

// ============================================================
//  Finite Summation
// ============================================================

/// Finite sum: sum(f, lo, hi) = f(lo) + f(lo+1) + ... + f(hi-1).
/// Peel-from-left form: sum(f, lo, hi) = f(lo) + sum(f, lo+1, hi).
pub open spec fn sum<R: Ring>(f: spec_fn(int) -> R, lo: int, hi: int) -> R
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if hi <= lo { R::zero() }
    else { f(lo).add(sum::<R>(f, lo + 1, hi)) }
}

// ============================================================
//  Basic lemmas
// ============================================================

/// sum over empty range is zero.
pub proof fn lemma_sum_empty<R: Ring>(f: spec_fn(int) -> R, lo: int, hi: int)
    requires
        hi <= lo,
    ensures
        sum::<R>(f, lo, hi).eqv(R::zero()),
{
    R::axiom_eqv_reflexive(R::zero());
}

/// sum of a single element: sum(f, lo, lo+1) ≡ f(lo).
pub proof fn lemma_sum_single<R: Ring>(f: spec_fn(int) -> R, lo: int)
    ensures
        sum::<R>(f, lo, lo + 1).eqv(f(lo)),
{
    // sum(f, lo, lo+1) = f(lo) + sum(f, lo+1, lo+1) = f(lo) + 0
    assert(sum::<R>(f, lo, lo + 1) == f(lo).add(sum::<R>(f, lo + 1, lo + 1)));
    assert(sum::<R>(f, lo + 1, lo + 1) == R::zero());
    R::axiom_add_zero_right(f(lo));
}

/// Peel first element: sum(f, lo, hi) ≡ f(lo) + sum(f, lo+1, hi) when lo < hi.
pub proof fn lemma_sum_peel_first<R: Ring>(f: spec_fn(int) -> R, lo: int, hi: int)
    requires
        lo < hi,
    ensures
        sum::<R>(f, lo, hi).eqv(f(lo).add(sum::<R>(f, lo + 1, hi))),
{
    R::axiom_eqv_reflexive(f(lo).add(sum::<R>(f, lo + 1, hi)));
}

/// Peel last element: sum(f, lo, hi) ≡ sum(f, lo, hi-1) + f(hi-1) when lo < hi.
pub proof fn lemma_sum_peel_last<R: Ring>(f: spec_fn(int) -> R, lo: int, hi: int)
    requires
        lo < hi,
    ensures
        sum::<R>(f, lo, hi).eqv(sum::<R>(f, lo, hi - 1).add(f(hi - 1))),
    decreases hi - lo,
{
    if hi - lo == 1 {
        // hi == lo + 1
        // sum(f, lo, hi) = f(lo).add(sum(f, lo+1, lo+1)) = f(lo).add(0)
        // sum(f, lo, hi-1) = sum(f, lo, lo) = 0
        // f(hi-1) = f(lo)
        // Need: f(lo).add(0).eqv(0.add(f(lo)))
        assert(sum::<R>(f, lo + 1, lo + 1) == R::zero());
        assert(sum::<R>(f, lo, hi) == f(lo).add(R::zero()));
        assert(sum::<R>(f, lo, hi - 1) == R::zero());
        assert(hi - 1 == lo);
        // f(lo) + 0 ≡ f(lo)
        R::axiom_add_zero_right(f(lo));
        // 0 + f(hi-1) ≡ f(hi-1) = f(lo)
        additive_group_lemmas::lemma_add_zero_left::<R>(f(hi - 1));
        R::axiom_eqv_symmetric(R::zero().add(f(hi - 1)), f(hi - 1));
        // f(lo) ≡ f(hi-1) [definitionally equal since hi-1 == lo]
        R::axiom_eqv_reflexive(f(lo));
        // f(lo).add(R::zero()) ≡ f(lo) ≡ 0.add(f(hi-1)) = sum(f,lo,hi-1).add(f(hi-1))
        R::axiom_eqv_transitive(
            f(lo).add(R::zero()),
            f(lo),
            R::zero().add(f(hi - 1)),
        );
    } else {
        // sum(f, lo, hi) = f(lo) + sum(f, lo+1, hi)
        // IH: sum(f, lo+1, hi) ≡ sum(f, lo+1, hi-1) + f(hi-1)
        lemma_sum_peel_last::<R>(f, lo + 1, hi);

        // f(lo) + sum(f, lo+1, hi) ≡ f(lo) + (sum(f, lo+1, hi-1) + f(hi-1))
        additive_group_lemmas::lemma_add_congruence_right::<R>(
            f(lo),
            sum::<R>(f, lo + 1, hi),
            sum::<R>(f, lo + 1, hi - 1).add(f(hi - 1)),
        );

        // f(lo) + (sum(f, lo+1, hi-1) + f(hi-1)) ≡ (f(lo) + sum(f, lo+1, hi-1)) + f(hi-1)
        R::axiom_add_associative(f(lo), sum::<R>(f, lo + 1, hi - 1), f(hi - 1));
        R::axiom_eqv_symmetric(
            f(lo).add(sum::<R>(f, lo + 1, hi - 1).add(f(hi - 1))),
            f(lo).add(sum::<R>(f, lo + 1, hi - 1)).add(f(hi - 1)),
        );

        // (f(lo) + sum(f, lo+1, hi-1)) = sum(f, lo, hi-1) [definitional]
        R::axiom_eqv_reflexive(sum::<R>(f, lo, hi - 1).add(f(hi - 1)));

        // Chain
        R::axiom_eqv_transitive(
            f(lo).add(sum::<R>(f, lo + 1, hi)),
            f(lo).add(sum::<R>(f, lo + 1, hi - 1).add(f(hi - 1))),
            f(lo).add(sum::<R>(f, lo + 1, hi - 1)).add(f(hi - 1)),
        );
    }
}

/// Congruence: if f(i) ≡ g(i) for all lo ≤ i < hi, then sum(f) ≡ sum(g).
pub proof fn lemma_sum_congruence<R: Ring>(
    f: spec_fn(int) -> R,
    g: spec_fn(int) -> R,
    lo: int,
    hi: int,
)
    requires
        forall|i: int| lo <= i < hi ==> (#[trigger] f(i)).eqv(g(i)),
    ensures
        sum::<R>(f, lo, hi).eqv(sum::<R>(g, lo, hi)),
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if hi <= lo {
        R::axiom_eqv_reflexive(R::zero());
    } else {
        // IH
        lemma_sum_congruence::<R>(f, g, lo + 1, hi);
        // f(lo) ≡ g(lo)
        assert(f(lo).eqv(g(lo)));
        // f(lo) + sum(f, lo+1, hi) ≡ g(lo) + sum(g, lo+1, hi)
        additive_group_lemmas::lemma_add_congruence::<R>(
            f(lo), g(lo),
            sum::<R>(f, lo + 1, hi), sum::<R>(g, lo + 1, hi),
        );
    }
}

/// Split: sum(f, lo, hi) ≡ sum(f, lo, mid) + sum(f, mid, hi) when lo ≤ mid ≤ hi.
pub proof fn lemma_sum_split<R: Ring>(
    f: spec_fn(int) -> R,
    lo: int,
    mid: int,
    hi: int,
)
    requires
        lo <= mid,
        mid <= hi,
    ensures
        sum::<R>(f, lo, hi).eqv(sum::<R>(f, lo, mid).add(sum::<R>(f, mid, hi))),
    decreases mid - lo,
{
    if lo == mid {
        // sum(f, lo, hi) = sum(f, mid, hi) [definitional since lo == mid]
        // sum(f, lo, mid) = R::zero() [definitional since lo == mid]
        // Need: sum(f, mid, hi).eqv(R::zero().add(sum(f, mid, hi)))
        assert(sum::<R>(f, lo, mid) == R::zero());
        additive_group_lemmas::lemma_add_zero_left::<R>(sum::<R>(f, mid, hi));
        R::axiom_eqv_symmetric(
            R::zero().add(sum::<R>(f, mid, hi)),
            sum::<R>(f, mid, hi),
        );
    } else {
        // lo < mid, so sum(f, lo, hi) = f(lo) + sum(f, lo+1, hi)
        // IH: sum(f, lo+1, hi) ≡ sum(f, lo+1, mid) + sum(f, mid, hi)
        lemma_sum_split::<R>(f, lo + 1, mid, hi);

        // f(lo) + sum(f, lo+1, hi) ≡ f(lo) + (sum(f, lo+1, mid) + sum(f, mid, hi))
        additive_group_lemmas::lemma_add_congruence_right::<R>(
            f(lo),
            sum::<R>(f, lo + 1, hi),
            sum::<R>(f, lo + 1, mid).add(sum::<R>(f, mid, hi)),
        );

        // f(lo) + (sum(f, lo+1, mid) + sum(f, mid, hi)) ≡ (f(lo) + sum(f, lo+1, mid)) + sum(f, mid, hi)
        R::axiom_add_associative(f(lo), sum::<R>(f, lo + 1, mid), sum::<R>(f, mid, hi));
        R::axiom_eqv_symmetric(
            f(lo).add(sum::<R>(f, lo + 1, mid).add(sum::<R>(f, mid, hi))),
            f(lo).add(sum::<R>(f, lo + 1, mid)).add(sum::<R>(f, mid, hi)),
        );

        // (f(lo) + sum(f, lo+1, mid)) = sum(f, lo, mid) [definitional when lo < mid]
        // Chain
        R::axiom_eqv_transitive(
            f(lo).add(sum::<R>(f, lo + 1, hi)),
            f(lo).add(sum::<R>(f, lo + 1, mid).add(sum::<R>(f, mid, hi))),
            f(lo).add(sum::<R>(f, lo + 1, mid)).add(sum::<R>(f, mid, hi)),
        );
    }
}

/// Linearity (addition): sum(f+g) ≡ sum(f) + sum(g).
pub proof fn lemma_sum_add<R: Ring>(
    f: spec_fn(int) -> R,
    g: spec_fn(int) -> R,
    lo: int,
    hi: int,
)
    ensures
        sum::<R>(|i: int| f(i).add(g(i)), lo, hi).eqv(
            sum::<R>(f, lo, hi).add(sum::<R>(g, lo, hi))
        ),
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if hi <= lo {
        // 0 ≡ 0 + 0
        additive_group_lemmas::lemma_add_zero_left::<R>(R::zero());
        R::axiom_eqv_symmetric(R::zero().add(R::zero()), R::zero());
    } else {
        let h = |i: int| -> R { f(i).add(g(i)) };
        // IH: sum(h, lo+1, hi) ≡ sum(f, lo+1, hi) + sum(g, lo+1, hi)
        lemma_sum_add::<R>(f, g, lo + 1, hi);

        // sum(h, lo, hi) = h(lo) + sum(h, lo+1, hi)
        //                = (f(lo)+g(lo)) + sum(h, lo+1, hi)
        // ≡ (f(lo)+g(lo)) + (sum(f,lo+1,hi) + sum(g,lo+1,hi))   [by IH]
        additive_group_lemmas::lemma_add_congruence_right::<R>(
            f(lo).add(g(lo)),
            sum::<R>(h, lo + 1, hi),
            sum::<R>(f, lo + 1, hi).add(sum::<R>(g, lo + 1, hi)),
        );

        // (f(lo)+g(lo)) + (sum_f + sum_g) ≡ (f(lo)+sum_f) + (g(lo)+sum_g)
        // This is lemma_add_rearrange_2x2(f(lo), g(lo), sum_f, sum_g)
        additive_group_lemmas::lemma_add_rearrange_2x2::<R>(
            f(lo), g(lo),
            sum::<R>(f, lo + 1, hi), sum::<R>(g, lo + 1, hi),
        );

        // Chain
        R::axiom_eqv_transitive(
            f(lo).add(g(lo)).add(sum::<R>(h, lo + 1, hi)),
            f(lo).add(g(lo)).add(sum::<R>(f, lo + 1, hi).add(sum::<R>(g, lo + 1, hi))),
            f(lo).add(sum::<R>(f, lo + 1, hi)).add(g(lo).add(sum::<R>(g, lo + 1, hi))),
        );
    }
}

/// Scaling: sum(k*f) ≡ k * sum(f).
pub proof fn lemma_sum_scale<R: Ring>(
    k: R,
    f: spec_fn(int) -> R,
    lo: int,
    hi: int,
)
    ensures
        sum::<R>(|i: int| k.mul(f(i)), lo, hi).eqv(
            k.mul(sum::<R>(f, lo, hi))
        ),
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if hi <= lo {
        // sum of empty = 0, k*0 ≡ 0
        R::axiom_mul_zero_right(k);
        R::axiom_eqv_symmetric(k.mul(R::zero()), R::zero());
    } else {
        let g = |i: int| -> R { k.mul(f(i)) };
        // IH: sum(g, lo+1, hi) ≡ k * sum(f, lo+1, hi)
        lemma_sum_scale::<R>(k, f, lo + 1, hi);

        // sum(g, lo, hi) = g(lo) + sum(g, lo+1, hi)
        //                = k*f(lo) + sum(g, lo+1, hi)
        // ≡ k*f(lo) + k*sum(f, lo+1, hi)   [by IH]
        additive_group_lemmas::lemma_add_congruence_right::<R>(
            k.mul(f(lo)),
            sum::<R>(g, lo + 1, hi),
            k.mul(sum::<R>(f, lo + 1, hi)),
        );

        // k*f(lo) + k*sum(f, lo+1, hi) ≡ k*(f(lo) + sum(f, lo+1, hi))
        R::axiom_mul_distributes_left(k, f(lo), sum::<R>(f, lo + 1, hi));
        R::axiom_eqv_symmetric(
            k.mul(f(lo).add(sum::<R>(f, lo + 1, hi))),
            k.mul(f(lo)).add(k.mul(sum::<R>(f, lo + 1, hi))),
        );

        // Chain
        R::axiom_eqv_transitive(
            k.mul(f(lo)).add(sum::<R>(g, lo + 1, hi)),
            k.mul(f(lo)).add(k.mul(sum::<R>(f, lo + 1, hi))),
            k.mul(f(lo).add(sum::<R>(f, lo + 1, hi))),
        );
    }
}

/// Telescoping: sum(f(i+1) - f(i), lo, hi) ≡ f(hi) - f(lo) when lo ≤ hi.
pub proof fn lemma_sum_telescoping<R: Ring>(
    f: spec_fn(int) -> R,
    lo: int,
    hi: int,
)
    requires
        lo <= hi,
    ensures
        sum::<R>(|i: int| f(i + 1).sub(f(i)), lo, hi).eqv(f(hi).sub(f(lo))),
    decreases hi - lo,
{
    let d = |i: int| -> R { f(i + 1).sub(f(i)) };
    if lo == hi {
        // sum = 0, f(hi) - f(lo) = f(lo) - f(lo) ≡ 0
        additive_group_lemmas::lemma_sub_self::<R>(f(lo));
        R::axiom_eqv_symmetric(f(lo).sub(f(lo)), R::zero());
    } else {
        // IH: sum(d, lo+1, hi) ≡ f(hi) - f(lo+1)
        lemma_sum_telescoping::<R>(f, lo + 1, hi);

        // sum(d, lo, hi) = d(lo) + sum(d, lo+1, hi)
        //                = (f(lo+1) - f(lo)) + sum(d, lo+1, hi)
        // ≡ (f(lo+1) - f(lo)) + (f(hi) - f(lo+1))   [by IH]
        additive_group_lemmas::lemma_add_congruence_right::<R>(
            f(lo + 1).sub(f(lo)),
            sum::<R>(d, lo + 1, hi),
            f(hi).sub(f(lo + 1)),
        );

        // (f(lo+1) - f(lo)) + (f(hi) - f(lo+1))
        // Use sub_add_sub: (a-b) + (b-c) ≡ (a-c) with a=f(hi), b=f(lo+1), c=f(lo)
        // Wait, sub_add_sub gives (a-b)+(b-c) ≡ (a-c).
        // We have (f(lo+1)-f(lo)) + (f(hi)-f(lo+1)).
        // By commutativity, this ≡ (f(hi)-f(lo+1)) + (f(lo+1)-f(lo))
        // Then sub_add_sub with a=f(hi), b=f(lo+1), c=f(lo) gives f(hi)-f(lo).
        R::axiom_add_commutative(
            f(lo + 1).sub(f(lo)),
            f(hi).sub(f(lo + 1)),
        );

        // Chain: (f(lo+1)-f(lo)) + (f(hi)-f(lo+1)) ≡ (f(hi)-f(lo+1)) + (f(lo+1)-f(lo))
        R::axiom_eqv_transitive(
            f(lo + 1).sub(f(lo)).add(sum::<R>(d, lo + 1, hi)),
            f(lo + 1).sub(f(lo)).add(f(hi).sub(f(lo + 1))),
            f(hi).sub(f(lo + 1)).add(f(lo + 1).sub(f(lo))),
        );

        // (f(hi)-f(lo+1)) + (f(lo+1)-f(lo)) ≡ f(hi)-f(lo)
        additive_group_lemmas::lemma_sub_add_sub::<R>(f(hi), f(lo + 1), f(lo));

        // Final chain
        R::axiom_eqv_transitive(
            f(lo + 1).sub(f(lo)).add(sum::<R>(d, lo + 1, hi)),
            f(hi).sub(f(lo + 1)).add(f(lo + 1).sub(f(lo))),
            f(hi).sub(f(lo)),
        );
    }
}

/// Index shift: sum(f, lo, hi) ≡ sum(|i| f(i + k), lo - k, hi - k).
pub proof fn lemma_sum_reindex<R: Ring>(
    f: spec_fn(int) -> R,
    lo: int,
    hi: int,
    k: int,
)
    ensures
        sum::<R>(f, lo, hi).eqv(sum::<R>(|i: int| f(i + k), lo - k, hi - k)),
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    let g = |i: int| -> R { f(i + k) };
    if hi <= lo {
        R::axiom_eqv_reflexive(R::zero());
    } else {
        // IH: sum(f, lo+1, hi) ≡ sum(g, lo+1-k, hi-k)
        lemma_sum_reindex::<R>(f, lo + 1, hi, k);
        // Note: lo+1-k = (lo-k)+1
        assert((lo + 1 - k) == (lo - k) + 1);

        // f(lo) ≡ g(lo - k) since g(lo-k) = f((lo-k)+k) = f(lo)
        R::axiom_eqv_reflexive(f(lo));

        // f(lo) + sum(f, lo+1, hi) ≡ g(lo-k) + sum(g, (lo-k)+1, hi-k)
        additive_group_lemmas::lemma_add_congruence::<R>(
            f(lo), f(lo),
            sum::<R>(f, lo + 1, hi), sum::<R>(g, lo - k + 1, hi - k),
        );
    }
}

/// Nonnegativity: if f(i) ≥ 0 for all i in [lo, hi), then sum(f) ≥ 0.
pub proof fn lemma_sum_nonneg<R: OrderedRing>(
    f: spec_fn(int) -> R,
    lo: int,
    hi: int,
)
    requires
        forall|i: int| lo <= i < hi ==> R::zero().le(#[trigger] f(i)),
    ensures
        R::zero().le(sum::<R>(f, lo, hi)),
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if hi <= lo {
        R::axiom_le_reflexive(R::zero());
    } else {
        lemma_sum_nonneg::<R>(f, lo + 1, hi);
        // 0 ≤ f(lo) and 0 ≤ sum(f, lo+1, hi)
        // → 0 ≤ f(lo) + sum(f, lo+1, hi) = sum(f, lo, hi)
        inequalities::lemma_nonneg_add::<R>(f(lo), sum::<R>(f, lo + 1, hi));
    }
}

/// Monotonicity: if f(i) ≤ g(i) for all i in [lo, hi), then sum(f) ≤ sum(g).
pub proof fn lemma_sum_monotone<R: OrderedRing>(
    f: spec_fn(int) -> R,
    g: spec_fn(int) -> R,
    lo: int,
    hi: int,
)
    requires
        forall|i: int| lo <= i < hi ==> (#[trigger] f(i)).le(g(i)),
    ensures
        sum::<R>(f, lo, hi).le(sum::<R>(g, lo, hi)),
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    if hi <= lo {
        R::axiom_le_reflexive(R::zero());
    } else {
        // IH: sum(f, lo+1, hi) ≤ sum(g, lo+1, hi)
        lemma_sum_monotone::<R>(f, g, lo + 1, hi);
        // f(lo) ≤ g(lo)
        assert(f(lo).le(g(lo)));
        // f(lo) + sum(f, lo+1, hi) ≤ g(lo) + sum(g, lo+1, hi)
        ordered_ring_lemmas::lemma_le_add_both::<R>(
            f(lo), g(lo),
            sum::<R>(f, lo + 1, hi), sum::<R>(g, lo + 1, hi),
        );
    }
}

/// Reverse: sum(f, lo, hi) ≡ sum(|i| f(lo + hi - 1 - i), lo, hi).
pub proof fn lemma_sum_reverse<R: Ring>(
    f: spec_fn(int) -> R,
    lo: int,
    hi: int,
)
    ensures
        sum::<R>(f, lo, hi).eqv(sum::<R>(|i: int| f(lo + hi - 1 - i), lo, hi)),
    decreases (if hi > lo { hi - lo } else { 0 }),
{
    let g = |i: int| -> R { f(lo + hi - 1 - i) };
    if hi <= lo {
        R::axiom_eqv_reflexive(R::zero());
    } else {
        // sum(f, lo, hi) ≡ sum(f, lo, hi-1) + f(hi-1)  [peel last]
        lemma_sum_peel_last::<R>(f, lo, hi);

        // IH: sum(f, lo, hi-1) ≡ sum(|i| f(lo + (hi-1) - 1 - i), lo, hi-1)
        lemma_sum_reverse::<R>(f, lo, hi - 1);

        // The reversed inner function: |i| f(lo + (hi-1) - 1 - i) = |i| f(lo + hi - 2 - i)
        // The outer reversed function: g(lo) = f(lo + hi - 1 - lo) = f(hi - 1)
        // g shifted by 1: |i| g(i+1) for sum(g, lo+1, hi)
        // sum(g, lo, hi) = g(lo) + sum(g, lo+1, hi) = f(hi-1) + sum(g, lo+1, hi)

        // We need sum(g, lo+1, hi) ≡ sum(|i| f(lo+hi-2-i), lo, hi-1)
        // g(i) for i in [lo+1, hi) = f(lo+hi-1-i) for i in [lo+1, hi)
        // Reindex sum(g, lo+1, hi) with shift -1: sum(|j| g(j+1), lo, hi-1)
        // g(j+1) = f(lo+hi-1-(j+1)) = f(lo+hi-2-j)
        // And the inner reversed function is |j| f(lo+(hi-1)-1-j) = |j| f(lo+hi-2-j). Same!

        // So sum(g, lo+1, hi) ≡ sum(|j| f(lo+hi-2-j), lo, hi-1) by reindex
        // And sum(f, lo, hi-1) ≡ sum(|j| f(lo+hi-2-j), lo, hi-1) by IH

        // Therefore sum(f, lo, hi-1) ≡ sum(g, lo+1, hi) [both ≡ same thing]
        // We need to show this via reindex on sum(g, lo+1, hi).

        // Actually let me take a simpler approach.
        // sum(g, lo, hi) = g(lo) + sum(g, lo+1, hi)
        // g(lo) = f(hi-1)
        // We want: sum(f, lo, hi) ≡ sum(g, lo, hi)
        // i.e., sum(f, lo, hi) ≡ f(hi-1) + sum(g, lo+1, hi)

        // From peel_last: sum(f, lo, hi) ≡ sum(f, lo, hi-1) + f(hi-1)
        // By commutativity: sum(f, lo, hi-1) + f(hi-1) ≡ f(hi-1) + sum(f, lo, hi-1)

        R::axiom_add_commutative(sum::<R>(f, lo, hi - 1), f(hi - 1));
        R::axiom_eqv_transitive(
            sum::<R>(f, lo, hi),
            sum::<R>(f, lo, hi - 1).add(f(hi - 1)),
            f(hi - 1).add(sum::<R>(f, lo, hi - 1)),
        );

        // IH gives: sum(f, lo, hi-1) ≡ sum(rev_{lo,hi-1}, lo, hi-1)
        // where rev_{lo,hi-1}(i) = f(lo + (hi-1) - 1 - i) = f(lo + hi - 2 - i)

        // We need: sum(g, lo+1, hi) ≡ sum(f, lo, hi-1)
        // g(i) for i in [lo+1, hi) gives f(lo+hi-1-i)
        // As i goes lo+1..hi, lo+hi-1-i goes hi-2..lo-1, i.e., the values f(lo)..f(hi-2)

        // sum(g, lo+1, hi): reindex j = i - 1, so sum(|j| g(j+1), lo, hi-1)
        lemma_sum_reindex::<R>(g, lo + 1, hi, -1);
        // This gives sum(g, lo+1, hi) ≡ sum(|j| g(j + (-1)), (lo+1)-(-1), hi-(-1))
        // Hmm that's wrong direction. Let me use k=1:
        // lemma_sum_reindex(g, lo+1, hi, 1):
        //   sum(g, lo+1, hi) ≡ sum(|i| g(i+1), (lo+1)-1, hi-1) = sum(|i| g(i+1), lo, hi-1)
        // Wait, let me re-read the lemma. It says:
        //   sum(f, lo, hi) ≡ sum(|i| f(i+k), lo-k, hi-k)
        // So sum(g, lo+1, hi) ≡ sum(|i| g(i+k), (lo+1)-k, hi-k)
        // With k = 1: sum(|i| g(i+1), lo, hi-1)
        // g(i+1) = f(lo + hi - 1 - (i+1)) = f(lo + hi - 2 - i)
        lemma_sum_reindex::<R>(g, lo + 1, hi, 1);
        // sum(g, lo+1, hi) ≡ sum(|i| g(i+1), lo, hi-1)
        // = sum(|i| f(lo+hi-2-i), lo, hi-1)

        // IH: sum(f, lo, hi-1) ≡ sum(|i| f(lo+(hi-1)-1-i), lo, hi-1)
        //   = sum(|i| f(lo+hi-2-i), lo, hi-1)
        // So sum(g, lo+1, hi) ≡ sum(f, lo, hi-1) via transitivity through the shared form.

        // But we need to be careful with function equality for Verus.
        // Actually g(i+1) and f(lo+hi-2-i) are definitionally equal, so Verus should handle it.

        // sum(g, lo+1, hi) ≡ sum(|i| g(i+1), lo, hi-1)  [from reindex]
        // Now we need: sum(|i| g(i+1), lo, hi-1) ≡ sum(|i| f(lo+hi-2-i), lo, hi-1)
        // These are the same function, so reflexive:
        // Actually, they might not be syntactically identical to Verus. Let's use congruence.

        // Congruence: for all i in [lo, hi-1), g(i+1) = f(lo+hi-1-(i+1)) = f(lo+hi-2-i)
        // and the IH reversed function is |i| f(lo + (hi-1) - 1 - i) = |i| f(lo+hi-2-i)
        // These are definitionally equal.

        // Let me try: sum(f, lo, hi-1) has IH giving ≡ to the reversed form.
        // sum(g, lo+1, hi) has reindex giving ≡ to a form involving g(i+1).
        // The key insight: for each i in [lo, hi-1), g(i+1) == f(lo+hi-2-i) definitionally.

        // Let's use congruence between |i| g(i+1) and the reverse of f on [lo, hi-1):
        let g1 = |i: int| -> R { g(i + 1) };
        let rev_inner = |i: int| -> R { f(lo + hi - 2 - i) };

        // These are pointwise equal:
        assert forall|i: int| lo <= i < hi - 1 implies (#[trigger] g1(i)).eqv(rev_inner(i)) by {
            R::axiom_eqv_reflexive(g1(i));
        }
        lemma_sum_congruence::<R>(g1, rev_inner, lo, hi - 1);

        // Now chain: sum(g, lo+1, hi) ≡ sum(g1, lo, hi-1) ≡ sum(rev_inner, lo, hi-1)
        R::axiom_eqv_transitive(
            sum::<R>(g, lo + 1, hi),
            sum::<R>(g1, lo, hi - 1),
            sum::<R>(rev_inner, lo, hi - 1),
        );

        // IH: sum(f, lo, hi-1) ≡ sum(rev_inner, lo, hi-1)
        // (this is exactly what lemma_sum_reverse gives us for the sub-range)
        // sum(f, lo, hi-1) ≡ sum(|i| f(lo+(hi-1)-1-i), lo, hi-1)
        //                   = sum(|i| f(lo+hi-2-i), lo, hi-1)
        //                   = sum(rev_inner, lo, hi-1)

        // So: sum(g, lo+1, hi) ≡ sum(rev_inner, lo, hi-1) ≡ sum(f, lo, hi-1) [symmetric]
        R::axiom_eqv_symmetric(
            sum::<R>(f, lo, hi - 1),
            sum::<R>(rev_inner, lo, hi - 1),
        );
        R::axiom_eqv_transitive(
            sum::<R>(g, lo + 1, hi),
            sum::<R>(rev_inner, lo, hi - 1),
            sum::<R>(f, lo, hi - 1),
        );

        // Now: sum(f, lo, hi) ≡ f(hi-1) + sum(f, lo, hi-1)  [from above]
        // And: f(hi-1) + sum(f, lo, hi-1) ≡ f(hi-1) + sum(g, lo+1, hi)  [swap using congruence]
        R::axiom_eqv_symmetric(
            sum::<R>(g, lo + 1, hi),
            sum::<R>(f, lo, hi - 1),
        );
        additive_group_lemmas::lemma_add_congruence_right::<R>(
            f(hi - 1),
            sum::<R>(f, lo, hi - 1),
            sum::<R>(g, lo + 1, hi),
        );

        // f(hi-1) + sum(g, lo+1, hi) = g(lo) + sum(g, lo+1, hi) = sum(g, lo, hi) [definitional]
        R::axiom_eqv_reflexive(sum::<R>(g, lo, hi));

        // Final chain: sum(f, lo, hi) ≡ f(hi-1) + sum(f, lo, hi-1)
        //              ≡ f(hi-1) + sum(g, lo+1, hi) = sum(g, lo, hi)
        R::axiom_eqv_transitive(
            sum::<R>(f, lo, hi),
            f(hi - 1).add(sum::<R>(f, lo, hi - 1)),
            f(hi - 1).add(sum::<R>(g, lo + 1, hi)),
        );
    }
}

/// Constant function: sum(c, lo, hi) ≡ nat_mul(hi - lo, c) when lo ≤ hi.
pub proof fn lemma_sum_constant<R: Ring>(c: R, lo: int, hi: int)
    requires
        lo <= hi,
    ensures
        sum::<R>(|i: int| c, lo, hi).eqv(nat_mul::<R>((hi - lo) as nat, c)),
    decreases hi - lo,
{
    if lo == hi {
        lemma_nat_mul_zero::<R>(c);
        R::axiom_eqv_symmetric(nat_mul::<R>(0, c), R::zero());
    } else {
        // IH: sum(c, lo+1, hi) ≡ nat_mul(hi-lo-1, c)
        lemma_sum_constant::<R>(c, lo + 1, hi);
        let n = (hi - lo - 1) as nat;

        // sum(c, lo, hi) = c + sum(c, lo+1, hi)
        // ≡ c + nat_mul(n, c)   [by IH]
        additive_group_lemmas::lemma_add_congruence_right::<R>(
            c,
            sum::<R>(|i: int| c, lo + 1, hi),
            nat_mul::<R>(n, c),
        );

        // c + nat_mul(n, c) = nat_mul(n+1, c) [definitional]
        // n+1 = (hi - lo) as nat
        assert(n + 1 == (hi - lo) as nat);
        lemma_nat_mul_succ::<R>(n, c);
        R::axiom_eqv_symmetric(
            nat_mul::<R>(n + 1, c),
            c.add(nat_mul::<R>(n, c)),
        );

        // Chain
        R::axiom_eqv_transitive(
            c.add(sum::<R>(|i: int| c, lo + 1, hi)),
            c.add(nat_mul::<R>(n, c)),
            nat_mul::<R>((hi - lo) as nat, c),
        );
    }
}

} // verus!
