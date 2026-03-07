use vstd::prelude::*;
use verus_algebra::traits::ring::Ring;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::convex::{convex, lemma_convex_bounds};
use crate::summation::{sum, lemma_sum_empty, lemma_sum_single, lemma_sum_congruence, lemma_sum_nonneg, lemma_sum_monotone};

verus! {

// ============================================================
//  Weighted Sum and Weight Sum
// ============================================================

/// Weighted sum: sum(w[i] * p[i], i=0..n).
pub open spec fn weighted_sum<R: Ring>(weights: Seq<R>, points: Seq<R>, n: nat) -> R {
    sum::<R>(|i: int| weights[i as int].mul(points[i as int]), 0, n as int)
}

/// Weight sum: sum(w[i], i=0..n).
pub open spec fn weight_sum<R: Ring>(weights: Seq<R>, n: nat) -> R {
    sum::<R>(|i: int| weights[i as int], 0, n as int)
}

// ============================================================
//  Lemmas
// ============================================================

/// Empty weighted sum is zero.
pub proof fn lemma_weighted_sum_empty<R: Ring>(weights: Seq<R>, points: Seq<R>)
    ensures
        weighted_sum::<R>(weights, points, 0).eqv(R::zero()),
{
    R::axiom_eqv_reflexive(R::zero());
}

/// Single-point weighted sum: w[0] * p[0].
pub proof fn lemma_weighted_sum_single<R: Ring>(weights: Seq<R>, points: Seq<R>)
    requires
        weights.len() >= 1,
        points.len() >= 1,
    ensures
        weighted_sum::<R>(weights, points, 1).eqv(weights[0].mul(points[0])),
{
    let f = |i: int| -> R { weights[i as int].mul(points[i as int]) };
    lemma_sum_single::<R>(f, 0);
}

/// Congruence: if weights and points are pairwise equivalent, sums are equivalent.
pub proof fn lemma_weighted_sum_congruence<R: Ring>(
    w1: Seq<R>,
    p1: Seq<R>,
    w2: Seq<R>,
    p2: Seq<R>,
    n: nat,
)
    requires
        w1.len() >= n,
        p1.len() >= n,
        w2.len() >= n,
        p2.len() >= n,
        forall|i: int| 0 <= i < n as int ==> (#[trigger] w1[i]).eqv(w2[i]),
        forall|i: int| 0 <= i < n as int ==> (#[trigger] p1[i]).eqv(p2[i]),
    ensures
        weighted_sum::<R>(w1, p1, n).eqv(weighted_sum::<R>(w2, p2, n)),
{
    let f1 = |i: int| -> R { w1[i as int].mul(p1[i as int]) };
    let f2 = |i: int| -> R { w2[i as int].mul(p2[i as int]) };

    assert forall|i: int| 0 <= i < n as int implies (#[trigger] f1(i)).eqv(f2(i)) by {
        ring_lemmas::lemma_mul_congruence::<R>(
            w1[i as int], w2[i as int],
            p1[i as int], p2[i as int],
        );
    }

    lemma_sum_congruence::<R>(f1, f2, 0, n as int);
}

/// Two-point convex combination reduces to existing `convex(a, b, t)`.
/// weighted_sum([t, 1-t], [a, b], 2) ≡ t*a + (1-t)*b = convex(a, b, t).
pub proof fn lemma_convex_combination_2<F: OrderedField>(
    a: F,
    b: F,
    t: F,
)
    ensures
        weighted_sum::<F>(
            seq![t, F::one().sub(t)],
            seq![a, b],
            2,
        ).eqv(convex::<F>(a, b, t)),
{
    let w = seq![t, F::one().sub(t)];
    let p = seq![a, b];
    let f = |i: int| -> F { w[i as int].mul(p[i as int]) };

    // weighted_sum = sum(f, 0, 2)
    // = f(0) + sum(f, 1, 2)
    // = f(0) + f(1) + sum(f, 2, 2)
    // = f(0) + f(1) + 0
    // = t*a + (1-t)*b

    // sum(f, 0, 2) = f(0) + sum(f, 1, 2)
    // sum(f, 1, 2) = f(1) + sum(f, 2, 2) = f(1) + 0

    // f(0) = t * a
    assert(f(0int) == t.mul(a));
    // f(1) = (1-t) * b
    assert(f(1int) == F::one().sub(t).mul(b));

    // sum(f, 1, 2) ≡ f(1)
    lemma_sum_single::<F>(f, 1int);

    // sum(f, 0, 2) = f(0) + sum(f, 1, 2) ≡ f(0) + f(1) = t*a + (1-t)*b
    additive_group_lemmas::lemma_add_congruence_right::<F>(
        f(0int),
        sum::<F>(f, 1, 2),
        f(1int),
    );
    // gives: f(0) + sum(f, 1, 2) ≡ f(0) + f(1) = t*a + (1-t)*b

    // convex(a, b, t) = t*a + (1-t)*b [definitional]
    F::axiom_eqv_reflexive(t.mul(a).add(F::one().sub(t).mul(b)));
}

/// Convex combination bounds: if weights are nonneg, sum to 1, and all points
/// are between lo and hi, then the weighted sum is between lo and hi.
pub proof fn lemma_convex_combination_bounds<F: OrderedField>(
    weights: Seq<F>,
    points: Seq<F>,
    n: nat,
    lo: F,
    hi: F,
)
    requires
        weights.len() >= n,
        points.len() >= n,
        n > 0,
        forall|i: int| 0 <= i < n as int ==> F::zero().le(#[trigger] weights[i]),
        forall|i: int| 0 <= i < n as int ==> lo.le(#[trigger] points[i]),
        forall|i: int| 0 <= i < n as int ==> (#[trigger] points[i]).le(hi),
        weight_sum::<F>(weights, n).eqv(F::one()),
        lo.le(hi),
    ensures
        lo.le(weighted_sum::<F>(weights, points, n)),
        weighted_sum::<F>(weights, points, n).le(hi),
{
    let f = |i: int| -> F { weights[i as int].mul(points[i as int]) };
    let f_lo = |i: int| -> F { weights[i as int].mul(lo) };
    let f_hi = |i: int| -> F { weights[i as int].mul(hi) };

    // For each i: w[i] * lo ≤ w[i] * p[i] ≤ w[i] * hi
    // because w[i] ≥ 0 and lo ≤ p[i] ≤ hi

    // Lower bound: sum(w[i]*lo) ≤ sum(w[i]*p[i])
    assert forall|i: int| 0 <= i < n as int implies (#[trigger] f_lo(i)).le(f(i)) by {
        F::axiom_le_mul_nonneg_monotone(lo, points[i as int], weights[i as int]);
        F::axiom_mul_commutative(lo, weights[i as int]);
        F::axiom_mul_commutative(points[i as int], weights[i as int]);
        F::axiom_le_congruence(
            lo.mul(weights[i as int]),
            weights[i as int].mul(lo),
            points[i as int].mul(weights[i as int]),
            weights[i as int].mul(points[i as int]),
        );
    }

    lemma_sum_monotone::<F>(f_lo, f, 0, n as int);

    // Use a named weight function so closures unify across lemma calls
    let g = |i: int| -> F { weights[i as int] };

    // sum(f_lo) ≡ sum(|i| lo*g(i)) by commutativity pointwise
    assert forall|i: int| 0 <= i < n as int implies (#[trigger] f_lo(i)).eqv(lo.mul(g(i))) by {
        F::axiom_mul_commutative(weights[i as int], lo);
    }
    lemma_sum_congruence::<F>(f_lo, |i: int| lo.mul(g(i)), 0, n as int);

    // sum(|i| lo*g(i)) ≡ lo * sum(g) by sum_scale
    crate::summation::lemma_sum_scale::<F>(lo, g, 0, n as int);

    // Chain: sum(f_lo) ≡ sum(|i| lo*g(i)) ≡ lo * sum(g) = lo * weight_sum
    F::axiom_eqv_transitive(
        sum::<F>(f_lo, 0, n as int),
        sum::<F>(|i: int| lo.mul(g(i)), 0, n as int),
        lo.mul(sum::<F>(g, 0, n as int)),
    );

    // lo * weight_sum ≡ lo * 1
    ring_lemmas::lemma_mul_congruence_right::<F>(
        lo,
        weight_sum::<F>(weights, n),
        F::one(),
    );
    // lo * 1 ≡ lo
    F::axiom_mul_one_right(lo);

    F::axiom_eqv_transitive(
        sum::<F>(f_lo, 0, n as int),
        lo.mul(weight_sum::<F>(weights, n)),
        lo.mul(F::one()),
    );
    F::axiom_eqv_transitive(
        sum::<F>(f_lo, 0, n as int),
        lo.mul(F::one()),
        lo,
    );

    // sum(f_lo) ≡ lo, sum(f_lo) ≤ sum(f) → lo ≤ sum(f)
    F::axiom_eqv_symmetric(sum::<F>(f_lo, 0, n as int), lo);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        sum::<F>(f_lo, 0, n as int),
        lo,
        sum::<F>(f, 0, n as int),
    );

    // Upper bound: sum(w[i]*p[i]) ≤ sum(w[i]*hi)
    assert forall|i: int| 0 <= i < n as int implies (#[trigger] f(i)).le(f_hi(i)) by {
        F::axiom_le_mul_nonneg_monotone(points[i as int], hi, weights[i as int]);
        F::axiom_mul_commutative(points[i as int], weights[i as int]);
        F::axiom_mul_commutative(hi, weights[i as int]);
        F::axiom_le_congruence(
            points[i as int].mul(weights[i as int]),
            weights[i as int].mul(points[i as int]),
            hi.mul(weights[i as int]),
            weights[i as int].mul(hi),
        );
    }

    lemma_sum_monotone::<F>(f, f_hi, 0, n as int);

    // sum(f_hi) ≡ sum(|i| hi*g(i)) by commutativity pointwise
    assert forall|i: int| 0 <= i < n as int implies (#[trigger] f_hi(i)).eqv(hi.mul(g(i))) by {
        F::axiom_mul_commutative(weights[i as int], hi);
    }
    lemma_sum_congruence::<F>(f_hi, |i: int| hi.mul(g(i)), 0, n as int);

    // sum(|i| hi*g(i)) ≡ hi * sum(g) by sum_scale
    crate::summation::lemma_sum_scale::<F>(hi, g, 0, n as int);

    // Chain: sum(f_hi) ≡ sum(|i| hi*g(i)) ≡ hi * sum(g) = hi * weight_sum
    F::axiom_eqv_transitive(
        sum::<F>(f_hi, 0, n as int),
        sum::<F>(|i: int| hi.mul(g(i)), 0, n as int),
        hi.mul(sum::<F>(g, 0, n as int)),
    );

    ring_lemmas::lemma_mul_congruence_right::<F>(
        hi,
        weight_sum::<F>(weights, n),
        F::one(),
    );
    F::axiom_mul_one_right(hi);

    F::axiom_eqv_transitive(
        sum::<F>(f_hi, 0, n as int),
        hi.mul(weight_sum::<F>(weights, n)),
        hi.mul(F::one()),
    );
    F::axiom_eqv_transitive(
        sum::<F>(f_hi, 0, n as int),
        hi.mul(F::one()),
        hi,
    );

    // sum(f) ≤ sum(f_hi) ≡ hi → sum(f) ≤ hi
    F::axiom_eqv_symmetric(sum::<F>(f_hi, 0, n as int), hi);
    ordered_ring_lemmas::lemma_le_congruence_right::<F>(
        sum::<F>(f, 0, n as int),
        sum::<F>(f_hi, 0, n as int),
        hi,
    );
}

} // verus!
