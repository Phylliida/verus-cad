use vstd::prelude::*;
use verus_algebra::traits::ring::Ring;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use crate::summation::{sum, lemma_sum_telescoping};

verus! {

// ============================================================
//  Forward Difference Operator
// ============================================================

/// Forward difference: Δf(i) = f(i+1) - f(i).
pub open spec fn forward_diff<R: Ring>(f: spec_fn(int) -> R, i: int) -> R {
    f(i + 1).sub(f(i))
}

// ============================================================
//  Lemmas
// ============================================================

/// Fundamental theorem of finite differences: sum of differences telescopes.
/// sum(Δf, lo, hi) ≡ f(hi) - f(lo) when lo ≤ hi.
pub proof fn lemma_diff_sum<R: Ring>(f: spec_fn(int) -> R, lo: int, hi: int)
    requires
        lo <= hi,
    ensures
        sum::<R>(|i: int| forward_diff::<R>(f, i), lo, hi).eqv(f(hi).sub(f(lo))),
{
    // forward_diff(f, i) == f(i+1).sub(f(i)) definitionally
    // The telescoping lemma uses |i| f(i+1).sub(f(i)) directly
    lemma_sum_telescoping::<R>(f, lo, hi);
    // gives: sum(|i| f(i+1).sub(f(i)), lo, hi).eqv(f(hi).sub(f(lo)))

    // Need: sum(|i| forward_diff(f, i), lo, hi) ≡ sum(|i| f(i+1).sub(f(i)), lo, hi)
    // These are the same function, but Verus may not see it. Use congruence.
    let d1 = |i: int| -> R { forward_diff::<R>(f, i) };
    let d2 = |i: int| -> R { f(i + 1).sub(f(i)) };
    assert forall|i: int| lo <= i < hi implies (#[trigger] d1(i)).eqv(d2(i)) by {
        R::axiom_eqv_reflexive(d1(i));
    }
    crate::summation::lemma_sum_congruence::<R>(d1, d2, lo, hi);
    R::axiom_eqv_transitive(
        sum::<R>(d1, lo, hi),
        sum::<R>(d2, lo, hi),
        f(hi).sub(f(lo)),
    );
}

/// Difference of a linear function: Δ(k*f)(i) ≡ k * Δf(i).
pub proof fn lemma_diff_scale<R: Ring>(k: R, f: spec_fn(int) -> R, i: int)
    ensures
        forward_diff::<R>(|j: int| k.mul(f(j)), i).eqv(k.mul(forward_diff::<R>(f, i))),
{
    // Δ(k*f)(i) = k*f(i+1) - k*f(i)
    // k*Δf(i) = k*(f(i+1) - f(i))
    // k*f(i+1) - k*f(i) ≡ k*(f(i+1) - f(i))  by mul_distributes_over_sub reversed

    // k*f(i+1) - k*f(i) ≡ k*(f(i+1) - f(i))
    ring_lemmas::lemma_mul_distributes_over_sub::<R>(k, f(i + 1), f(i));
    // gives: k.mul(f(i+1).sub(f(i))).eqv(k.mul(f(i+1)).sub(k.mul(f(i))))
    R::axiom_eqv_symmetric(
        k.mul(f(i + 1).sub(f(i))),
        k.mul(f(i + 1)).sub(k.mul(f(i))),
    );
    // gives: k.mul(f(i+1)).sub(k.mul(f(i))).eqv(k.mul(f(i+1).sub(f(i))))

    // forward_diff(|j| k*f(j), i) = k*f(i+1) - k*f(i) [definitional]
    // k*forward_diff(f, i) = k*(f(i+1)-f(i)) [definitional]
}

/// Difference of a constant is zero: Δc ≡ 0.
pub proof fn lemma_diff_constant<R: Ring>(c: R, i: int)
    ensures
        forward_diff::<R>(|_j: int| c, i).eqv(R::zero()),
{
    // c - c ≡ 0
    additive_group_lemmas::lemma_sub_self::<R>(c);
}

/// Difference of a sum: Δ(f+g)(i) ≡ Δf(i) + Δg(i).
pub proof fn lemma_diff_add<R: Ring>(
    f: spec_fn(int) -> R,
    g: spec_fn(int) -> R,
    i: int,
)
    ensures
        forward_diff::<R>(|j: int| f(j).add(g(j)), i).eqv(
            forward_diff::<R>(f, i).add(forward_diff::<R>(g, i))
        ),
{
    // Δ(f+g)(i) = (f(i+1)+g(i+1)) - (f(i)+g(i))
    // Δf(i) + Δg(i) = (f(i+1)-f(i)) + (g(i+1)-g(i))

    // (f(i+1)+g(i+1)) - (f(i)+g(i)) ≡ ... ≡ (f(i+1)-f(i)) + (g(i+1)-g(i))
    // Expand sub as add-neg:
    // (a+b) - (c+d) = (a+b) + (-(c+d)) = (a+b) + (-c + -d)
    // = a + b + (-c) + (-d) = (a + (-c)) + (b + (-d)) = (a-c) + (b-d)

    let a = f(i + 1);
    let b = g(i + 1);
    let c = f(i);
    let d = g(i);

    // (a+b).sub(c+d) ≡ (a+b).add((c+d).neg())
    R::axiom_sub_is_add_neg(a.add(b), c.add(d));

    // (c+d).neg() ≡ c.neg() + d.neg()
    additive_group_lemmas::lemma_neg_add::<R>(c, d);
    // gives: c.add(d).neg().eqv(c.neg().add(d.neg()))

    // (a+b) + (c+d).neg() ≡ (a+b) + (c.neg()+d.neg())
    additive_group_lemmas::lemma_add_congruence_right::<R>(
        a.add(b), c.add(d).neg(), c.neg().add(d.neg()),
    );

    // Chain: (a+b)-(c+d) ≡ (a+b)+(c.neg()+d.neg())
    R::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(b).add(c.add(d).neg()),
        a.add(b).add(c.neg().add(d.neg())),
    );

    // (a+b) + (c.neg()+d.neg()) ≡ (a+c.neg()) + (b+d.neg())  by rearrange_2x2
    additive_group_lemmas::lemma_add_rearrange_2x2::<R>(a, b, c.neg(), d.neg());

    R::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(b).add(c.neg().add(d.neg())),
        a.add(c.neg()).add(b.add(d.neg())),
    );

    // a+c.neg() ≡ a-c  and  b+d.neg() ≡ b-d
    R::axiom_sub_is_add_neg(a, c);
    R::axiom_eqv_symmetric(a.sub(c), a.add(c.neg()));
    R::axiom_sub_is_add_neg(b, d);
    R::axiom_eqv_symmetric(b.sub(d), b.add(d.neg()));

    additive_group_lemmas::lemma_add_congruence::<R>(
        a.add(c.neg()), a.sub(c),
        b.add(d.neg()), b.sub(d),
    );

    R::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(c.neg()).add(b.add(d.neg())),
        a.sub(c).add(b.sub(d)),
    );
}

/// Difference of negation: Δ(-f)(i) ≡ -(Δf(i)).
pub proof fn lemma_diff_neg<R: Ring>(f: spec_fn(int) -> R, i: int)
    ensures
        forward_diff::<R>(|j: int| f(j).neg(), i).eqv(
            forward_diff::<R>(f, i).neg()
        ),
{
    // Δ(-f)(i) = (-f(i+1)) - (-f(i)) = f(i+1).neg() - f(i).neg()
    // (Δf(i)).neg() = (f(i+1) - f(i)).neg()
    // f(i+1).neg() - f(i).neg() ≡ (f(i) - f(i+1)) by sub_neg_both
    // (f(i+1) - f(i)).neg() ≡ f(i) - f(i+1)  by sub_antisymmetric

    // sub_neg_both: a.neg().sub(b.neg()).eqv(b.sub(a))
    additive_group_lemmas::lemma_sub_neg_both::<R>(f(i + 1), f(i));
    // gives: f(i+1).neg().sub(f(i).neg()).eqv(f(i).sub(f(i+1)))

    // sub_antisymmetric(f(i+1), f(i)): f(i+1).sub(f(i)).eqv(f(i).sub(f(i+1)).neg())
    additive_group_lemmas::lemma_sub_antisymmetric::<R>(f(i + 1), f(i));

    // We need: f(i).sub(f(i+1)).eqv(f(i+1).sub(f(i)).neg())
    // sub_antisymmetric(f(i), f(i+1)): f(i).sub(f(i+1)).eqv(f(i+1).sub(f(i)).neg())
    additive_group_lemmas::lemma_sub_antisymmetric::<R>(f(i), f(i + 1));

    // Chain: f(i+1).neg().sub(f(i).neg()) ≡ f(i).sub(f(i+1)) ≡ f(i+1).sub(f(i)).neg()
    R::axiom_eqv_transitive(
        f(i + 1).neg().sub(f(i).neg()),
        f(i).sub(f(i + 1)),
        f(i + 1).sub(f(i)).neg(),
    );
}

} // verus!
