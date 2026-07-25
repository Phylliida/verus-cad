//! Scalar and vector type aliases + tiny ordering helpers (SPEC §1).
//!
//! Exec scalar: RuntimeRational (bigint-backed exact rational, ghost model
//! Rational). Exec vector: RuntimeVec2<RuntimeRational, Rational>.

use vstd::prelude::*;

use verus_algebra::traits::*;
use verus_linalg::runtime::vec2::RuntimeVec2;
use verus_rational::{Rational, RuntimeRational};

verus! {

/// Exec-level exact scalar.
pub type Scalar = RuntimeRational;

/// Exec-level exact 2D vector (ghost model Vec2<Rational>).
pub type SVec2 = RuntimeVec2<RuntimeRational, Rational>;

// ── Qualified spec aliases ─────────────────────────────────────────────
// Rational carries inherent PROOF fns named zero/one/add/mul (witness
// constructors), which shadow the trait spec fns under plain method-call
// syntax in spec mode. These aliases pin the trait spec ops once; all
// engine specs use q_* forms.

pub open spec fn q_zero() -> Rational {
    <Rational as AdditiveCommutativeMonoid>::zero()
}

pub open spec fn q_one() -> Rational {
    <Rational as Ring>::one()
}

pub open spec fn q_add(a: Rational, b: Rational) -> Rational {
    <Rational as AdditiveCommutativeMonoid>::add(a, b)
}

pub open spec fn q_mul(a: Rational, b: Rational) -> Rational {
    <Rational as Ring>::mul(a, b)
}

pub open spec fn q_eqv(a: Rational, b: Rational) -> bool {
    <Rational as Equivalence>::eqv(a, b)
}

pub open spec fn q_le(a: Rational, b: Rational) -> bool {
    <Rational as PartialOrder>::le(a, b)
}

pub open spec fn q_lt(a: Rational, b: Rational) -> bool {
    <Rational as OrderedRing>::lt(a, b)
}

/// x ≥ 0 at the spec level (OrderedRing order on Rational).
pub open spec fn q_nonneg(x: Rational) -> bool {
    q_le(q_zero(), x)
}

/// x > 0 at the spec level.
pub open spec fn q_pos(x: Rational) -> bool {
    q_lt(q_zero(), x)
}

/// 0 ≤ 0 in the OrderedRing order (used by static-body constructors).
pub proof fn lemma_zero_nonneg()
    ensures q_nonneg(Rational::from_int_spec(0))
{
    let zero = q_zero();
    Rational::axiom_eqv_reflexive(zero);
    Rational::axiom_le_total(zero, Rational::from_int_spec(0));
}

} // verus!
