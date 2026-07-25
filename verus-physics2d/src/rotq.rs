//! RotQ: orientation as an exact rational point on the unit circle (D2/E2).
//!
//! No angles are stored anywhere — an orientation IS a pair (c, s) with
//! c² + s² ≡ 1 (Rational eqv). Phase phys-01 provides the struct, the
//! invariant, and the identity constructor; phys-02 adds apply / compose /
//! inverse / from_tan_half and the arctan angle ledger.

use vstd::prelude::*;

use verus_algebra::traits::*;
use verus_rational::{Rational, RuntimeRational};

use crate::types::{q_add, q_eqv, q_mul, q_one, q_zero, Scalar};

verus! {

/// c² + s² ≡ 1, stated with the Ring trait ops so it composes directly
/// with RuntimeRational exec ensures (which produce trait-op models).
pub open spec fn unit_norm(c: Rational, s: Rational) -> bool {
    q_eqv(q_add(q_mul(c, c), q_mul(s, s)), q_one())
}

pub struct RotQ {
    pub c: Scalar,
    pub s: Scalar,
}

impl RotQ {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.c.wf_spec()
        &&& self.s.wf_spec()
        &&& unit_norm(self.c@, self.s@)
    }

    /// The identity rotation: (c, s) = (1, 0).
    pub fn identity() -> (out: Self)
        ensures
            out.wf_spec(),
            out.c@ == Rational::from_int_spec(1),
            out.s@ == Rational::from_int_spec(0),
    {
        let c = RuntimeRational::from_int(1);
        let s = RuntimeRational::from_int(0);
        proof {
            lemma_unit_norm_one_zero();
            // from_int_spec(1) is Ring::one, from_int_spec(0) is zero
            assert(c@ == q_one());
            assert(s@ == q_zero());
        }
        RotQ { c, s }
    }
}

/// 1·1 + 0·0 ≡ 1, by the ring axioms (no unfolding of Rational internals).
pub proof fn lemma_unit_norm_one_zero()
    ensures unit_norm(q_one(), q_zero())
{
    let one = q_one();
    let zero = q_zero();
    let a = q_mul(one, one);   // ≡ one
    let b = q_mul(zero, zero); // ≡ zero

    Rational::axiom_mul_one_right(one);       // a ≡ one
    Rational::axiom_mul_zero_right(zero);     // b ≡ zero

    // a + b ≡ one + b
    Rational::axiom_add_congruence_left(a, one, b);
    // one + b ≡ b + one ≡ zero + one ≡ one + zero ≡ one
    Rational::axiom_add_commutative(one, b);
    Rational::axiom_add_congruence_left(b, zero, one);
    Rational::axiom_add_commutative(zero, one);
    Rational::axiom_add_zero_right(one);

    // chain: a+b ≡ one+b ≡ b+one ≡ zero+one ≡ one+zero ≡ one
    Rational::axiom_eqv_transitive(q_add(a, b), q_add(one, b), q_add(b, one));
    Rational::axiom_eqv_transitive(q_add(a, b), q_add(b, one), q_add(zero, one));
    Rational::axiom_eqv_transitive(q_add(a, b), q_add(zero, one), q_add(one, zero));
    Rational::axiom_eqv_transitive(q_add(a, b), q_add(one, zero), one);
}

} // verus!
