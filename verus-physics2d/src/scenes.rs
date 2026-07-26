//! Acceptance scenes (SPEC §8), as verified exec functions: each scene's
//! claim is proven statically, so `ensures out == true` is the green flag.
//!
//! S1 (phys-03): two bodies, zero gravity, initial velocities; 1000 steps;
//!   total linear and angular momentum EXACTLY (eqv) equal to initial.
//! S2 (phys-02): one body spinning at ω = 3, dt = 1/240, 240 steps;
//!   accumulated angle-enclosure width ≤ 240 · (2/(2k+3)) with k = 8.

use vstd::prelude::*;

use verus_algebra::traits::*;
use verus_linalg::runtime::vec2::RuntimeVec2;
use verus_linalg::vec2::Vec2;
use verus_rational::{Rational, RuntimeRational};

use crate::angle_ledger::{arctan_term, t_in_unit_interval, two_x};
use crate::body::Body;
use crate::momentum::{ang_mom, ang_mom_exec, lin_mom_x, lin_mom_y, lin_mom_exec};
use crate::proofs::angle_ledger::{
    lemma_arctan_term_bound, lemma_arctan_term_nonneg, lemma_two_mul_monotone,
};
use crate::proofs::momentum::{grav_zero, lemma_step_preserves_momentum};
use crate::rotq::RotQ;
use crate::step::{
    body_step_rel, half_angle_model, ledger_increment, lemma_series_unit_interval,
    step_free_flight, tan_half_series_model,
};
use crate::types::{q_nonneg, SVec2, Scalar};
use crate::world::World;

verus! {

/// 0 ≤ x for a closed nonneg from_int/from_frac value (helper).
proof fn lemma_closed_nonneg_one()
    ensures
        q_nonneg(Rational::from_int_spec(1)),
{
    let z = Rational::from_int_spec(0);
    let one = Rational::from_int_spec(1);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(one.num == 1);
    assert(one.denom() == 1);
    assert(z.le_spec(one));
    assert(q_nonneg(one));
}

proof fn lemma_closed_nonneg_half()
    ensures
        q_nonneg(Rational::from_frac_spec(1, 2)),
{
    let z = Rational::from_int_spec(0);
    let h = Rational::from_frac_spec(1, 2);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(h.num == 1);
    assert(h.denom() == 2);
    assert(z.le_spec(h));
    assert(q_nonneg(h));
}

/// h = 0·dt/2 ≡ 0 — so any body's zero-spin tan-half is in [0,1].
proof fn lemma_half_angle_zero(dt: Rational)
    ensures
        half_angle_model(Rational::from_int_spec(0), dt).eqv_spec(
            Rational::from_int_spec(0)),
{
    let z = Rational::from_int_spec(0);
    let h = half_angle_model(z, dt);
    Rational::lemma_mul_zero(dt);
    let num0 = z.mul_spec(dt);
    assert(Rational::from_int_spec(2).num == 2);
    let recip = Rational::from_int_spec(2).reciprocal_spec();
    assert(h == num0.mul_spec(recip));
    Rational::lemma_eqv_reflexive(recip);
    Rational::lemma_eqv_mul_congruence(num0, z, recip, recip);
    Rational::lemma_mul_zero(recip);
    Rational::lemma_eqv_transitive(h, z.mul_spec(recip), z);
}

/// S1: zero-gravity momentum conservation over 1000 steps.
pub fn scene_s1() -> (out: bool)
    ensures
        out == true,
{
    let zero = RuntimeRational::from_int(0);
    let zero2 = RuntimeRational::from_int(0);
    let gravity = RuntimeVec2::new(zero, zero2);
    let dt = RuntimeRational::from_frac(1, 240);
    proof {
        // dt > 0
        assert(Rational::from_int_spec(0).lt_spec(Rational::from_frac_spec(1, 240)));
    }
    let mut w = World::new(gravity, dt, 8);

    // body 1: pos (0,0), vel (1, 2), ω = 0, m = 1, I = 1
    let b1 = Body::new_dynamic(
        RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0)),
        RotQ::identity(),
        RuntimeVec2::new(RuntimeRational::from_int(1), RuntimeRational::from_int(2)),
        RuntimeRational::from_int(0),
        RuntimeRational::from_int(1),
        RuntimeRational::from_int(1),
    );
    // body 2: pos (3,−1), vel (−1, 1/2), ω = 0, m = 2, I = 1
    let b2 = Body::new_dynamic(
        RuntimeVec2::new(RuntimeRational::from_int(3), RuntimeRational::from_int(-1)),
        RotQ::identity(),
        RuntimeVec2::new(RuntimeRational::from_int(-1), RuntimeRational::from_frac(1, 2)),
        RuntimeRational::from_int(0),
        RuntimeRational::from_frac(1, 2),
        RuntimeRational::from_int(1),
    );
    proof {
        lemma_closed_nonneg_one();
        lemma_closed_nonneg_half();
    }
    w.add_body(b1);
    w.add_body(b2);

    let p0 = lin_mom_exec(&w);
    let l0 = ang_mom_exec(&w);
    let ghost init_bodies = w.bodies@;
    proof {
        assert(w.gravity.model@.x == Rational::from_int_spec(0));
        assert(w.gravity.model@.y == Rational::from_int_spec(0));
        assert(w.dt@ == Rational::from_frac_spec(1, 240));
    }

    let mut i: usize = 0;
    while i < 1000
        invariant
            w.wf_spec(),
            w.bodies@.len() == 2 as int,
            w.gravity.model@.x == Rational::from_int_spec(0),
            w.gravity.model@.y == Rational::from_int_spec(0),
            w.dt@ == Rational::from_frac_spec(1, 240),
            forall|j: int|
                0 <= j < 2 ==> (#[trigger] w.bodies@[j]).omega@ == Rational::from_int_spec(0),
            lin_mom_x(w.bodies@, 2 as nat).eqv_spec(lin_mom_x(init_bodies, 2 as nat)),
            lin_mom_y(w.bodies@, 2 as nat).eqv_spec(lin_mom_y(init_bodies, 2 as nat)),
            ang_mom(w.bodies@, 2 as nat).eqv_spec(ang_mom(init_bodies, 2 as nat)),
        decreases 1000 - i,
    {
        proof {
            assert forall|j: int|
                0 <= j < w.bodies@.len() implies t_in_unit_interval(
                    tan_half_series_model(half_angle_model(
                        #[trigger] w.bodies@[j].omega@, w.dt@)))
            by {
                lemma_half_angle_zero(w.dt@);
                let z = Rational::from_int_spec(0);
                let h = half_angle_model(w.bodies@[j].omega@, w.dt@);
                Rational::lemma_eqv_symmetric(h, z);
                Rational::lemma_eqv_implies_le(z, h);
                Rational::lemma_eqv_implies_le(h, z);
                assert(Rational::from_int_spec(0).le_spec(Rational::from_frac_spec(1, 2)));
                Rational::lemma_le_transitive(
                    h, z, Rational::from_frac_spec(1, 2));
                lemma_series_unit_interval(h);
            }
        }
        let r = step_free_flight(&w);
        proof {
            assert(r is Some);
        }
        let (w2, ts) = match r {
            Some(v) => v,
            None => {
                proof {
                    assert(false);
                }
                return false;
            },
        };
        proof {
            lemma_step_preserves_momentum(w, w2, ts@);
            Rational::lemma_eqv_transitive(
                lin_mom_x(w2.bodies@, 2 as nat),
                lin_mom_x(w.bodies@, 2 as nat),
                lin_mom_x(init_bodies, 2 as nat));
            Rational::lemma_eqv_transitive(
                lin_mom_y(w2.bodies@, 2 as nat),
                lin_mom_y(w.bodies@, 2 as nat),
                lin_mom_y(init_bodies, 2 as nat));
            Rational::lemma_eqv_transitive(
                ang_mom(w2.bodies@, 2 as nat),
                ang_mom(w.bodies@, 2 as nat),
                ang_mom(init_bodies, 2 as nat));
            assert forall|j: int|
                0 <= j < 2 implies (#[trigger] w2.bodies@[j]).omega@ == Rational::from_int_spec(0)
            by {
                let tj = ts@[j];
            }
        }
        w = w2;
        i = i + 1;
    }

    let p1 = lin_mom_exec(&w);
    let l1 = ang_mom_exec(&w);
    let ok = p1.x.eq(&p0.x) && p1.y.eq(&p0.y) && l1.eq(&l0);
    proof {
        assert(p1.x@ == lin_mom_x(w.bodies@, 2 as nat));
        assert(p0.x@ == lin_mom_x(init_bodies, 2 as nat));
        assert(ok == true);
    }
    ok
}

/// S2: ω = 3 spin, 240 steps, ledger width ≤ 240 · 2/19 (k = 8).
pub fn scene_s2() -> (out: bool)
    ensures
        out == true,
{
    let zero = RuntimeRational::from_int(0);
    let zero2 = RuntimeRational::from_int(0);
    let gravity = RuntimeVec2::new(zero, zero2);
    let dt = RuntimeRational::from_frac(1, 240);
    proof {
        assert(Rational::from_int_spec(0).lt_spec(Rational::from_frac_spec(1, 240)));
    }
    let mut w = World::new(gravity, dt, 8);

    // one spinning body: pos (0,0), vel (0,0), ω = 3, m = 1, I = 1
    let b = Body::new_dynamic(
        RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0)),
        RotQ::identity(),
        RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(0)),
        RuntimeRational::from_int(3),
        RuntimeRational::from_int(1),
        RuntimeRational::from_int(1),
    );
    proof {
        lemma_closed_nonneg_one();
    }
    w.add_body(b);
    proof {
        assert(w.dt@ == Rational::from_frac_spec(1, 240));
        assert(w.series_k == 8);
        assert(w.bodies@[0].omega@ == Rational::from_int_spec(3));
    }

    let mut i: usize = 0;
    while i < 240
        invariant
            i <= 240,
            w.wf_spec(),
            w.bodies@.len() == 1 as int,
            w.dt@ == Rational::from_frac_spec(1, 240),
            w.series_k == 8,
            w.bodies@[0].omega@ == Rational::from_int_spec(3),
            w.angle_err@[0]@.le_spec(
                Rational::from_int_spec(i as int).mul_spec(Rational::from_frac_spec(2, 19))),
        decreases 240 - i,
    {
        proof {
            // h = 3·(1/240)/2 = 3/480 ∈ [0, 1/2]
            let h = half_angle_model(Rational::from_int_spec(3), Rational::from_frac_spec(1, 240));
            let f = Rational::from_int_spec(3).mul_spec(Rational::from_frac_spec(1, 240));
            Rational::lemma_mul_denom_product_int(
                Rational::from_int_spec(3), Rational::from_frac_spec(1, 240));
            assert(f.num == 3);
            assert(f.denom() == 240);
            assert(Rational::from_int_spec(2).num == 2);
            assert(Rational::from_int_spec(2).reciprocal_spec().num == 1);
            assert(Rational::from_int_spec(2).reciprocal_spec().denom() == 2);
            Rational::lemma_mul_denom_product_int(
                f, Rational::from_int_spec(2).reciprocal_spec());
            assert(h.num == 3);
            assert(h.denom() == 480);
            let z = Rational::from_int_spec(0);
            assert(z.num == 0);
            assert(z.denom() == 1);
            assert(z.le_spec(h));
            assert(h.le_spec(Rational::from_frac_spec(1, 2)));
            lemma_series_unit_interval(h);
            assert(w.bodies@[0].omega@ == Rational::from_int_spec(3));
            assert(t_in_unit_interval(
                tan_half_series_model(half_angle_model(w.bodies@[0].omega@, w.dt@))));
            assert forall|j: int|
                0 <= j < w.bodies@.len() implies t_in_unit_interval(
                    tan_half_series_model(half_angle_model(
                        #[trigger] w.bodies@[j].omega@, w.dt@)))
            by {
            }
        }
        let r = step_free_flight(&w);
        proof {
            assert(r is Some);
        }
        let (w2, ts) = match r {
            Some(v) => v,
            None => {
                proof {
                    assert(false);
                }
                return false;
            },
        };
        proof {
            let ghost t0 = ts@[0]@;
            let ghost inc = ledger_increment(t0, 8 as nat);
            let ghost cap = Rational::from_frac_spec(2, 19);
            // inc = 2·|term_9(t0)| ≤ 2·(1/19) == cap
            lemma_arctan_term_nonneg(t0, 9);
            lemma_arctan_term_bound(t0, 9);
            assert(Rational::from_int_spec(0).num == 0);
            assert(Rational::from_int_spec(0).denom() == 1);
            assert(Rational::from_int_spec(0).le_spec(arctan_term(t0, 9))
                == (Rational::from_int_spec(0).num * arctan_term(t0, 9).denom()
                    <= arctan_term(t0, 9).num * Rational::from_int_spec(0).denom()));
            assert(arctan_term(t0, 9).num >= 0);
            assert(arctan_term(t0, 9).abs_spec() == arctan_term(t0, 9));
            lemma_two_mul_monotone(
                arctan_term(t0, 9), Rational::from_frac_spec(1, 19));
            assert(two_x(Rational::from_frac_spec(1, 19)) == Rational::from_frac_spec(2, 19));
            assert(inc.le_spec(cap));
            // err' ≡ err + inc ≤ err + cap ≤ i·cap + cap ≡ (i+1)·cap
            Rational::lemma_le_add_both(
                w.angle_err@[0]@,
                Rational::from_int_spec(i as int).mul_spec(cap),
                inc,
                cap);
            Rational::lemma_eqv_implies_le(
                w2.angle_err@[0]@,
                w.angle_err@[0]@.add_spec(inc));
            Rational::lemma_le_transitive(
                w2.angle_err@[0]@,
                w.angle_err@[0]@.add_spec(inc),
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap));
            // (i+1)·cap ≡ i·cap + cap
            Rational::lemma_from_int_add(i as int, 1);
            Rational::lemma_mul_commutative(
                Rational::from_int_spec((i + 1) as int), cap);
            Rational::lemma_mul_distributes_over_add(
                cap, Rational::from_int_spec(i as int), Rational::from_int_spec(1));
            Rational::lemma_mul_one_identity(cap);
            Rational::lemma_mul_commutative(cap, Rational::from_int_spec(i as int));
            assert(Rational::from_int_spec((i + 1) as int).mul_spec(cap).eqv_spec(
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap)));
            Rational::lemma_eqv_symmetric(
                Rational::from_int_spec((i + 1) as int).mul_spec(cap),
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap));
            Rational::lemma_eqv_implies_le(
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap),
                Rational::from_int_spec((i + 1) as int).mul_spec(cap));
            Rational::lemma_le_transitive(
                w2.angle_err@[0]@,
                Rational::from_int_spec(i as int).mul_spec(cap).add_spec(cap),
                Rational::from_int_spec((i + 1) as int).mul_spec(cap));
        }
        w = w2;
        i = i + 1;
    }

    // final: angle_err[0] ≤ 240·(2/19)
    let cap_total = RuntimeRational::from_int(240).mul(&RuntimeRational::from_frac(2, 19));
    let ok = w.angle_err[0].le(&cap_total);
    proof {
        assert(w.angle_err@[0]@.le_spec(
            Rational::from_int_spec(240).mul_spec(Rational::from_frac_spec(2, 19))));
        assert(ok == true);
    }
    ok
}

} // verus!
