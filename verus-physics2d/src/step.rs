//! Free-flight symplectic Euler step (phys-03; SPEC §6 pipeline steps 1+4).
//!
//! Pure: World -> Option<(World, Vec<Scalar>)>, None = reject (tan-half
//! parameter outside [0,1]; driver policy is to halve dt, SPEC §1/§3).
//! Rotation integrates through the untrusted tan_half_series chooser; the
//! per-body ledger accumulates 2·|term_{k+1}(t)| (E2 angle ledger, phys-02b).

use vstd::prelude::*;

use verus_algebra::traits::*;
use verus_linalg::vec2::Vec2;
use verus_linalg::vec2::ops::scale;
use verus_rational::{Rational, RuntimeRational};

use crate::angle_ledger::{arctan_term, arctan_term_exec, t_in_unit_interval, two_x};
use crate::body::Body;
use crate::proofs::rational_raw::{
    compose_c, compose_s, lemma_raw_add_nonneg, lemma_raw_add_zero_right, lemma_raw_abs_nonneg,
    lemma_raw_two_nonneg,
};
use crate::proofs::rpow::{ipow, lemma_ipow_congruence, lemma_ipow_zero_base};
use crate::rotq::RotQ;
use crate::types::{copy_svec2, q_nonneg, q_pos, SVec2, Scalar};
use crate::world::World;

verus! {

/// A body is dynamic iff its inverse mass numerator is nonzero.
pub open spec fn body_dynamic(b: Body) -> bool {
    b.inv_mass@.num != 0
}

/// tan-half-angle coordinates (spec forms matching RotQ::from_tan_half).
pub open spec fn tan_half_c(t: Rational) -> Rational {
    Rational::from_int_spec(1).sub_spec(t.mul_spec(t)).div_spec(
        Rational::from_int_spec(1).add_spec(t.mul_spec(t)))
}

pub open spec fn tan_half_s(t: Rational) -> Rational {
    Rational::from_int_spec(2).mul_spec(t).div_spec(
        Rational::from_int_spec(1).add_spec(t.mul_spec(t)))
}

/// The untrusted series chooser model (matches RotQ::tan_half_series).
pub open spec fn tan_half_series_model(h: Rational) -> Rational {
    h.add_spec(
        h.mul_spec(h).mul_spec(h).mul_spec(Rational::from_frac_spec(1, 3)),
    ).add_spec(
        Rational::from_int_spec(2).mul_spec(
            h.mul_spec(h).mul_spec(h).mul_spec(h).mul_spec(h),
        ).mul_spec(Rational::from_frac_spec(1, 15)),
    )
}

/// h = ω·dt/2 (matches the exec computation order).
pub open spec fn half_angle_model(omega: Rational, dt: Rational) -> Rational {
    omega.mul_spec(dt).div_spec(Rational::from_int_spec(2))
}

/// Relational spec of one body's free-flight step (symplectic Euler +
/// tan-half rotation). The exec step ensures this for every body.
pub open spec fn body_step_rel(
    pre: Body,
    post: Body,
    g: Vec2<Rational>,
    dt: Rational,
    t: Rational,
) -> bool {
    if body_dynamic(pre) {
        let vel1 = pre.vel.model@.add(scale(dt, g));
        &&& t == tan_half_series_model(half_angle_model(pre.omega@, dt))
        &&& post.vel.model@ == vel1
        &&& post.pos.model@ == pre.pos.model@.add(scale(dt, vel1))
        &&& post.omega@ == pre.omega@
        &&& post.rot.c@ == compose_c(pre.rot.c@, pre.rot.s@, tan_half_c(t), tan_half_s(t))
        &&& post.rot.s@ == compose_s(pre.rot.c@, pre.rot.s@, tan_half_c(t), tan_half_s(t))
        &&& post.inv_mass@ == pre.inv_mass@
        &&& post.inv_inertia@ == pre.inv_inertia@
    } else {
        &&& post.pos.model@ == pre.pos.model@
        &&& post.vel.model@ == pre.vel.model@
        &&& post.rot.c@ == pre.rot.c@
        &&& post.rot.s@ == pre.rot.s@
        &&& post.omega@ == pre.omega@
        &&& post.inv_mass@ == pre.inv_mass@
        &&& post.inv_inertia@ == pre.inv_inertia@
    }
}

/// The per-body per-step ledger increment: 2·|term_{k+1}(t)|.
pub open spec fn ledger_increment(t: Rational, series_k: nat) -> Rational {
    two_x(arctan_term(t, series_k + 1).abs_spec())
}

/// |term_j| ≥ 0 (abs of anything is nonneg — re-export shape for callers).
pub proof fn lemma_ledger_increment_nonneg(t: Rational, series_k: nat)
    ensures
        Rational::from_int_spec(0).le_spec(ledger_increment(t, series_k)),
{
    lemma_raw_abs_nonneg(arctan_term(t, series_k + 1));
    lemma_raw_two_nonneg(arctan_term(t, series_k + 1).abs_spec());
}

/// 0 ≤ h ≤ 1/2 ⇒ the untrusted series stays in [0, 1] (so the step
/// never rejects for such h). Bounds: t ≤ h + h/12 + h/120 < 1.
pub proof fn lemma_series_unit_interval(h: Rational)
    requires
        Rational::from_int_spec(0).le_spec(h),
        h.le_spec(Rational::from_frac_spec(1, 2)),
    ensures
        t_in_unit_interval(tan_half_series_model(h)),
{
    let z = Rational::from_int_spec(0);
    let half = Rational::from_frac_spec(1, 2);
    let t = tan_half_series_model(h);
    // pieces
    let h2 = h.mul_spec(h);
    let h3 = h2.mul_spec(h);
    let h4 = h3.mul_spec(h);
    let h5 = h4.mul_spec(h);
    let third = Rational::from_frac_spec(1, 3);
    let t1 = h3.mul_spec(third);
    let h5x2 = Rational::from_int_spec(2).mul_spec(h5);
    let t2 = h5x2.mul_spec(Rational::from_frac_spec(1, 15));
    let s1 = h.add_spec(t1);
    // nonnegatives
    Rational::lemma_eqv_implies_le(z, z);
    Rational::lemma_le_mul_nonneg_both(z, h, z, h);
    Rational::lemma_mul_zero(z);
    Rational::lemma_eqv_implies_le(z.mul_spec(z), z);
    Rational::lemma_le_transitive(z, z.mul_spec(z), z.mul_spec(h));
    assert(z.le_spec(h2));
    Rational::lemma_le_mul_nonneg_both(z, h2, z, h);
    Rational::lemma_le_transitive(z, z.mul_spec(z), h2.mul_spec(h));
    assert(z.le_spec(h3));
    Rational::lemma_le_mul_nonneg_both(z, h3, z, h);
    Rational::lemma_le_transitive(z, z.mul_spec(z), h3.mul_spec(h));
    assert(z.le_spec(h4));
    Rational::lemma_le_mul_nonneg_both(z, h4, z, h);
    Rational::lemma_le_transitive(z, z.mul_spec(z), h4.mul_spec(h));
    assert(z.le_spec(h5));
    assert(z.le_spec(third));
    Rational::lemma_le_mul_nonneg_both(z, h3, z, third);
    Rational::lemma_le_transitive(z, z.mul_spec(z), t1);
    assert(z.le_spec(t1));
    assert(z.le_spec(Rational::from_int_spec(2)));
    Rational::lemma_le_mul_nonneg_both(z, Rational::from_int_spec(2), z, h5);
    Rational::lemma_le_transitive(z, z.mul_spec(z), h5x2);
    assert(z.le_spec(h5x2));
    assert(z.le_spec(Rational::from_frac_spec(1, 15)));
    Rational::lemma_le_mul_nonneg_both(z, h5x2, z, Rational::from_frac_spec(1, 15));
    Rational::lemma_le_transitive(z, z.mul_spec(z), t2);
    assert(z.le_spec(t2));
    Rational::lemma_le_add_both(z, h, z, t1);
    assert(z.add_spec(z) == z);
    Rational::lemma_le_transitive(z, z.add_spec(z), s1);
    Rational::lemma_le_add_both(z, s1, z, t2);
    Rational::lemma_le_transitive(z, z.add_spec(z), t);
    assert(z.le_spec(t));
    // upper bounds: h ≤ 1/2 ⇒ h^p ≤ (1/2)^p
    Rational::lemma_le_mul_nonneg_both(h, half, h, half);
    assert(half.mul_spec(half) == Rational::from_frac_spec(1, 4));
    Rational::lemma_le_mul_nonneg_both(h2, Rational::from_frac_spec(1, 4), h, half);
    assert(Rational::from_frac_spec(1, 4).mul_spec(half) == Rational::from_frac_spec(1, 8));
    Rational::lemma_le_mul_nonneg_both(h3, Rational::from_frac_spec(1, 8), h, half);
    assert(Rational::from_frac_spec(1, 8).mul_spec(half) == Rational::from_frac_spec(1, 16));
    Rational::lemma_le_mul_nonneg_both(h4, Rational::from_frac_spec(1, 16), h, half);
    assert(Rational::from_frac_spec(1, 16).mul_spec(half) == Rational::from_frac_spec(1, 32));
    // t1 ≤ 1/8 · 1/3 = 1/24 ; 2h⁵ ≤ 2/32 = 1/16 ; t2 ≤ 1/16 · 1/15 = 1/240
    Rational::lemma_eqv_implies_le(third, third);
    Rational::lemma_le_mul_nonneg_both(h3, Rational::from_frac_spec(1, 8), third, third);
    assert(Rational::from_frac_spec(1, 8).mul_spec(third) == Rational::from_frac_spec(1, 24));
    assert(t1.le_spec(Rational::from_frac_spec(1, 24)));
    Rational::lemma_eqv_implies_le(Rational::from_int_spec(2), Rational::from_int_spec(2));
    Rational::lemma_le_mul_nonneg_both(
        Rational::from_int_spec(2), Rational::from_int_spec(2),
        h5, Rational::from_frac_spec(1, 32));
    assert(Rational::from_int_spec(2).mul_spec(Rational::from_frac_spec(1, 32))
        .eqv_spec(Rational::from_frac_spec(1, 16)));
    Rational::lemma_eqv_implies_le(
        Rational::from_int_spec(2).mul_spec(Rational::from_frac_spec(1, 32)),
        Rational::from_frac_spec(1, 16));
    Rational::lemma_le_transitive(
        h5x2,
        Rational::from_int_spec(2).mul_spec(Rational::from_frac_spec(1, 32)),
        Rational::from_frac_spec(1, 16));
    assert(h5x2.le_spec(Rational::from_frac_spec(1, 16)));
    Rational::lemma_eqv_implies_le(Rational::from_frac_spec(1, 15), Rational::from_frac_spec(1, 15));
    Rational::lemma_le_mul_nonneg_both(
        h5x2, Rational::from_frac_spec(1, 16),
        Rational::from_frac_spec(1, 15), Rational::from_frac_spec(1, 15));
    assert(Rational::from_frac_spec(1, 16).mul_spec(Rational::from_frac_spec(1, 15))
        == Rational::from_frac_spec(1, 240));
    assert(t2.le_spec(Rational::from_frac_spec(1, 240)));
    // s1 ≤ 1/2 + 1/24 ≡ 13/24 ; t ≤ 13/24 + 1/240 ≤ 1
    Rational::lemma_le_add_both(h, half, t1, Rational::from_frac_spec(1, 24));
    let s1b = half.add_spec(Rational::from_frac_spec(1, 24));
    let f1324 = Rational::from_frac_spec(13, 24);
    assert(s1b.num == 26);
    assert(s1b.denom() == 48);
    assert(f1324.num == 13);
    assert(f1324.denom() == 24);
    assert(s1b.eqv_spec(f1324));
    Rational::lemma_eqv_implies_le(s1b, f1324);
    Rational::lemma_le_transitive(s1, s1b, f1324);
    Rational::lemma_le_add_both(s1, f1324, t2, Rational::from_frac_spec(1, 240));
    let s2b = f1324.add_spec(Rational::from_frac_spec(1, 240));
    let onei = Rational::from_int_spec(1);
    assert(s2b.num == 3144);
    assert(s2b.denom() == 5760);
    assert(onei.num == 1);
    assert(onei.denom() == 1);
    assert(s2b.le_spec(onei));
    Rational::lemma_le_transitive(t, s2b, onei);
    assert(t.le_spec(Rational::from_int_spec(1)));
}

/// t ≡ 0 ⇒ the ledger increment is ≡ 0.
pub proof fn lemma_ledger_increment_zero(t: Rational, series_k: nat)
    requires
        t.num == 0,
    ensures
        ledger_increment(t, series_k).eqv_spec(Rational::from_int_spec(0)),
{
    let z = Rational::from_int_spec(0);
    crate::proofs::angle_ledger::lemma_arctan_term_zero(t, series_k + 1);
    crate::proofs::angle_ledger::lemma_arctan_term_num_denom(t, series_k + 1);
    lemma_ipow_congruence(t.num, 0, 2 * (series_k + 1) + 1);
    lemma_ipow_zero_base(2 * (series_k + 1) + 1);
    let term = arctan_term(t, series_k + 1);
    assert(term.num == 0);
    assert(term.abs_spec() == term);
    Rational::lemma_eqv_reflexive(Rational::from_int_spec(2));
    Rational::lemma_eqv_mul_congruence(
        Rational::from_int_spec(2), Rational::from_int_spec(2), term, z);
    let tz = two_x(z);
    Rational::lemma_mul_denom_product_int(Rational::from_int_spec(2), z);
    assert(tz.num == 0);
    assert(tz.denom() == 1);
    assert(z.num == 0);
    assert(z.denom() == 1);
    assert(tz.eqv_spec(z));
    Rational::lemma_eqv_transitive(two_x(term), tz, z);
    assert(ledger_increment(t, series_k) == two_x(term.abs_spec()));
}

/// Free-flight step: gravity to velocities, symplectic position update,
/// tan-half rotation compose, ledger accumulation. None = angle reject.
pub fn step_free_flight(w: &World) -> (out: Option<(World, Vec<Scalar>)>)
    requires
        w.wf_spec(),
    ensures
        // the step only rejects when some body's tan-half parameter
        // escapes [0, 1] (SPEC §3 phase-1 restriction)
        (forall|i: int|
            0 <= i < w.bodies@.len() ==> t_in_unit_interval(
                tan_half_series_model(half_angle_model(
                    #[trigger] w.bodies@[i].omega@, w.dt@))))
            ==> out is Some,
        out is Some ==> {
            let r = out->Some_0;
            &&& r.0.wf_spec()
            &&& r.0.bodies@.len() == w.bodies@.len()
            &&& r.1@.len() == w.bodies@.len()
            &&& r.0.gravity.model@ == w.gravity.model@
            &&& r.0.dt@ == w.dt@
            &&& r.0.series_k == w.series_k
            &&& forall|i: int|
                0 <= i < w.bodies@.len() ==> {
                    let ti = #[trigger] r.1@[i];
                    &&& ti.wf_spec()
                    &&& t_in_unit_interval(ti@)
                    &&& body_step_rel(
                        w.bodies@[i], r.0.bodies@[i], w.gravity.model@, w.dt@, ti@)
                    &&& r.0.angle_err@[i]@.eqv_spec(
                        w.angle_err@[i as int]@.add_spec(ledger_increment(ti@, w.series_k as nat)))
                }
        },
{
    let mut new_bodies: Vec<Body> = Vec::new();
    let mut new_errs: Vec<Scalar> = Vec::new();
    let mut ts: Vec<Scalar> = Vec::new();
    let mut i: usize = 0;
    while i < w.bodies.len()
        invariant
            i <= w.bodies@.len(),
            w.wf_spec(),
            new_bodies@.len() == i as int,
            new_errs@.len() == i as int,
            ts@.len() == i as int,
            forall|j: int|
                0 <= j < i as int ==> {
                    let tj = #[trigger] ts@[j];
                    &&& tj.wf_spec()
                    &&& t_in_unit_interval(tj@)
                    &&& new_bodies@[j].wf_spec()
                    &&& body_step_rel(
                        w.bodies@[j], new_bodies@[j], w.gravity.model@, w.dt@, tj@)
                    &&& new_errs@[j].wf_spec()
                    &&& q_nonneg(new_errs@[j]@)
                    &&& new_errs@[j]@.eqv_spec(
                        w.angle_err@[j]@.add_spec(ledger_increment(tj@, w.series_k as nat)))
                },
        decreases w.bodies.len() - i,
    {
        let zero = RuntimeRational::from_int(0);
        let is_static = w.bodies[i].inv_mass.eq(&zero);
        proof {
            // eq ⟺ num == 0 (bridge to body_dynamic)
            assert(w.bodies@[i as int].inv_mass@.eqv_spec(Rational::from_int_spec(0))
                == (w.bodies@[i as int].inv_mass@.num == 0));
            assert(is_static == (w.bodies@[i as int].inv_mass@.num == 0));
        }
        if is_static {
            let b2 = w.bodies[i].copy_body();
            let e2 = verus_rational::runtime_rational::copy_rational(&w.angle_err[i]);
            let t2 = RuntimeRational::from_int(0);
            proof {
                let ghost old_e = w.angle_err@[i as int]@;
                let ghost inc = ledger_increment(t2@, w.series_k as nat);
                let ghost z = Rational::from_int_spec(0);
                assert(t2@ == z);
                assert(t2@.num == 0);
                lemma_ledger_increment_zero(t2@, w.series_k as nat);
                // old + inc ≡ old + 0 ≡ old, so e2@ == old ≡ old + inc
                Rational::lemma_eqv_reflexive(old_e);
                Rational::lemma_eqv_add_congruence(old_e, old_e, inc, z);
                lemma_raw_add_zero_right(old_e);
                Rational::lemma_eqv_symmetric(old_e.add_spec(z), old_e);
                Rational::lemma_eqv_transitive(old_e.add_spec(inc), old_e.add_spec(z), old_e);
                Rational::lemma_eqv_symmetric(old_e.add_spec(inc), old_e);
                // t_in_unit_interval(0)
                assert(z.le_spec(t2@));
                assert(t2@.le_spec(Rational::from_int_spec(1)));
            }
            new_bodies.push(b2);
            new_errs.push(e2);
            ts.push(t2);
        } else {
            let gdt = w.gravity.scaled(&w.dt);
            let vel1 = w.bodies[i].vel.add(&gdt);
            let dp = vel1.scaled(&w.dt);
            let pos1 = w.bodies[i].pos.add(&dp);
            let h = w.bodies[i].omega.mul(&w.dt);
            let two = RuntimeRational::from_int(2);
            proof {
                assert(!two@.eqv_spec(Rational::from_int_spec(0)));
            }
            let half = h.div(&two);
            let t = RotQ::tan_half_series(&half);
            let one = RuntimeRational::from_int(1);
            let t_ok = zero.le(&t) && t.le(&one);
            if !t_ok {
                proof {
                    // reject witness: this body's t is outside [0, 1]
                    assert(!t_in_unit_interval(t@));
                    assert(t@ == tan_half_series_model(half_angle_model(
                        w.bodies@[i as int].omega@, w.dt@)));
                }
                return None;
            }
            let dr = RotQ::from_tan_half(&t);
            let rot1 = w.bodies[i].rot.compose(&dr);
            proof {
                assert(half@ == w.bodies@[i as int].omega@.mul_spec(w.dt@).div_spec(
                    Rational::from_int_spec(2)));
                assert(half@ == half_angle_model(w.bodies@[i as int].omega@, w.dt@));
                assert(t@ == tan_half_series_model(half@));
                assert(t@ == tan_half_series_model(half_angle_model(
                    w.bodies@[i as int].omega@, w.dt@)));
            }
            let omega1 = verus_rational::runtime_rational::copy_rational(&w.bodies[i].omega);
            let im1 = verus_rational::runtime_rational::copy_rational(&w.bodies[i].inv_mass);
            let ii1 = verus_rational::runtime_rational::copy_rational(&w.bodies[i].inv_inertia);
            let b2 = Body {
                pos: pos1,
                rot: rot1,
                vel: vel1,
                omega: omega1,
                inv_mass: im1,
                inv_inertia: ii1,
            };
            // ledger: 2·|term_{k+1}(t)|
            let term = arctan_term_exec(&t, w.series_k + 1);
            let sgn = term.signum();
            let abs_term = if sgn < 0i8 {
                term.neg()
            } else {
                term
            };
            let width = two.mul(&abs_term);
            let e2 = w.angle_err[i].add(&width);
            proof {
                Rational::lemma_signum_negative_iff(term@);
                Rational::lemma_signum_zero_iff(term@);
                Rational::lemma_signum_positive_iff(term@);
                if sgn < 0i8 {
                    assert(term@.signum() == -1);
                    assert(term@.num < 0);
                    assert(term@.abs_spec() == term@.neg_spec());
                } else {
                    assert(term@.signum() == 0 || term@.signum() == 1);
                    assert(term@.num >= 0);
                    assert(term@.abs_spec() == term@);
                }
                assert(abs_term@ == term@.abs_spec());
                assert(width@ == ledger_increment(t@, w.series_k as nat));
                lemma_ledger_increment_nonneg(t@, w.series_k as nat);
                lemma_raw_add_nonneg(w.angle_err@[i as int]@, ledger_increment(t@, w.series_k as nat));
            }
            new_bodies.push(b2);
            new_errs.push(e2);
            ts.push(t);
        }
        i = i + 1;
    }
    let gravity2 = copy_svec2(&w.gravity);
    let dt2 = verus_rational::runtime_rational::copy_rational(&w.dt);
    let w2 = World {
        bodies: new_bodies,
        gravity: gravity2,
        dt: dt2,
        series_k: w.series_k,
        angle_err: new_errs,
    };
    proof {
        assert(q_pos(w2.dt@));
        assert forall|j: int|
            0 <= j < w2.bodies@.len() implies (#[trigger] w2.bodies@[j]).wf_spec()
        by {
            let tj = ts@[j];
            assert(new_bodies@[j].wf_spec());
        }
        assert forall|j: int|
            0 <= j < w2.angle_err@.len() implies {
                let e = #[trigger] w2.angle_err@[j];
                e.wf_spec() && q_nonneg(e@)
            }
        by {
            let tj = ts@[j];
            assert(new_errs@[j].wf_spec());
            assert(q_nonneg(new_errs@[j]@));
        }
        assert(w2.wf_spec());
        assert forall|i: int|
            0 <= i < w.bodies@.len() implies {
                let ti = #[trigger] ts@[i];
                &&& ti.wf_spec()
                &&& t_in_unit_interval(ti@)
                &&& body_step_rel(w.bodies@[i], w2.bodies@[i], w.gravity.model@, w.dt@, ti@)
                &&& w2.angle_err@[i]@.eqv_spec(
                    w.angle_err@[i]@.add_spec(ledger_increment(ti@, w.series_k as nat)))
            }
        by {
            let ti = ts@[i];
            assert(ti.wf_spec());
            assert(t_in_unit_interval(ti@));
            assert(body_step_rel(w.bodies@[i], w2.bodies@[i], w.gravity.model@, w.dt@, ti@));
            assert(w2.angle_err@[i]@.eqv_spec(
                w.angle_err@[i]@.add_spec(ledger_increment(ti@, w.series_k as nat))));
        }
    }
    Some((w2, ts))
}

} // verus!
