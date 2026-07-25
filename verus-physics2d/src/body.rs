//! Rigid body state (SPEC §1). inv_mass/inv_inertia form: statics are 0 —
//! no division by mass anywhere in the engine.

use vstd::prelude::*;

use verus_rational::{Rational, RuntimeRational};

use crate::rotq::RotQ;
use crate::types::{q_nonneg, SVec2, Scalar};

verus! {

pub struct Body {
    pub pos: SVec2,
    pub rot: RotQ,
    pub vel: SVec2,
    pub omega: Scalar,
    pub inv_mass: Scalar,
    pub inv_inertia: Scalar,
}

impl Body {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.pos.wf_spec()
        &&& self.rot.wf_spec()
        &&& self.vel.wf_spec()
        &&& self.omega.wf_spec()
        &&& self.inv_mass.wf_spec()
        &&& self.inv_inertia.wf_spec()
        &&& q_nonneg(self.inv_mass@)
        &&& q_nonneg(self.inv_inertia@)
    }

    /// A body is static iff its inverse mass is (exactly, structurally)
    /// the canonical zero — constructors only ever store from_int(0).
    pub open spec fn is_static_spec(&self) -> bool {
        self.inv_mass@ == Rational::from_int_spec(0)
    }

    /// Dynamic body from explicit inverse mass/inertia.
    pub fn new_dynamic(
        pos: SVec2, rot: RotQ, vel: SVec2, omega: Scalar,
        inv_mass: Scalar, inv_inertia: Scalar,
    ) -> (out: Self)
        requires
            pos.wf_spec(), rot.wf_spec(), vel.wf_spec(), omega.wf_spec(),
            inv_mass.wf_spec(), inv_inertia.wf_spec(),
            q_nonneg(inv_mass@), q_nonneg(inv_inertia@),
        ensures
            out.wf_spec(),
            out.pos == pos, out.rot == rot, out.vel == vel,
            out.omega == omega, out.inv_mass == inv_mass,
            out.inv_inertia == inv_inertia,
    {
        Body { pos, rot, vel, omega, inv_mass, inv_inertia }
    }

    /// Static body: zero inverse mass/inertia, zero velocity.
    pub fn new_static(pos: SVec2, rot: RotQ) -> (out: Self)
        requires pos.wf_spec(), rot.wf_spec(),
        ensures out.wf_spec(), out.is_static_spec(),
    {
        let vel = pos.zero();
        let omega = RuntimeRational::from_int(0);
        let inv_mass = RuntimeRational::from_int(0);
        let inv_inertia = RuntimeRational::from_int(0);
        proof {
            crate::types::lemma_zero_nonneg();
            assert(inv_mass@ == Rational::from_int_spec(0));
        }
        Body { pos, rot, vel, omega, inv_mass, inv_inertia }
    }
}

} // verus!
