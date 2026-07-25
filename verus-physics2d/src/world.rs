//! World: the full simulation state (SPEC §1). Stepping (phys-03) is a
//! PURE function World -> StepResult; nothing here mutates during a step
//! except through the constructors below.

use vstd::prelude::*;

use verus_algebra::traits::*;

use crate::body::Body;
use crate::types::{q_pos, SVec2, Scalar};

verus! {

pub struct World {
    pub bodies: Vec<Body>,
    pub gravity: SVec2,
    pub dt: Scalar,
}

impl World {
    pub open spec fn wf_spec(&self) -> bool {
        &&& forall|i: int|
                0 <= i < self.bodies@.len() ==> (#[trigger] self.bodies@[i]).wf_spec()
        &&& self.gravity.wf_spec()
        &&& self.dt.wf_spec()
        &&& q_pos(self.dt@)
    }

    pub fn new(gravity: SVec2, dt: Scalar) -> (out: Self)
        requires gravity.wf_spec(), dt.wf_spec(), q_pos(dt@),
        ensures out.wf_spec(), out.bodies@.len() == 0,
    {
        World { bodies: Vec::new(), gravity, dt }
    }

    /// Canonical body identity = index in `bodies` (E6: canonical order).
    pub fn add_body(&mut self, b: Body) -> (id: usize)
        requires old(self).wf_spec(), b.wf_spec(),
        ensures
            self.wf_spec(),
            id == old(self).bodies@.len(),
            self.bodies@.len() == old(self).bodies@.len() + 1,
            self.bodies@[id as int] == b,
            forall|i: int|
                0 <= i < old(self).bodies@.len()
                    ==> self.bodies@[i] == old(self).bodies@[i],
            self.gravity == old(self).gravity,
            self.dt == old(self).dt,
    {
        let id = self.bodies.len();
        self.bodies.push(b);
        id
    }
}

} // verus!
