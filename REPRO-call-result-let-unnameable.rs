// Minimal repro: a call result `x` is a goal-position `let`, unnameable in the
// assert's by-block. `verus --lean-backend REPRO-call-result-let-unnameable.rs`
use verus_builtin::*;
use verus_builtin_macros::*;
verus! {
import Mathlib.Tactic.Linarith

struct S { a: u64 }
spec fn sview(s: S) -> nat { s.a as nat }

#[verifier::tactus_auto]
fn mk() -> (r: S)
    ensures sview(r) == 0
{ S { a: 0 } }

#[verifier::tactus_auto]
fn use_it() {
    let x = mk();                       // x : S, ensures sview(x) == 0
    assert(sview(x) == 0) by {
        have h : sview x = 0 := by assumption    // FAILS: Unknown identifier `x`
        exact h
    };
}
fn main() {}
} // verus!
