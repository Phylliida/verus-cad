use verus_builtin::*;
use verus_builtin_macros::*;
verus! {
spec fn f(x: nat) -> nat decreases x { if x == 0 { 0 } else { f((x - 1) as nat) + 1 } }

#[verifier::tactus_auto]
fn h(m: u64) -> (p: (u64, u64))
    requires f(m as nat) <= 100
    ensures p.0 as nat == f(m as nat), p.1 as nat == f((m + 1) as nat)
{ (m, m + 1) }

#[verifier::tactus_auto]
fn g(n: u64) -> (res: u64)
    requires f((n + 1) as nat) <= 100
    ensures true
{
    let (a, b) = h(n);          // a.toNat = f(n), b.toNat = f(n+1)  (behind lets)
    // b.toNat = f(n+1) <= 100  ==>  b <= 100. Needs bridging b -> ret.2 -> ensures.
    assert(b <= 100) by { intros; omega };   // <-- expect FAIL (omega can't see let-fvar b)
    a
}
fn main() {}
} // verus!
