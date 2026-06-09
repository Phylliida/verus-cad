// Minimal reproducer for the --lean-backend panic on indexing a Vec<CopyDatatype>.
//
//   verus --lean-backend BUG-vec-copy-datatype-index-lean-panic.repro.rs
//
// Panics:
//   tuple_field_accessor: arity 1 < 2 — 0-tuple (unit) and 1-tuple shouldn't
//   reach field accessor synthesis. n=0.  (lean_verify/src/expr_shared.rs:831)
//
// Change `Vec<Foo>` to `Vec<usize>` (and `r.a` to `r`) and it verifies — the
// trigger is a user-defined #[derive(Copy)] datatype as the Vec element type.
use vstd::prelude::*;
verus! {
#[derive(Clone, Copy)]
pub struct Foo { pub a: usize }

pub fn f(w: &Vec<Foo>) -> usize
    requires w@.len() > 0,
{
    let r = w[0];
    r.a
}
fn main() {}
}
