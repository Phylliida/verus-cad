//! Arctan ledger lemmas (phys-02b). All statements are rational arithmetic
//! only (E3): exact endpoints, width formula, monotone shrink. The semantic
//! bracketing of arctan itself is Lean card G0.
//!
//! Same R-discipline as proofs/rational_raw.rs: exact body-form unfolds,
//! implication-form NLA, verbatim modus-ponens antecedents.

use vstd::prelude::*;

use verus_rational::Rational;

use crate::angle_ledger::{angle_enclosure, arctan_sum, arctan_term, t_in_unit_interval, two_x};
use crate::proofs::rpow::{
    ipow, lemma_ipow_add, lemma_ipow_congruence, lemma_ipow_double, lemma_ipow_le,
    lemma_ipow_nonneg, lemma_ipow_pos, lemma_rpow_num_denom, rpow,
};

verus! {

// ── term structure ───────────────────────────────────────────────────

/// term_j.num == n^(2j+1) and term_j.denom() == dd^(2j+1)·(2j+1).
pub proof fn lemma_arctan_term_num_denom(t: Rational, j: nat)
    ensures
        arctan_term(t, j).num == ipow(t.num, 2 * j + 1),
        arctan_term(t, j).denom() == ipow(t.denom(), 2 * j + 1) * ((2 * j + 1) as int),
{
    let e = 2 * j + 1;
    let m = (2 * j + 1) as int;
    let rp = rpow(t, e);
    let d = Rational::from_int_spec(m);
    let r = d.reciprocal_spec();
    let term = arctan_term(t, j);

    lemma_rpow_num_denom(t, e);
    Rational::lemma_mul_denom_product_int(rp, r);

    // from_int(m): num == m, denom() == 1, and m >= 1 so reciprocal flips
    assert(d.num == m);
    assert(d.denom() == 1);
    assert(d.num > 0);
    // reciprocal_spec positive branch
    assert(r.num == d.denom());
    assert(r.denom() == d.num);
    assert(r.num == 1);
    assert(r.denom() == m);

    // term == rp.div_spec(d) == rp.mul_spec(r)
    assert(term == rp.mul_spec(r));
    assert(term.num == rp.num * r.num);
    assert(term.num == ipow(t.num, e));
    assert(term.denom() == rp.denom() * r.denom());
    assert(term.denom() == ipow(t.denom(), e) * m);
}

/// x^(e+2) == x²·x^e (one-step regroup of lemma_ipow_add).
pub proof fn lemma_ipow_plus_two(x: int, e: nat)
    ensures ipow(x, e + 2) == x * x * ipow(x, e),
{
    lemma_ipow_add(x, e, 2);
    lemma_ipow_double(x, 1);
    assert(ipow(x, 1) == x) by { reveal_with_fuel(ipow, 2); }
    assert(ipow(x, 2) == x * x);
    assert(ipow(x, e + 2) == ipow(x, e) * ipow(x, 2));
    assert(ipow(x, 2) == x * x ==> ipow(x, e) * ipow(x, 2) == x * x * ipow(x, e))
        by (nonlinear_arith);
}

/// 0 ≤ t ⇒ term_j ≥ 0.
pub proof fn lemma_arctan_term_nonneg(t: Rational, j: nat)
    requires
        Rational::from_int_spec(0).le_spec(t),
    ensures
        Rational::from_int_spec(0).le_spec(arctan_term(t, j)),
{
    let zero = Rational::from_int_spec(0);
    lemma_arctan_term_num_denom(t, j);
    // 0 ≤ t ⟺ 0 ≤ t.num
    assert(zero.le_spec(t) == (zero.num * t.denom() <= t.num * zero.denom()));
    assert(zero.num == 0);
    assert(zero.denom() == 1);
    assert(zero.num * t.denom() <= t.num * zero.denom());
    assert((zero.num * t.denom() <= t.num * zero.denom() && zero.num == 0 && zero.denom() == 1)
        ==> t.num >= 0) by (nonlinear_arith);
    assert(t.num >= 0);
    lemma_ipow_nonneg(t.num, 2 * j + 1);
    // 0 ≤ term ⟺ 0 ≤ term.num
    assert(zero.le_spec(arctan_term(t, j)) == (
        zero.num * arctan_term(t, j).denom() <= arctan_term(t, j).num * zero.denom()));
}

/// 0 ≤ t ≤ 1 ⇒ term_{j+1} ≤ term_j (terms shrink for unit-interval t).
pub proof fn lemma_arctan_term_decreasing(t: Rational, j: nat)
    requires
        t_in_unit_interval(t),
    ensures
        arctan_term(t, (j + 1) as nat).le_spec(arctan_term(t, j)),
{
    let zero = Rational::from_int_spec(0);
    let one = Rational::from_int_spec(1);
    let ghost n = t.num;
    let ghost dd = t.denom();
    Rational::lemma_denom_positive(t);

    // 0 ≤ n ≤ dd from the unit-interval hypothesis
    assert(zero.le_spec(t) == (zero.num * t.denom() <= t.num * zero.denom()));
    assert(zero.num == 0);
    assert(zero.denom() == 1);
    assert(t.le_spec(one) == (t.num * one.denom() <= one.num * t.denom()));
    assert(one.num == 1);
    assert(one.denom() == 1);
    assert(zero.num * t.denom() <= t.num * zero.denom());
    assert(t.num * one.denom() <= one.num * t.denom());
    assert((zero.num * t.denom() <= t.num * zero.denom() && zero.num == 0 && zero.denom() == 1)
        ==> t.num >= 0) by (nonlinear_arith);
    vstd::arithmetic::mul::lemma_mul_basics(t.num);
    vstd::arithmetic::mul::lemma_mul_basics(t.denom());
    assert(t.num <= dd);
    assert(0 <= n && n <= dd);

    let e = 2 * j + 1;
    let ghost m = (2 * j + 1) as int;
    lemma_arctan_term_num_denom(t, j);
    lemma_arctan_term_num_denom(t, (j + 1) as nat);
    // (j+1) exponent: 2(j+1)+1 == e + 2
    assert(2 * (j + 1) + 1 == e + 2);
    let ghost nn = ipow(n, e);
    let ghost dp = ipow(dd, e);
    lemma_ipow_plus_two(n, e);
    lemma_ipow_plus_two(dd, e);
    lemma_ipow_nonneg(n, e);
    lemma_ipow_nonneg(dd, e);
    lemma_ipow_le(n, dd, 2);
    lemma_ipow_nonneg(n, 2);
    // P = nn·dp ≥ 0, and n²·m ≤ dd²·(m+2)
    assert((0 <= n && n <= dd) ==> n * n <= dd * dd) by (nonlinear_arith);
    assert((n * n <= dd * dd && m >= 1) ==> n * n * m <= dd * dd * (m + 2)) by (nonlinear_arith);
    assert((nn >= 0 && dp >= 0 && n * n * m <= dd * dd * (m + 2))
        ==> (n * n * nn) * (dp * m) <= (nn * (dd * dd)) * (dp * (m + 2))) by (nonlinear_arith);
    // the cross-multiplied goal
    let tj = arctan_term(t, j);
    let tj1 = arctan_term(t, (j + 1) as nat);
    assert(tj1.num == ipow(n, e + 2));
    assert(tj1.denom() == ipow(dd, e + 2) * (m + 2));
    assert(tj.num == nn);
    assert(tj.denom() == dp * m);
    assert((tj1.num == ipow(n, e + 2) && tj1.denom() == ipow(dd, e + 2) * (m + 2)
        && tj.num == nn && tj.denom() == dp * m
        && ipow(n, e + 2) == n * n * nn && ipow(dd, e + 2) == dd * dd * dp
        && (n * n * nn) * (dp * m) <= (nn * (dd * dd)) * (dp * (m + 2)))
        ==> tj1.num * tj.denom() <= tj.num * tj1.denom()) by (nonlinear_arith);
    assert(tj1.le_spec(tj));
}

// ── sum steps ────────────────────────────────────────────────────────

pub proof fn lemma_arctan_step_even(t: Rational, k: nat)
    requires
        k > 0,
        k % 2 == 0,
    ensures
        arctan_sum(t, k) == arctan_sum(t, (k - 1) as nat).add_spec(arctan_term(t, k)),
{
}

pub proof fn lemma_arctan_step_odd(t: Rational, k: nat)
    requires
        k > 0,
        k % 2 == 1,
    ensures
        arctan_sum(t, k) == arctan_sum(t, (k - 1) as nat).sub_spec(arctan_term(t, k)),
{
}

// ── small raw arithmetic lemmas ──────────────────────────────────────

/// 0 ≤ c ⇒ a − c ≤ a.
pub proof fn lemma_raw_sub_nonneg_le(a: Rational, c: Rational)
    requires
        Rational::from_int_spec(0).le_spec(c),
    ensures
        a.sub_spec(c).le_spec(a),
{
    let zero = Rational::from_int_spec(0);
    let s = a.sub_spec(c);
    Rational::lemma_add_denom_product_int(a, c.neg_spec());
    Rational::lemma_denom_positive(a);
    Rational::lemma_denom_positive(c);
    assert(zero.num == 0);
    assert(zero.denom() == 1);
    assert(zero.le_spec(c) == (zero.num * c.denom() <= c.num * zero.denom()));
    assert(zero.num * c.denom() <= c.num * zero.denom());
    assert((zero.num * c.denom() <= c.num * zero.denom() && zero.num == 0 && zero.denom() == 1)
        ==> c.num >= 0) by (nonlinear_arith);
    assert(c.num >= 0);
    assert(s.num == a.num * c.denom() + (-c.num) * a.denom());
    assert(s.denom() == a.denom() * c.denom());
    assert(s.le_spec(a) == (s.num * a.denom() <= a.num * s.denom()));
    assert((c.num >= 0 && a.denom() >= 1 && c.denom() >= 1
        && s.num == a.num * c.denom() + (-c.num) * a.denom()
        && s.denom() == a.denom() * c.denom())
        ==> s.num * a.denom() <= a.num * s.denom()) by (nonlinear_arith);
}

/// 0 ≤ c ⇒ a ≤ a + c.
pub proof fn lemma_raw_le_add_nonneg(a: Rational, c: Rational)
    requires
        Rational::from_int_spec(0).le_spec(c),
    ensures
        a.le_spec(a.add_spec(c)),
{
    let zero = Rational::from_int_spec(0);
    let s = a.add_spec(c);
    Rational::lemma_add_denom_product_int(a, c);
    Rational::lemma_denom_positive(a);
    Rational::lemma_denom_positive(c);
    assert(zero.num == 0);
    assert(zero.denom() == 1);
    assert(zero.le_spec(c) == (zero.num * c.denom() <= c.num * zero.denom()));
    assert(zero.num * c.denom() <= c.num * zero.denom());
    assert((zero.num * c.denom() <= c.num * zero.denom() && zero.num == 0 && zero.denom() == 1)
        ==> c.num >= 0) by (nonlinear_arith);
    assert(c.num >= 0);
    assert(s.num == a.num * c.denom() + c.num * a.denom());
    assert(s.denom() == a.denom() * c.denom());
    assert(a.le_spec(s) == (a.num * s.denom() <= s.num * a.denom()));
    assert((c.num >= 0 && a.denom() >= 1 && c.denom() >= 1
        && s.num == a.num * c.denom() + c.num * a.denom()
        && s.denom() == a.denom() * c.denom())
        ==> a.num * s.denom() <= s.num * a.denom()) by (nonlinear_arith);
}

/// a − (a − u) ≡ u.
pub proof fn lemma_raw_sub_sub_cancel(a: Rational, u: Rational)
    ensures
        a.sub_spec(a.sub_spec(u)).eqv_spec(u),
{
    let s = a.sub_spec(u);
    let s2 = a.sub_spec(s);
    Rational::lemma_add_denom_product_int(a, u.neg_spec());
    Rational::lemma_add_denom_product_int(a, s.neg_spec());
    Rational::lemma_denom_positive(a);
    Rational::lemma_denom_positive(u);
    assert(s.num == a.num * u.denom() + (-u.num) * a.denom());
    assert(s.denom() == a.denom() * u.denom());
    assert(s2.num == a.num * s.denom() + (-s.num) * a.denom());
    assert(s2.denom() == a.denom() * s.denom());
    assert(s2.eqv_spec(u) == (s2.num * u.denom() == u.num * s2.denom()));
    assert((a.denom() >= 1 && u.denom() >= 1
        && s.num == a.num * u.denom() + (-u.num) * a.denom()
        && s.denom() == a.denom() * u.denom()
        && s2.num == a.num * s.denom() + (-s.num) * a.denom()
        && s2.denom() == a.denom() * s.denom())
        ==> s2.num * u.denom() == u.num * s2.denom()) by (nonlinear_arith);
}

/// 2x − 2y ≡ 2(x − y).
pub proof fn lemma_raw_two_distrib_sub(x: Rational, y: Rational)
    ensures
        two_x(x).sub_spec(two_x(y)).eqv_spec(two_x(x.sub_spec(y))),
{
    let two = Rational::from_int_spec(2);
    let tx = two_x(x);
    let ty = two_x(y);
    let s = tx.sub_spec(ty);
    let xy = x.sub_spec(y);
    let txy = two_x(xy);
    Rational::lemma_mul_denom_product_int(two, x);
    Rational::lemma_mul_denom_product_int(two, y);
    Rational::lemma_mul_denom_product_int(two, xy);
    Rational::lemma_add_denom_product_int(tx, ty.neg_spec());
    Rational::lemma_add_denom_product_int(x, y.neg_spec());
    Rational::lemma_denom_positive(x);
    Rational::lemma_denom_positive(y);
    assert(two.num == 2);
    assert(two.denom() == 1);
    assert(tx.num == two.num * x.num);
    assert(ty.num == two.num * y.num);
    assert(txy.num == two.num * xy.num);
    assert(xy.num == x.num * y.denom() + (-y.num) * x.denom());
    assert(xy.denom() == x.denom() * y.denom());
    assert(s.num == tx.num * ty.denom() + (-ty.num) * tx.denom());
    assert(s.denom() == tx.denom() * ty.denom());
    assert(s.eqv_spec(txy) == (s.num * txy.denom() == txy.num * s.denom()));
    assert((two.num == 2 && x.denom() >= 1 && y.denom() >= 1
        && tx.num == two.num * x.num && tx.denom() == two.denom() * x.denom()
        && ty.num == two.num * y.num && ty.denom() == two.denom() * y.denom()
        && xy.num == x.num * y.denom() + (-y.num) * x.denom()
        && xy.denom() == x.denom() * y.denom()
        && txy.num == two.num * xy.num && txy.denom() == two.denom() * xy.denom()
        && s.num == tx.num * ty.denom() + (-ty.num) * tx.denom()
        && s.denom() == tx.denom() * ty.denom())
        ==> s.num * txy.denom() == txy.num * s.denom()) by (nonlinear_arith);
}

// ── bracket: adjacent sums ───────────────────────────────────────────

/// k even ⇒ A_{k+1} ≤ A_k (A_{k+1} = A_k − term_{k+1}, term ≥ 0).
pub proof fn lemma_arctan_adjacent_even(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
        k % 2 == 0,
    ensures
        arctan_sum(t, (k + 1) as nat).le_spec(arctan_sum(t, k)),
{
    lemma_arctan_step_odd(t, (k + 1) as nat);
    lemma_arctan_term_nonneg(t, (k + 1) as nat);
    lemma_raw_sub_nonneg_le(arctan_sum(t, k), arctan_term(t, (k + 1) as nat));
}

/// k odd ⇒ A_k ≤ A_{k+1} (A_{k+1} = A_k + term_{k+1}, term ≥ 0).
pub proof fn lemma_arctan_adjacent_odd(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
        k % 2 == 1,
    ensures
        arctan_sum(t, k).le_spec(arctan_sum(t, (k + 1) as nat)),
{
    lemma_arctan_step_even(t, (k + 1) as nat);
    lemma_arctan_term_nonneg(t, (k + 1) as nat);
    lemma_raw_le_add_nonneg(arctan_sum(t, k), arctan_term(t, (k + 1) as nat));
}

// ── bracket: two-step monotonicity ───────────────────────────────────

/// k even ⇒ A_{k+2} ≤ A_k (even partial sums decrease).
pub proof fn lemma_arctan_two_step_even(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
        k % 2 == 0,
    ensures
        arctan_sum(t, (k + 2) as nat).le_spec(arctan_sum(t, k)),
{
    lemma_arctan_step_odd(t, (k + 1) as nat);
    lemma_arctan_step_even(t, (k + 2) as nat);
    lemma_arctan_term_decreasing(t, (k + 1) as nat);
    let a1 = arctan_sum(t, (k + 1) as nat);
    let t1 = arctan_term(t, (k + 1) as nat);
    let t2 = arctan_term(t, (k + 2) as nat);
    // A_{k+2} = A_{k+1} + t2 ≤ A_{k+1} + t1 ≡ A_k
    Rational::lemma_le_add_monotone(t2, t1, a1);
    Rational::lemma_sub_then_add_cancel(arctan_sum(t, k), t1);
    Rational::lemma_add_commutative(t1, arctan_sum(t, k).sub_spec(t1));
    Rational::lemma_eqv_symmetric(t1.add_spec(a1), a1.add_spec(t1));
    Rational::lemma_eqv_transitive(
        a1.add_spec(t1), t1.add_spec(a1), arctan_sum(t, k));
    Rational::lemma_eqv_implies_le(a1.add_spec(t1), arctan_sum(t, k));
    Rational::lemma_le_transitive(a1.add_spec(t2), a1.add_spec(t1), arctan_sum(t, k));
    assert(arctan_sum(t, (k + 2) as nat).le_spec(arctan_sum(t, k)));
}

/// k odd ⇒ A_k ≤ A_{k+2} (odd partial sums increase).
pub proof fn lemma_arctan_two_step_odd(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
        k % 2 == 1,
    ensures
        arctan_sum(t, k).le_spec(arctan_sum(t, (k + 2) as nat)),
{
    lemma_arctan_step_even(t, (k + 1) as nat);
    lemma_arctan_step_odd(t, (k + 2) as nat);
    lemma_arctan_term_decreasing(t, (k + 1) as nat);
    let a1 = arctan_sum(t, (k + 1) as nat);
    let t1 = arctan_term(t, (k + 1) as nat);
    let t2 = arctan_term(t, (k + 2) as nat);
    // A_k ≡ A_{k+1} − t1 ≤ A_{k+1} − t2 = A_{k+2}
    Rational::lemma_sub_le_monotone_right(t2, t1, a1);
    Rational::lemma_add_then_sub_cancel(t1, arctan_sum(t, k));
    Rational::lemma_add_commutative(arctan_sum(t, k), t1);
    Rational::lemma_eqv_reflexive(t1);
    Rational::lemma_eqv_sub_congruence(
        arctan_sum(t, k).add_spec(t1), t1.add_spec(arctan_sum(t, k)), t1, t1);
    Rational::lemma_eqv_transitive(
        a1.sub_spec(t1), t1.add_spec(arctan_sum(t, k)).sub_spec(t1), arctan_sum(t, k));
    Rational::lemma_eqv_symmetric(a1.sub_spec(t1), arctan_sum(t, k));
    Rational::lemma_eqv_implies_le(arctan_sum(t, k), a1.sub_spec(t1));
    Rational::lemma_le_transitive(arctan_sum(t, k), a1.sub_spec(t1), a1.sub_spec(t2));
    assert(arctan_sum(t, k).le_spec(arctan_sum(t, (k + 2) as nat)));
}

// ── width formula ────────────────────────────────────────────────────

/// k even ⇒ 2A_k − 2A_{k+1} ≡ 2·term_{k+1} (exact width).
pub proof fn lemma_arctan_width_even(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
        k % 2 == 0,
    ensures
        two_x(arctan_sum(t, k)).sub_spec(two_x(arctan_sum(t, (k + 1) as nat))).eqv_spec(
            two_x(arctan_term(t, (k + 1) as nat))),
{
    lemma_arctan_step_odd(t, (k + 1) as nat);
    let ak = arctan_sum(t, k);
    let ak1 = arctan_sum(t, (k + 1) as nat);
    let term = arctan_term(t, (k + 1) as nat);
    let two = Rational::from_int_spec(2);
    lemma_raw_two_distrib_sub(ak, ak1);
    lemma_raw_sub_sub_cancel(ak, term);
    assert(ak.sub_spec(ak1) == ak.sub_spec(ak.sub_spec(term)));
    Rational::lemma_eqv_reflexive(two);
    Rational::lemma_eqv_mul_congruence(two, two, ak.sub_spec(ak1), term);
    Rational::lemma_eqv_transitive(
        two_x(ak).sub_spec(two_x(ak1)), two_x(ak.sub_spec(ak1)), two_x(term));
}

/// k odd ⇒ 2A_{k+1} − 2A_k ≡ 2·term_{k+1} (exact width).
pub proof fn lemma_arctan_width_odd(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
        k % 2 == 1,
    ensures
        two_x(arctan_sum(t, (k + 1) as nat)).sub_spec(two_x(arctan_sum(t, k))).eqv_spec(
            two_x(arctan_term(t, (k + 1) as nat))),
{
    lemma_arctan_step_even(t, (k + 1) as nat);
    let ak = arctan_sum(t, k);
    let ak1 = arctan_sum(t, (k + 1) as nat);
    let term = arctan_term(t, (k + 1) as nat);
    let two = Rational::from_int_spec(2);
    lemma_raw_two_distrib_sub(ak1, ak);
    Rational::lemma_add_then_sub_cancel(ak, term);
    assert(ak1.sub_spec(ak) == ak.add_spec(term).sub_spec(ak));
    Rational::lemma_eqv_reflexive(two);
    Rational::lemma_eqv_mul_congruence(two, two, ak1.sub_spec(ak), term);
    Rational::lemma_eqv_transitive(
        two_x(ak1).sub_spec(two_x(ak)), two_x(ak1.sub_spec(ak)), two_x(term));
}

// ── enclosure properties ─────────────────────────────────────────────

/// a ≤ b ⇒ 2a ≤ 2b (two is from_int(2), nonneg).
pub proof fn lemma_two_mul_monotone(a: Rational, b: Rational)
    requires
        a.le_spec(b),
    ensures
        two_x(a).le_spec(two_x(b)),
{
    let two = Rational::from_int_spec(2);
    let zero = Rational::from_int_spec(0);
    assert(zero.le_spec(two));
    Rational::lemma_le_mul_monotone_nonnegative(a, b, two);
    Rational::lemma_mul_commutative(a, two);
    Rational::lemma_mul_commutative(b, two);
    Rational::lemma_eqv_implies_le(two_x(a), a.mul_spec(two));
    Rational::lemma_eqv_symmetric(b.mul_spec(two), two_x(b));
    Rational::lemma_eqv_implies_le(b.mul_spec(two), two_x(b));
    Rational::lemma_le_transitive(two_x(a), a.mul_spec(two), b.mul_spec(two));
    Rational::lemma_le_transitive(two_x(a), b.mul_spec(two), two_x(b));
}

/// The enclosure is always ordered: lo ≤ hi.
pub proof fn lemma_angle_enclosure_ordered(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
    ensures
        crate::angle_ledger::angle_enclosure(t, k).0.le_spec(
            crate::angle_ledger::angle_enclosure(t, k).1),
{
    if k % 2 == 0 {
        lemma_arctan_adjacent_even(t, k);
        lemma_two_mul_monotone(arctan_sum(t, (k + 1) as nat), arctan_sum(t, k));
        assert(angle_enclosure(t, k).0 == two_x(arctan_sum(t, (k + 1) as nat)));
        assert(angle_enclosure(t, k).1 == two_x(arctan_sum(t, k)));
    } else {
        lemma_arctan_adjacent_odd(t, k);
        lemma_two_mul_monotone(arctan_sum(t, k), arctan_sum(t, (k + 1) as nat));
        assert(angle_enclosure(t, k).0 == two_x(arctan_sum(t, k)));
        assert(angle_enclosure(t, k).1 == two_x(arctan_sum(t, (k + 1) as nat)));
    }
}

/// Enclosures nest: enclosure_{k+2} ⊆ enclosure_k (monotone shrink, SPEC §3).
pub proof fn lemma_angle_enclosure_shrink(t: Rational, k: nat)
    requires
        t_in_unit_interval(t),
    ensures
        crate::angle_ledger::angle_enclosure(t, k).0.le_spec(
            crate::angle_ledger::angle_enclosure(t, (k + 2) as nat).0),
        crate::angle_ledger::angle_enclosure(t, (k + 2) as nat).1.le_spec(
            crate::angle_ledger::angle_enclosure(t, k).1),
{
    assert((k + 2) % 2 == k % 2) by (nonlinear_arith);
    if k % 2 == 0 {
        lemma_arctan_two_step_even(t, k);
        lemma_arctan_two_step_odd(t, (k + 1) as nat);
        lemma_two_mul_monotone(arctan_sum(t, (k + 2) as nat), arctan_sum(t, k));
        lemma_two_mul_monotone(arctan_sum(t, (k + 1) as nat), arctan_sum(t, (k + 3) as nat));
        assert(angle_enclosure(t, k).0 == two_x(arctan_sum(t, (k + 1) as nat)));
        assert(angle_enclosure(t, k).1 == two_x(arctan_sum(t, k)));
        assert(angle_enclosure(t, (k + 2) as nat).0 == two_x(arctan_sum(t, (k + 3) as nat)));
        assert(angle_enclosure(t, (k + 2) as nat).1 == two_x(arctan_sum(t, (k + 2) as nat)));
    } else {
        lemma_arctan_two_step_odd(t, k);
        lemma_arctan_two_step_even(t, (k + 1) as nat);
        lemma_two_mul_monotone(arctan_sum(t, k), arctan_sum(t, (k + 2) as nat));
        lemma_two_mul_monotone(arctan_sum(t, (k + 3) as nat), arctan_sum(t, (k + 1) as nat));
        assert(angle_enclosure(t, k).0 == two_x(arctan_sum(t, k)));
        assert(angle_enclosure(t, k).1 == two_x(arctan_sum(t, (k + 1) as nat)));
        assert(angle_enclosure(t, (k + 2) as nat).0 == two_x(arctan_sum(t, (k + 2) as nat)));
        assert(angle_enclosure(t, (k + 2) as nat).1 == two_x(arctan_sum(t, (k + 3) as nat)));
    }
}

} // verus!
