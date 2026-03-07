use vstd::prelude::*;
use verus_algebra::traits::ring::Ring;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::traits::field::OrderedField;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::power::{pow, lemma_pow_zero, lemma_pow_succ, lemma_pow_add, lemma_pow_eqv, lemma_pow_nonneg, lemma_one_pow, lemma_pow_mul_base};
use verus_algebra::archimedean::{nat_mul, lemma_nat_mul_zero, lemma_nat_mul_one, lemma_nat_mul_succ, lemma_nat_mul_add};
use crate::summation::{sum, lemma_sum_empty, lemma_sum_single, lemma_sum_peel_first, lemma_sum_peel_last, lemma_sum_congruence, lemma_sum_split, lemma_sum_add, lemma_sum_scale, lemma_sum_nonneg, lemma_sum_reindex};
use crate::embedding::{from_int, lemma_from_int_zero, lemma_from_int_one, lemma_from_int_add, lemma_from_int_nonneg};

verus! {

// ============================================================
//  Binomial Coefficients (Pascal's triangle)
// ============================================================

/// Binomial coefficient C(n, k) via Pascal's recursion.
pub open spec fn binom(n: nat, k: nat) -> nat
    decreases n,
{
    if k == 0 { 1 }
    else if k > n { 0 }
    else { binom((n - 1) as nat, k) + binom((n - 1) as nat, (k - 1) as nat) }
}

// ============================================================
//  Binomial coefficient lemmas
// ============================================================

/// C(n, 0) = 1.
pub proof fn lemma_binom_zero(n: nat)
    ensures
        binom(n, 0) == 1,
{
}

/// C(n, n) = 1.
pub proof fn lemma_binom_self(n: nat)
    ensures
        binom(n, n) == 1,
    decreases n,
{
    if n == 0 {
        // binom(0, 0) = 1 [k==0 case]
    } else {
        // binom(n, n) = binom(n-1, n) + binom(n-1, n-1)
        // binom(n-1, n) = 0 [k > n case]
        // binom(n-1, n-1) = 1 [IH]
        lemma_binom_self((n - 1) as nat);
        assert(binom((n - 1) as nat, n) == 0);
    }
}

/// C(n, k) = 0 when k > n.
pub proof fn lemma_binom_gt(n: nat, k: nat)
    requires
        k > n,
    ensures
        binom(n, k) == 0,
{
}

/// C(n, 1) = n.
pub proof fn lemma_binom_one(n: nat)
    ensures
        binom(n, 1) == n,
    decreases n,
{
    if n == 0 {
        // binom(0, 1) = 0 [k > n]
    } else {
        // binom(n, 1) = binom(n-1, 1) + binom(n-1, 0)
        // = (n-1) + 1 = n
        lemma_binom_one((n - 1) as nat);
        assert(binom((n - 1) as nat, 0) == 1);
        assert(binom(n, 1) == binom((n - 1) as nat, 1) + binom((n - 1) as nat, 0));
    }
}

/// Pascal's identity: C(n, k) = C(n-1, k) + C(n-1, k-1) when 0 < k ≤ n.
pub proof fn lemma_pascal(n: nat, k: nat)
    requires
        0 < k,
        k <= n,
        n > 0,
    ensures
        binom(n, k) == binom((n - 1) as nat, k) + binom((n - 1) as nat, (k - 1) as nat),
{
    // Definitional — follows from the spec
}

/// C(n, k) = C(n, n-k) when k ≤ n.
pub proof fn lemma_binom_symmetry(n: nat, k: nat)
    requires
        k <= n,
    ensures
        binom(n, k) == binom(n, (n - k) as nat),
    decreases n,
{
    if k == 0 {
        lemma_binom_self(n);
    } else if k == n {
        lemma_binom_self(n);
    } else {
        // 0 < k < n, so n >= 2
        // binom(n, k) = binom(n-1, k) + binom(n-1, k-1)
        // binom(n, n-k) = binom(n-1, n-k) + binom(n-1, n-k-1)
        // IH: binom(n-1, k) = binom(n-1, (n-1)-k) = binom(n-1, n-k-1)
        // IH: binom(n-1, k-1) = binom(n-1, (n-1)-(k-1)) = binom(n-1, n-k)
        let nm1 = (n - 1) as nat;
        lemma_binom_symmetry(nm1, k);
        assert(binom(nm1, k) == binom(nm1, (nm1 - k) as nat));
        assert((nm1 - k) as nat == (n - k - 1) as nat);

        lemma_binom_symmetry(nm1, (k - 1) as nat);
        assert(binom(nm1, (k - 1) as nat) == binom(nm1, (nm1 - (k - 1)) as nat));
        assert((nm1 - (k - 1)) as nat == (n - k) as nat);

        // binom(n, k) = binom(n-1, k) + binom(n-1, k-1)
        //             = binom(n-1, n-k-1) + binom(n-1, n-k)
        //             = binom(n-1, n-k) + binom(n-1, n-k-1)  [+ is commutative]
        //             = binom(n, n-k)
        // The last step is the Pascal identity for binom(n, n-k):
        // binom(n, n-k) = binom(n-1, n-k) + binom(n-1, (n-k)-1) = binom(n-1, n-k) + binom(n-1, n-k-1)
    }
}

// ============================================================
//  Algebra helpers
// ============================================================

/// a*(b*c) ≡ (a*b)*c  (associativity reversed direction).
proof fn lemma_mul_assoc_rev<R: Ring>(a: R, b: R, c: R)
    ensures a.mul(b.mul(c)).eqv(a.mul(b).mul(c))
{
    R::axiom_mul_associative(a, b, c);
    R::axiom_eqv_symmetric(a.mul(b).mul(c), a.mul(b.mul(c)));
}

/// Left commutativity: a*(b*c) ≡ b*(a*c).
proof fn lemma_mul_left_comm<R: Ring>(a: R, b: R, c: R)
    ensures a.mul(b.mul(c)).eqv(b.mul(a.mul(c)))
{
    lemma_mul_assoc_rev::<R>(a, b, c);
    R::axiom_mul_commutative(a, b);
    R::axiom_mul_congruence_left(a.mul(b), b.mul(a), c);
    R::axiom_mul_associative(b, a, c);
    R::axiom_eqv_transitive(a.mul(b.mul(c)), a.mul(b).mul(c), b.mul(a).mul(c));
    R::axiom_eqv_transitive(a.mul(b.mul(c)), b.mul(a).mul(c), b.mul(a.mul(c)));
}

// ============================================================
//  Binomial Theorem
// ============================================================

/// Helper: sum(i=0..n+1, binom(n,i) * a^i * b^(n-i)) ≡ (a+b)^n.
/// Binomial theorem: (a+b)^n ≡ sum(i=0..n+1, C(n,i) * a^i * b^(n-i)).
pub proof fn lemma_binomial_theorem<R: Ring>(a: R, b: R, n: nat)
    ensures
        pow::<R>(a.add(b), n).eqv(
            sum::<R>(
                |i: int| from_int::<R>(binom(n, i as nat) as int).mul(pow::<R>(a, i as nat).mul(pow::<R>(b, (n - i) as nat))),
                0,
                (n + 1) as int,
            )
        ),
    decreases n,
{
    let f = |i: int| -> R {
        from_int::<R>(binom(n, i as nat) as int).mul(
            pow::<R>(a, i as nat).mul(pow::<R>(b, (n - i) as nat))
        )
    };

    if n == 0 {
        // pow(a+b, 0) ≡ 1
        lemma_pow_zero::<R>(a.add(b));
        // sum has one term: binom(0,0) * a^0 * b^0 = 1 * 1 * 1 = 1
        // sum(f, 0, 1) = f(0) + sum(f, 1, 1) = f(0) + 0 ≡ f(0)
        lemma_sum_single::<R>(f, 0);
        // f(0) = from_int(1) * (pow(a,0) * pow(b,0))
        //      ≡ 1 * (1 * 1) ≡ 1

        // from_int(1) ≡ 1
        lemma_from_int_one::<R>();
        // pow(a, 0) ≡ 1
        lemma_pow_zero::<R>(a);
        // pow(b, 0) ≡ 1
        lemma_pow_zero::<R>(b);
        // 1 * 1 ≡ 1
        ring_lemmas::lemma_mul_congruence::<R>(
            pow::<R>(a, 0), R::one(),
            pow::<R>(b, 0), R::one(),
        );
        R::axiom_mul_one_right(R::one());
        R::axiom_eqv_transitive(
            pow::<R>(a, 0).mul(pow::<R>(b, 0)),
            R::one().mul(R::one()),
            R::one(),
        );
        // from_int(1) * (pow(a,0)*pow(b,0)) ≡ 1 * 1 ≡ 1
        ring_lemmas::lemma_mul_congruence::<R>(
            from_int::<R>(1int), R::one(),
            pow::<R>(a, 0).mul(pow::<R>(b, 0)), R::one(),
        );
        R::axiom_mul_one_right(R::one());
        R::axiom_eqv_transitive(
            from_int::<R>(1int).mul(pow::<R>(a, 0).mul(pow::<R>(b, 0))),
            R::one().mul(R::one()),
            R::one(),
        );
        // sum(f, 0, 1) ≡ f(0) ≡ 1
        R::axiom_eqv_transitive(
            sum::<R>(f, 0, 1),
            f(0),
            R::one(),
        );

        // pow(a+b, 0) ≡ 1 ≡ sum(f, 0, 1) [symmetric]
        R::axiom_eqv_symmetric(sum::<R>(f, 0, 1), R::one());
        R::axiom_eqv_transitive(
            pow::<R>(a.add(b), 0),
            R::one(),
            sum::<R>(f, 0, 1),
        );
    } else {
        // (a+b)^n = (a+b) * (a+b)^(n-1)
        lemma_pow_succ::<R>(a.add(b), (n - 1) as nat);
        // gives: pow(a+b, n).eqv((a+b).mul(pow(a+b, n-1)))

        // IH: (a+b)^(n-1) ≡ sum(binom(n-1, i) * a^i * b^(n-1-i), i=0..n)
        let nm1 = (n - 1) as nat;
        lemma_binomial_theorem::<R>(a, b, nm1);

        let g = |i: int| -> R {
            from_int::<R>(binom(nm1, i as nat) as int).mul(
                pow::<R>(a, i as nat).mul(pow::<R>(b, (nm1 - i) as nat))
            )
        };

        // (a+b) * sum(g, 0, n) ≡ (a+b) * (a+b)^(n-1)
        // → pow(a+b, n) ≡ (a+b) * sum(g, 0, n)
        R::axiom_eqv_symmetric(
            pow::<R>(a.add(b), nm1),
            sum::<R>(g, 0, n as int),
        );
        ring_lemmas::lemma_mul_congruence_right::<R>(
            a.add(b),
            pow::<R>(a.add(b), nm1),
            sum::<R>(g, 0, n as int),
        );
        R::axiom_eqv_transitive(
            pow::<R>(a.add(b), n),
            a.add(b).mul(pow::<R>(a.add(b), nm1)),
            a.add(b).mul(sum::<R>(g, 0, n as int)),
        );

        // (a+b) * sum(g) = a*sum(g) + b*sum(g)
        R::axiom_mul_distributes_left(a.add(b), sum::<R>(g, 0, n as int), sum::<R>(g, 0, n as int));
        // Wrong — distributes_left is a*(b+c) = a*b + a*c, not (a+b)*c
        // Use distributes_right: (a+b)*c = a*c + b*c
        ring_lemmas::lemma_mul_distributes_right::<R>(a, b, sum::<R>(g, 0, n as int));

        R::axiom_eqv_transitive(
            pow::<R>(a.add(b), n),
            a.add(b).mul(sum::<R>(g, 0, n as int)),
            a.mul(sum::<R>(g, 0, n as int)).add(b.mul(sum::<R>(g, 0, n as int))),
        );

        // a*sum(g) ≡ sum(a*g(i)), b*sum(g) ≡ sum(b*g(i))  by sum_scale
        lemma_sum_scale::<R>(a, g, 0, n as int);
        lemma_sum_scale::<R>(b, g, 0, n as int);

        let ag = |i: int| -> R { a.mul(g(i)) };
        let bg = |i: int| -> R { b.mul(g(i)) };

        // sum_scale gives: sum(ag, 0, n) ≡ a*sum(g, 0, n). Need reverse.
        R::axiom_eqv_symmetric(
            sum::<R>(ag, 0, n as int),
            a.mul(sum::<R>(g, 0, n as int)),
        );
        R::axiom_eqv_symmetric(
            sum::<R>(bg, 0, n as int),
            b.mul(sum::<R>(g, 0, n as int)),
        );

        additive_group_lemmas::lemma_add_congruence::<R>(
            a.mul(sum::<R>(g, 0, n as int)), sum::<R>(ag, 0, n as int),
            b.mul(sum::<R>(g, 0, n as int)), sum::<R>(bg, 0, n as int),
        );

        R::axiom_eqv_transitive(
            pow::<R>(a.add(b), n),
            a.mul(sum::<R>(g, 0, n as int)).add(b.mul(sum::<R>(g, 0, n as int))),
            sum::<R>(ag, 0, n as int).add(sum::<R>(bg, 0, n as int)),
        );

        // ---- Phase 1: Pointwise transforms ----
        // P(i) = binom(nm1,i) * a^i * b^(n-i)     [absorb b into b-power]
        // A_fn(i) = binom(nm1,i) * a^(i+1) * b^(nm1-i) [absorb a into a-power]
        let P = |i: int| -> R {
            from_int::<R>(binom(nm1, i as nat) as int).mul(
                pow::<R>(a, i as nat).mul(pow::<R>(b, (n - i) as nat))
            )
        };
        let A_fn = |i: int| -> R {
            from_int::<R>(binom(nm1, i as nat) as int).mul(
                pow::<R>(a, (i + 1) as nat).mul(pow::<R>(b, (nm1 - i) as nat))
            )
        };

        // bg(i) ≡ P(i): b * (c * (a^i * b^(nm1-i))) ≡ c * (a^i * b^(n-i))
        // by left-comm to move b inside, then pow_succ on b
        assert forall|i: int| 0 <= i < n as int implies (#[trigger] bg(i)).eqv(P(i)) by {
            let c = from_int::<R>(binom(nm1, i as nat) as int);
            let ai = pow::<R>(a, i as nat);
            let bnm1i = pow::<R>(b, (nm1 - i) as nat);
            // bg(i) = b * (c * (ai * bnm1i))
            // Step 1: b * (c * X) ≡ c * (b * X) by left_comm
            lemma_mul_left_comm::<R>(b, c, ai.mul(bnm1i));
            // gives: b.mul(c.mul(ai.mul(bnm1i))).eqv(c.mul(b.mul(ai.mul(bnm1i))))
            // Step 2: b * (ai * bnm1i) ≡ ai * (b * bnm1i) by left_comm
            lemma_mul_left_comm::<R>(b, ai, bnm1i);
            // Step 3: b * bnm1i ≡ pow(b, n-i) by pow_succ (reversed)
            lemma_pow_succ::<R>(b, (nm1 - i) as nat);
            R::axiom_eqv_symmetric(
                pow::<R>(b, (nm1 - i + 1) as nat),
                b.mul(bnm1i),
            );
            // Chain b * (ai * bnm1i) ≡ ai * (b * bnm1i) ≡ ai * pow(b, n-i)
            ring_lemmas::lemma_mul_congruence_right::<R>(ai, b.mul(bnm1i), pow::<R>(b, (n - i) as nat));
            R::axiom_eqv_transitive(
                b.mul(ai.mul(bnm1i)),
                ai.mul(b.mul(bnm1i)),
                ai.mul(pow::<R>(b, (n - i) as nat)),
            );
            // Chain bg(i) ≡ c * (b * (ai * bnm1i)) ≡ c * (ai * pow(b, n-i)) = P(i)
            ring_lemmas::lemma_mul_congruence_right::<R>(
                c, b.mul(ai.mul(bnm1i)), ai.mul(pow::<R>(b, (n - i) as nat)),
            );
            R::axiom_eqv_transitive(bg(i), c.mul(b.mul(ai.mul(bnm1i))), P(i));
        }
        lemma_sum_congruence::<R>(bg, P, 0, n as int);

        // ag(i) ≡ A_fn(i): a * (c * (a^i * b^(nm1-i))) ≡ c * (a^(i+1) * b^(nm1-i))
        assert forall|i: int| 0 <= i < n as int implies (#[trigger] ag(i)).eqv(A_fn(i)) by {
            let c = from_int::<R>(binom(nm1, i as nat) as int);
            let ai = pow::<R>(a, i as nat);
            let bnm1i = pow::<R>(b, (nm1 - i) as nat);
            // Step 1: a * (c * (ai * bnm1i)) ≡ c * (a * (ai * bnm1i)) by left_comm
            lemma_mul_left_comm::<R>(a, c, ai.mul(bnm1i));
            // Step 2: a * (ai * bnm1i) ≡ (a * ai) * bnm1i by assoc_rev
            lemma_mul_assoc_rev::<R>(a, ai, bnm1i);
            // Step 3: a * ai ≡ pow(a, i+1) by pow_succ (reversed)
            lemma_pow_succ::<R>(a, i as nat);
            R::axiom_eqv_symmetric(pow::<R>(a, (i + 1) as nat), a.mul(ai));
            // (a*ai) * bnm1i ≡ pow(a,i+1) * bnm1i
            R::axiom_mul_congruence_left(a.mul(ai), pow::<R>(a, (i + 1) as nat), bnm1i);
            // Chain: a*(ai*bnm1i) ≡ (a*ai)*bnm1i ≡ pow(a,i+1)*bnm1i
            R::axiom_eqv_transitive(
                a.mul(ai.mul(bnm1i)),
                a.mul(ai).mul(bnm1i),
                pow::<R>(a, (i + 1) as nat).mul(bnm1i),
            );
            // c * (a*(ai*bnm1i)) ≡ c * (pow(a,i+1)*bnm1i) = A_fn(i)
            ring_lemmas::lemma_mul_congruence_right::<R>(
                c, a.mul(ai.mul(bnm1i)), pow::<R>(a, (i + 1) as nat).mul(bnm1i),
            );
            R::axiom_eqv_transitive(ag(i), c.mul(a.mul(ai.mul(bnm1i))), A_fn(i));
        }
        lemma_sum_congruence::<R>(ag, A_fn, 0, n as int);

        // Now: pow(a+b,n) ≡ sum(ag,0,n) + sum(bg,0,n)
        //                  ≡ sum(A_fn,0,n) + sum(P,0,n)
        additive_group_lemmas::lemma_add_congruence::<R>(
            sum::<R>(ag, 0, n as int), sum::<R>(A_fn, 0, n as int),
            sum::<R>(bg, 0, n as int), sum::<R>(P, 0, n as int),
        );
        R::axiom_eqv_transitive(
            pow::<R>(a.add(b), n),
            sum::<R>(ag, 0, n as int).add(sum::<R>(bg, 0, n as int)),
            sum::<R>(A_fn, 0, n as int).add(sum::<R>(P, 0, n as int)),
        );
        // Commute to: sum(P,0,n) + sum(A_fn,0,n)
        R::axiom_add_commutative(sum::<R>(A_fn, 0, n as int), sum::<R>(P, 0, n as int));
        R::axiom_eqv_transitive(
            pow::<R>(a.add(b), n),
            sum::<R>(A_fn, 0, n as int).add(sum::<R>(P, 0, n as int)),
            sum::<R>(P, 0, n as int).add(sum::<R>(A_fn, 0, n as int)),
        );

        // ---- Phase 2: Reindex sum(A_fn, 0, n) → sum(Aj, 1, n+1) ----
        let Aj = |j: int| -> R { A_fn(j + (-1int)) };
        lemma_sum_reindex::<R>(A_fn, 0, n as int, -1int);
        // gives: sum(A_fn, 0, n) ≡ sum(Aj, 1, n+1)

        // Chain: pow(a+b,n) ≡ sum(P,0,n) + sum(Aj,1,n+1)
        additive_group_lemmas::lemma_add_congruence_right::<R>(
            sum::<R>(P, 0, n as int),
            sum::<R>(A_fn, 0, n as int),
            sum::<R>(Aj, 1, (n + 1) as int),
        );
        R::axiom_eqv_transitive(
            pow::<R>(a.add(b), n),
            sum::<R>(P, 0, n as int).add(sum::<R>(A_fn, 0, n as int)),
            sum::<R>(P, 0, n as int).add(sum::<R>(Aj, 1, (n + 1) as int)),
        );

        // ---- Phase 3: Pascal for middle terms ----
        // For j in [1, n): P(j) + Aj(j) ≡ f(j)
        // P(j) = binom(nm1,j) * (a^j * b^(n-j))
        // Aj(j) = A_fn(j-1) = binom(nm1,j-1) * (a^j * b^(n-j))
        // P(j) + Aj(j) = (binom(nm1,j) + binom(nm1,j-1)) * X = binom(n,j) * X = f(j)
        let PA = |j: int| -> R { P(j).add(Aj(j)) };
        assert forall|j: int| 1 <= j < n as int implies (#[trigger] PA(j)).eqv(f(j)) by {
            let c1 = from_int::<R>(binom(nm1, j as nat) as int);
            let c2 = from_int::<R>(binom(nm1, (j - 1) as nat) as int);
            let X = pow::<R>(a, j as nat).mul(pow::<R>(b, (n - j) as nat));
            // P(j) = c1 * X, Aj(j) = c2 * X  [definitional]
            // c1*X + c2*X ≡ (c1+c2)*X  by distributes_right reversed
            ring_lemmas::lemma_mul_distributes_right::<R>(c1, c2, X);
            R::axiom_eqv_symmetric(c1.add(c2).mul(X), c1.mul(X).add(c2.mul(X)));
            // c1 + c2 = from_int(binom(nm1,j)) + from_int(binom(nm1,j-1))
            //         ≡ from_int(binom(nm1,j) + binom(nm1,j-1))  by from_int_add reversed
            lemma_from_int_add::<R>(binom(nm1, j as nat) as int, binom(nm1, (j - 1) as nat) as int);
            R::axiom_eqv_symmetric(
                from_int::<R>((binom(nm1, j as nat) as int) + (binom(nm1, (j - 1) as nat) as int)),
                c1.add(c2),
            );
            // Pascal: binom(nm1,j) + binom(nm1,j-1) == binom(n,j)
            lemma_pascal(n, j as nat);
            // Help SMT see the int equality from the nat equality
            assert((binom(nm1, j as nat) as int) + (binom(nm1, (j - 1) as nat) as int) == binom(n, j as nat) as int);
            // (c1+c2)*X ≡ from_int(binom(n,j))*X = f(j) by congruence_left
            R::axiom_mul_congruence_left(c1.add(c2), from_int::<R>(binom(n, j as nat) as int), X);
            // Chain: PA(j) = c1*X + c2*X ≡ (c1+c2)*X ≡ f(j)
            R::axiom_eqv_transitive(PA(j), c1.add(c2).mul(X), f(j));
        }

        // ---- Phase 4: Reassembly ----
        // Goal: sum(P,0,n) + sum(Aj,1,n+1) ≡ sum(f,0,n+1)

        // (a) Peel: sum(P,0,n) = P(0) + sum(P,1,n)
        lemma_sum_peel_first::<R>(P, 0, n as int);
        // (b) Peel: sum(Aj,1,n+1) = sum(Aj,1,n) + Aj(n)
        lemma_sum_peel_last::<R>(Aj, 1, (n + 1) as int);

        // (c) Middle: sum(P,1,n) + sum(Aj,1,n) ≡ sum(f,1,n)
        // sum_add(P, Aj): sum(PA, 1, n) ≡ sum(P,1,n) + sum(Aj,1,n)
        lemma_sum_add::<R>(P, Aj, 1, n as int);
        // sum(PA,1,n) ≡ sum(f,1,n) from Phase 3
        lemma_sum_congruence::<R>(PA, f, 1, n as int);
        // Chain: sum(P,1,n)+sum(Aj,1,n) ≡ sum(PA,1,n) ≡ sum(f,1,n)
        R::axiom_eqv_symmetric(
            sum::<R>(PA, 1, n as int),
            sum::<R>(P, 1, n as int).add(sum::<R>(Aj, 1, n as int)),
        );
        R::axiom_eqv_transitive(
            sum::<R>(P, 1, n as int).add(sum::<R>(Aj, 1, n as int)),
            sum::<R>(PA, 1, n as int),
            sum::<R>(f, 1, n as int),
        );

        // (d) Boundary: P(0) == f(0) and Aj(n) == f(n) [definitional, binom(_,0)=1, binom(_,_)=1]
        lemma_binom_zero(nm1);
        lemma_binom_zero(n);
        assert(P(0int) == f(0int));
        lemma_binom_self(nm1);
        lemma_binom_self(n);
        assert(Aj(n as int) == f(n as int));

        // (e) Combine: sum(f,1,n) + Aj(n) ≡ sum(f,1,n) + f(n) = sum(f,1,n+1)
        // by peel_last reversed
        lemma_sum_peel_last::<R>(f, 1, (n + 1) as int);
        R::axiom_eqv_symmetric(
            sum::<R>(f, 1, (n + 1) as int),
            sum::<R>(f, 1, n as int).add(f(n as int)),
        );

        // (f) Build: sum(P,0,n) + sum(Aj,1,n+1) ≡ f(0) + sum(f,1,n+1) ≡ sum(f,0,n+1)
        // Start: sum(P,0,n) + sum(Aj,1,n+1)
        //      ≡ (P(0) + sum(P,1,n)) + (sum(Aj,1,n) + Aj(n))    [peeling from (a),(b)]
        R::axiom_add_congruence_left(
            sum::<R>(P, 0, n as int),
            P(0int).add(sum::<R>(P, 1, n as int)),
            sum::<R>(Aj, 1, (n + 1) as int),
        );
        additive_group_lemmas::lemma_add_congruence_right::<R>(
            P(0int).add(sum::<R>(P, 1, n as int)),
            sum::<R>(Aj, 1, (n + 1) as int),
            sum::<R>(Aj, 1, n as int).add(Aj(n as int)),
        );
        R::axiom_eqv_transitive(
            sum::<R>(P, 0, n as int).add(sum::<R>(Aj, 1, (n + 1) as int)),
            P(0int).add(sum::<R>(P, 1, n as int)).add(sum::<R>(Aj, 1, (n + 1) as int)),
            P(0int).add(sum::<R>(P, 1, n as int)).add(sum::<R>(Aj, 1, n as int).add(Aj(n as int))),
        );

        // Reassociate: (P(0)+sP1) + (sAj1+Aj(n))
        //            ≡ P(0) + (sP1 + (sAj1 + Aj(n)))
        R::axiom_add_associative(
            P(0int),
            sum::<R>(P, 1, n as int),
            sum::<R>(Aj, 1, n as int).add(Aj(n as int)),
        );
        R::axiom_eqv_transitive(
            sum::<R>(P, 0, n as int).add(sum::<R>(Aj, 1, (n + 1) as int)),
            P(0int).add(sum::<R>(P, 1, n as int)).add(sum::<R>(Aj, 1, n as int).add(Aj(n as int))),
            P(0int).add(sum::<R>(P, 1, n as int).add(sum::<R>(Aj, 1, n as int).add(Aj(n as int)))),
        );

        // Inner: sP1 + (sAj1 + Aj(n))
        //      ≡ (sP1 + sAj1) + Aj(n)     [assoc reversed]
        R::axiom_add_associative(
            sum::<R>(P, 1, n as int),
            sum::<R>(Aj, 1, n as int),
            Aj(n as int),
        );
        R::axiom_eqv_symmetric(
            sum::<R>(P, 1, n as int).add(sum::<R>(Aj, 1, n as int)).add(Aj(n as int)),
            sum::<R>(P, 1, n as int).add(sum::<R>(Aj, 1, n as int).add(Aj(n as int))),
        );
        //      ≡ sum(f,1,n) + Aj(n)        [from (c)]
        R::axiom_add_congruence_left(
            sum::<R>(P, 1, n as int).add(sum::<R>(Aj, 1, n as int)),
            sum::<R>(f, 1, n as int),
            Aj(n as int),
        );
        R::axiom_eqv_transitive(
            sum::<R>(P, 1, n as int).add(sum::<R>(Aj, 1, n as int).add(Aj(n as int))),
            sum::<R>(P, 1, n as int).add(sum::<R>(Aj, 1, n as int)).add(Aj(n as int)),
            sum::<R>(f, 1, n as int).add(Aj(n as int)),
        );
        //      ≡ sum(f,1,n) + f(n) = sum(f,1,n+1)  [from (e), boundary]
        R::axiom_eqv_transitive(
            sum::<R>(P, 1, n as int).add(sum::<R>(Aj, 1, n as int).add(Aj(n as int))),
            sum::<R>(f, 1, n as int).add(Aj(n as int)),
            sum::<R>(f, 1, (n + 1) as int),
        );

        // Outer: P(0) + inner ≡ P(0) + sum(f,1,n+1) = f(0) + sum(f,1,n+1) = sum(f,0,n+1)
        additive_group_lemmas::lemma_add_congruence_right::<R>(
            P(0int),
            sum::<R>(P, 1, n as int).add(sum::<R>(Aj, 1, n as int).add(Aj(n as int))),
            sum::<R>(f, 1, (n + 1) as int),
        );
        R::axiom_eqv_transitive(
            sum::<R>(P, 0, n as int).add(sum::<R>(Aj, 1, (n + 1) as int)),
            P(0int).add(sum::<R>(P, 1, n as int).add(sum::<R>(Aj, 1, n as int).add(Aj(n as int)))),
            P(0int).add(sum::<R>(f, 1, (n + 1) as int)),
        );

        // P(0) == f(0), so P(0) + sum(f,1,n+1) == f(0) + sum(f,1,n+1)
        // f(0) + sum(f,1,n+1) ≡ sum(f,0,n+1) by peel_first reversed
        lemma_sum_peel_first::<R>(f, 0, (n + 1) as int);
        R::axiom_eqv_symmetric(
            sum::<R>(f, 0, (n + 1) as int),
            f(0int).add(sum::<R>(f, 1, (n + 1) as int)),
        );

        // Final chain: pow(a+b,n) ≡ sum(P,0,n)+sum(Aj,1,n+1) ≡ f(0)+sum(f,1,n+1) ≡ sum(f,0,n+1)
        R::axiom_eqv_transitive(
            pow::<R>(a.add(b), n),
            sum::<R>(P, 0, n as int).add(sum::<R>(Aj, 1, (n + 1) as int)),
            P(0int).add(sum::<R>(f, 1, (n + 1) as int)),
        );
        R::axiom_eqv_transitive(
            pow::<R>(a.add(b), n),
            P(0int).add(sum::<R>(f, 1, (n + 1) as int)),
            sum::<R>(f, 0, (n + 1) as int),
        );
    }
}

// ============================================================
//  Bernstein Basis
// ============================================================

/// Bernstein basis polynomial: B_{i,n}(t) = C(n,i) * t^i * (1-t)^(n-i).
pub open spec fn bernstein<F: OrderedField>(n: nat, i: nat, t: F) -> F {
    from_int::<F>(binom(n, i) as int).mul(
        pow::<F>(t, i).mul(pow::<F>(F::one().sub(t), (n - i) as nat))
    )
}

/// Bernstein basis is nonneg when 0 ≤ t ≤ 1.
pub proof fn lemma_bernstein_nonneg<F: OrderedField>(n: nat, i: nat, t: F)
    requires
        i <= n,
        F::zero().le(t),
        t.le(F::one()),
    ensures
        F::zero().le(bernstein::<F>(n, i, t)),
{
    // binom(n, i) ≥ 0 [it's a nat]
    // t ≥ 0 → t^i ≥ 0
    // 1-t ≥ 0 → (1-t)^(n-i) ≥ 0
    // Product of nonneg terms is nonneg.

    // t^i ≥ 0
    lemma_pow_nonneg::<F>(t, i);

    // 1-t ≥ 0
    // 0 ≤ t ≤ 1 → 0 ≤ 1-t
    ordered_ring_lemmas::lemma_le_sub_monotone::<F>(t, F::one(), t);
    additive_group_lemmas::lemma_sub_self::<F>(t);
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        t.sub(t), F::zero(), F::one().sub(t),
    );

    // (1-t)^(n-i) ≥ 0
    lemma_pow_nonneg::<F>(F::one().sub(t), (n - i) as nat);

    // t^i * (1-t)^(n-i) ≥ 0
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(
        pow::<F>(t, i),
        pow::<F>(F::one().sub(t), (n - i) as nat),
    );

    // from_int(binom(n,i)) ≥ 0
    lemma_from_int_nonneg::<F>(binom(n, i) as int);

    // Product ≥ 0
    ordered_ring_lemmas::lemma_nonneg_mul_nonneg::<F>(
        from_int::<F>(binom(n, i) as int),
        pow::<F>(t, i).mul(pow::<F>(F::one().sub(t), (n - i) as nat)),
    );
}

/// Partition of unity: sum of Bernstein basis over i=0..n+1 equals 1.
/// This follows from the binomial theorem with a=t, b=1-t, a+b=1.
pub proof fn lemma_bernstein_partition_of_unity<F: OrderedField>(n: nat, t: F)
    ensures
        sum::<F>(|i: int| bernstein::<F>(n, i as nat, t), 0, (n + 1) as int).eqv(F::one()),
{
    // (t + (1-t))^n ≡ sum(binom(n,i) * t^i * (1-t)^(n-i))
    // t + (1-t) ≡ 1
    // 1^n ≡ 1
    // So sum ≡ 1.

    // t + (1-t) ≡ 1
    additive_group_lemmas::lemma_sub_then_add_cancel::<F>(F::one(), t);
    F::axiom_add_commutative(t, F::one().sub(t));
    // t + (1-t) ≡ (1-t) + t ≡ 1

    // Actually sub_then_add_cancel gives (1-t)+t ≡ 1
    // add_commutative gives t + (1-t) ≡ (1-t) + t
    // Transitive: t + (1-t) ≡ 1
    F::axiom_eqv_transitive(
        t.add(F::one().sub(t)),
        F::one().sub(t).add(t),
        F::one(),
    );

    // pow(1, n) ≡ 1
    lemma_one_pow::<F>(n);

    // pow(t + (1-t), n) ≡ pow(1, n) ≡ 1
    lemma_pow_eqv::<F>(t.add(F::one().sub(t)), F::one(), n);
    F::axiom_eqv_transitive(
        pow::<F>(t.add(F::one().sub(t)), n),
        pow::<F>(F::one(), n),
        F::one(),
    );

    // Binomial theorem: pow(t+(1-t), n) ≡ sum(binom(n,i)*t^i*(1-t)^(n-i))
    lemma_binomial_theorem::<F>(t, F::one().sub(t), n);

    // The bernstein function is exactly binom(n,i) * t^i * (1-t)^(n-i) = bernstein(n,i,t)
    // sum(|i| bernstein(n, i as nat, t), 0, n+1)
    // ≡ sum(|i| from_int(binom(n, i as nat)) * (t^i * (1-t)^(n-i)), 0, n+1)
    // which is the same as the binomial theorem's sum

    // pow(t+(1-t), n) ≡ sum(binomial_term, 0, n+1)
    // and pow(t+(1-t), n) ≡ 1
    // So sum ≡ 1

    // But we need sum(bernstein, ...) ≡ sum(binomial_term, ...) via congruence.
    let bt = |i: int| -> F {
        from_int::<F>(binom(n, i as nat) as int).mul(
            pow::<F>(t, i as nat).mul(pow::<F>(F::one().sub(t), (n - i) as nat))
        )
    };
    let bern = |i: int| -> F { bernstein::<F>(n, i as nat, t) };

    assert forall|i: int| 0 <= i < (n + 1) as int implies (#[trigger] bern(i)).eqv(bt(i)) by {
        F::axiom_eqv_reflexive(bern(i));
    }
    lemma_sum_congruence::<F>(bern, bt, 0, (n + 1) as int);

    // sum(bern) ≡ sum(bt) ≡ pow(t+(1-t), n) ≡ 1
    F::axiom_eqv_symmetric(
        pow::<F>(t.add(F::one().sub(t)), n),
        sum::<F>(bt, 0, (n + 1) as int),
    );
    F::axiom_eqv_transitive(
        sum::<F>(bern, 0, (n + 1) as int),
        sum::<F>(bt, 0, (n + 1) as int),
        pow::<F>(t.add(F::one().sub(t)), n),
    );
    F::axiom_eqv_transitive(
        sum::<F>(bern, 0, (n + 1) as int),
        pow::<F>(t.add(F::one().sub(t)), n),
        F::one(),
    );
}

} // verus!
