use vstd::prelude::*;
use verus_algebra::traits::ring::Ring;
use verus_algebra::traits::ordered_ring::OrderedRing;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::archimedean::{nat_mul, lemma_nat_mul_zero, lemma_nat_mul_one, lemma_nat_mul_succ, lemma_nat_mul_add, lemma_nat_mul_congruence, lemma_nat_mul_nonneg};
use verus_algebra::inequalities;

verus! {

// ============================================================
//  Integer Embedding into a Ring
// ============================================================

/// Embed an integer into a ring: from_int(n) = n * 1.
/// For n > 0: nat_mul(n, 1).
/// For n == 0: 0.
/// For n < 0: neg(nat_mul(-n, 1)).
pub open spec fn from_int<R: Ring>(n: int) -> R {
    if n > 0 { nat_mul::<R>(n as nat, R::one()) }
    else if n == 0 { R::zero() }
    else { nat_mul::<R>((-n) as nat, R::one()).neg() }
}

// ============================================================
//  Basic lemmas
// ============================================================

/// from_int(0) ≡ 0.
pub proof fn lemma_from_int_zero<R: Ring>()
    ensures
        from_int::<R>(0int).eqv(R::zero()),
{
    R::axiom_eqv_reflexive(R::zero());
}

/// from_int(1) ≡ 1.
pub proof fn lemma_from_int_one<R: Ring>()
    ensures
        from_int::<R>(1int).eqv(R::one()),
{
    lemma_nat_mul_one::<R>(R::one());
}

/// from_int(-n) ≡ neg(from_int(n)).
pub proof fn lemma_from_int_neg<R: Ring>(n: int)
    ensures
        from_int::<R>(-n).eqv(from_int::<R>(n).neg()),
{
    if n > 0 {
        // from_int(-n): -n < 0, so nat_mul(n, 1).neg()
        // from_int(n).neg() = nat_mul(n, 1).neg()
        R::axiom_eqv_reflexive(nat_mul::<R>(n as nat, R::one()).neg());
    } else if n == 0 {
        // from_int(0) = 0, from_int(0).neg() = 0.neg()
        // from_int(-0) = from_int(0) = 0
        // Need: 0.eqv(0.neg())
        additive_group_lemmas::lemma_neg_zero::<R>();
        R::axiom_eqv_symmetric(R::zero().neg(), R::zero());
    } else {
        // n < 0, -n > 0
        // from_int(-n) = nat_mul(-n, 1)
        // from_int(n) = nat_mul(-n, 1).neg()
        // from_int(n).neg() = nat_mul(-n, 1).neg().neg()
        // Need: nat_mul(-n, 1).eqv(nat_mul(-n, 1).neg().neg())
        additive_group_lemmas::lemma_neg_involution::<R>(nat_mul::<R>((-n) as nat, R::one()));
        R::axiom_eqv_symmetric(
            nat_mul::<R>((-n) as nat, R::one()).neg().neg(),
            nat_mul::<R>((-n) as nat, R::one()),
        );
    }
}

/// Helper: from_int(m + n) ≡ from_int(m) + from_int(n) when m ≥ 0 and n ≥ 0.
proof fn lemma_from_int_add_nonneg<R: Ring>(m: int, n: int)
    requires
        m >= 0,
        n >= 0,
    ensures
        from_int::<R>(m + n).eqv(from_int::<R>(m).add(from_int::<R>(n))),
{
    if m == 0 {
        // from_int(0) + from_int(n) = 0 + from_int(n) ≡ from_int(n) = from_int(0+n)
        additive_group_lemmas::lemma_add_zero_left::<R>(from_int::<R>(n));
        R::axiom_eqv_symmetric(
            R::zero().add(from_int::<R>(n)),
            from_int::<R>(n),
        );
    } else if n == 0 {
        // from_int(m) + 0 ≡ from_int(m) = from_int(m+0)
        R::axiom_add_zero_right(from_int::<R>(m));
        R::axiom_eqv_symmetric(
            from_int::<R>(m).add(R::zero()),
            from_int::<R>(m),
        );
    } else {
        // m > 0, n > 0, m+n > 0
        assert((m + n) as nat == (m as nat) + (n as nat));
        lemma_nat_mul_add::<R>(m as nat, n as nat, R::one());
    }
}

/// from_int(m + n) ≡ from_int(m) + from_int(n).
pub proof fn lemma_from_int_add<R: Ring>(m: int, n: int)
    ensures
        from_int::<R>(m + n).eqv(from_int::<R>(m).add(from_int::<R>(n))),
    decreases (if m < 0 && n >= 0 { 1int } else { 0int }),
{
    if m >= 0 && n >= 0 {
        lemma_from_int_add_nonneg::<R>(m, n);
    } else if m <= 0 && n <= 0 {
        // Both nonpositive.
        // Strategy: from_int(m)+from_int(n) ≡ -from_int(-m) + -from_int(-n) ≡ -(from_int(-m)+from_int(-n))
        // ≡ -from_int(-m + -n) = -from_int(-(m+n)) ≡ from_int(m+n)

        // Step 1: from_int(m) ≡ -from_int(-m)
        // from_int_neg(-m): from_int(m) ≡ from_int(-m).neg()
        lemma_from_int_neg::<R>(-m);
        assert(-(-m) == m);
        // gives: from_int(m).eqv(from_int(-m).neg())

        // Step 2: from_int(n) ≡ -from_int(-n)
        lemma_from_int_neg::<R>(-n);
        assert(-(-n) == n);

        // Step 3: from_int(m)+from_int(n) ≡ from_int(-m).neg()+from_int(-n).neg()
        R::axiom_eqv_symmetric(from_int::<R>(m), from_int::<R>(-m).neg());
        R::axiom_eqv_symmetric(from_int::<R>(n), from_int::<R>(-n).neg());
        additive_group_lemmas::lemma_add_congruence::<R>(
            from_int::<R>(m), from_int::<R>(-m).neg(),
            from_int::<R>(n), from_int::<R>(-n).neg(),
        );

        // Step 4: neg(a)+neg(b) ≡ neg(a+b)
        additive_group_lemmas::lemma_neg_add::<R>(from_int::<R>(-m), from_int::<R>(-n));
        R::axiom_eqv_symmetric(
            from_int::<R>(-m).add(from_int::<R>(-n)).neg(),
            from_int::<R>(-m).neg().add(from_int::<R>(-n).neg()),
        );

        // Chain steps 3+4
        R::axiom_eqv_transitive(
            from_int::<R>(m).add(from_int::<R>(n)),
            from_int::<R>(-m).neg().add(from_int::<R>(-n).neg()),
            from_int::<R>(-m).add(from_int::<R>(-n)).neg(),
        );

        // Step 5: from_int(-m)+from_int(-n) ≡ from_int(-m + -n)
        lemma_from_int_add_nonneg::<R>(-m, -n);
        assert((-m) + (-n) == -(m + n));
        // gives: from_int(-(m+n)).eqv(from_int(-m).add(from_int(-n)))
        // We need: from_int(-m).add(from_int(-n)).eqv(from_int(-(m+n)))
        R::axiom_eqv_symmetric(
            from_int::<R>(-(m + n)),
            from_int::<R>(-m).add(from_int::<R>(-n)),
        );

        // Step 6: neg congruence
        R::axiom_neg_congruence(
            from_int::<R>(-m).add(from_int::<R>(-n)),
            from_int::<R>(-(m + n)),
        );

        // Chain steps 4+6: from_int(m)+from_int(n) ≡ neg(from_int(-(m+n)))
        R::axiom_eqv_transitive(
            from_int::<R>(m).add(from_int::<R>(n)),
            from_int::<R>(-m).add(from_int::<R>(-n)).neg(),
            from_int::<R>(-(m + n)).neg(),
        );

        // Step 7: neg(from_int(-(m+n))) ≡ from_int(m+n)
        // from_int_neg(m+n): from_int(-(m+n)).eqv(from_int(m+n).neg())
        lemma_from_int_neg::<R>(m + n);
        R::axiom_neg_congruence(from_int::<R>(-(m + n)), from_int::<R>(m + n).neg());
        // gives: from_int(-(m+n)).neg().eqv(from_int(m+n).neg().neg())
        additive_group_lemmas::lemma_neg_involution::<R>(from_int::<R>(m + n));
        R::axiom_eqv_transitive(
            from_int::<R>(-(m + n)).neg(),
            from_int::<R>(m + n).neg().neg(),
            from_int::<R>(m + n),
        );

        // Final chain
        R::axiom_eqv_transitive(
            from_int::<R>(m).add(from_int::<R>(n)),
            from_int::<R>(-(m + n)).neg(),
            from_int::<R>(m + n),
        );

        // Flip
        R::axiom_eqv_symmetric(
            from_int::<R>(m).add(from_int::<R>(n)),
            from_int::<R>(m + n),
        );
    } else if m >= 0 && n < 0 {
        // m >= 0, n < 0
        if m + n >= 0 {
            // from_int(m+n) + from_int(-n) ≡ from_int((m+n)+(-n)) = from_int(m)
            assert((m + n) + (-n) == m);
            lemma_from_int_add_nonneg::<R>(m + n, -n);
            // gives: from_int(m).eqv(from_int(m+n).add(from_int(-n)))

            // from_int(m+n) + from_int(-n) ≡ from_int(m)
            R::axiom_eqv_symmetric(
                from_int::<R>(m),
                from_int::<R>(m + n).add(from_int::<R>(-n)),
            );
            // gives: from_int(m+n).add(from_int(-n)).eqv(from_int(m))

            // Subtract from_int(-n): use add_then_sub_cancel
            // from_int(m+n) + from_int(-n) - from_int(-n) ≡ from_int(m+n)
            additive_group_lemmas::lemma_add_then_sub_cancel::<R>(from_int::<R>(m + n), from_int::<R>(-n));

            // Apply sub_congruence with the established eqv
            R::axiom_eqv_reflexive(from_int::<R>(-n));
            additive_group_lemmas::lemma_sub_congruence::<R>(
                from_int::<R>(m + n).add(from_int::<R>(-n)), from_int::<R>(m),
                from_int::<R>(-n), from_int::<R>(-n),
            );
            // gives: (from_int(m+n)+from_int(-n)).sub(from_int(-n)).eqv(from_int(m).sub(from_int(-n)))

            // Chain: from_int(m+n) ≡ (a+b)-b ≡ from_int(m) - from_int(-n)
            R::axiom_eqv_symmetric(
                from_int::<R>(m + n).add(from_int::<R>(-n)).sub(from_int::<R>(-n)),
                from_int::<R>(m + n),
            );
            R::axiom_eqv_transitive(
                from_int::<R>(m + n),
                from_int::<R>(m + n).add(from_int::<R>(-n)).sub(from_int::<R>(-n)),
                from_int::<R>(m).sub(from_int::<R>(-n)),
            );

            // from_int(m) - from_int(-n) ≡ from_int(m) + from_int(-n).neg()
            R::axiom_sub_is_add_neg(from_int::<R>(m), from_int::<R>(-n));

            R::axiom_eqv_transitive(
                from_int::<R>(m + n),
                from_int::<R>(m).sub(from_int::<R>(-n)),
                from_int::<R>(m).add(from_int::<R>(-n).neg()),
            );

            // from_int(-n).neg() ≡ from_int(n)
            // from_int_neg(-n): from_int(n).eqv(from_int(-n).neg())
            lemma_from_int_neg::<R>(-n);
            assert(-(-n) == n);
            // from_int(n).eqv(from_int(-n).neg())
            R::axiom_eqv_symmetric(from_int::<R>(n), from_int::<R>(-n).neg());
            // from_int(-n).neg().eqv(from_int(n))

            additive_group_lemmas::lemma_add_congruence_right::<R>(
                from_int::<R>(m),
                from_int::<R>(-n).neg(),
                from_int::<R>(n),
            );

            R::axiom_eqv_transitive(
                from_int::<R>(m + n),
                from_int::<R>(m).add(from_int::<R>(-n).neg()),
                from_int::<R>(m).add(from_int::<R>(n)),
            );
        } else {
            // m + n < 0
            // from_int(m) + from_int(-(m+n)) ≡ from_int(m + (-(m+n))) = from_int(-n)
            assert(m + (-(m + n)) == -n);
            lemma_from_int_add_nonneg::<R>(m, -(m + n));
            // gives: from_int(-n).eqv(from_int(m).add(from_int(-(m+n))))

            // Sub from_int(m) from both sides:
            // from_int(-(m+n)) ≡ from_int(-n) - from_int(m)
            R::axiom_eqv_symmetric(
                from_int::<R>(-n),
                from_int::<R>(m).add(from_int::<R>(-(m + n))),
            );
            // gives: from_int(m).add(from_int(-(m+n))).eqv(from_int(-n))

            // Use add_comm + add_then_sub_cancel to isolate from_int(-(m+n))
            // from_int(-(m+n)) + from_int(m) - from_int(m) ≡ from_int(-(m+n))
            additive_group_lemmas::lemma_add_then_sub_cancel::<R>(from_int::<R>(-(m + n)), from_int::<R>(m));

            // comm: from_int(-(m+n))+from_int(m) ≡ from_int(m)+from_int(-(m+n))
            R::axiom_add_commutative(from_int::<R>(-(m + n)), from_int::<R>(m));
            // Chain to from_int(-n)
            R::axiom_eqv_transitive(
                from_int::<R>(-(m + n)).add(from_int::<R>(m)),
                from_int::<R>(m).add(from_int::<R>(-(m + n))),
                from_int::<R>(-n),
            );

            // sub_congruence
            R::axiom_eqv_reflexive(from_int::<R>(m));
            additive_group_lemmas::lemma_sub_congruence::<R>(
                from_int::<R>(-(m + n)).add(from_int::<R>(m)), from_int::<R>(-n),
                from_int::<R>(m), from_int::<R>(m),
            );
            // (from_int(-(m+n))+from_int(m)).sub(from_int(m)).eqv(from_int(-n).sub(from_int(m)))

            // Chain: from_int(-(m+n)) ≡ ... ≡ from_int(-n) - from_int(m)
            R::axiom_eqv_symmetric(
                from_int::<R>(-(m + n)).add(from_int::<R>(m)).sub(from_int::<R>(m)),
                from_int::<R>(-(m + n)),
            );
            R::axiom_eqv_transitive(
                from_int::<R>(-(m + n)),
                from_int::<R>(-(m + n)).add(from_int::<R>(m)).sub(from_int::<R>(m)),
                from_int::<R>(-n).sub(from_int::<R>(m)),
            );

            // Negate both sides: from_int(-(m+n)).neg() ≡ (from_int(-n)-from_int(m)).neg()
            R::axiom_neg_congruence(
                from_int::<R>(-(m + n)),
                from_int::<R>(-n).sub(from_int::<R>(m)),
            );

            // from_int(-(m+n)).neg() ≡ from_int(m+n)
            // from_int_neg(m+n): from_int(-(m+n)).eqv(from_int(m+n).neg())
            lemma_from_int_neg::<R>(m + n);
            R::axiom_neg_congruence(from_int::<R>(-(m + n)), from_int::<R>(m + n).neg());
            additive_group_lemmas::lemma_neg_involution::<R>(from_int::<R>(m + n));
            R::axiom_eqv_transitive(
                from_int::<R>(-(m + n)).neg(),
                from_int::<R>(m + n).neg().neg(),
                from_int::<R>(m + n),
            );

            // (from_int(-n) - from_int(m)).neg() ≡ from_int(m) - from_int(-n)
            additive_group_lemmas::lemma_sub_antisymmetric::<R>(from_int::<R>(-n), from_int::<R>(m));
            // gives: from_int(-n).sub(from_int(m)).eqv(from_int(m).sub(from_int(-n)).neg())
            R::axiom_neg_congruence(
                from_int::<R>(-n).sub(from_int::<R>(m)),
                from_int::<R>(m).sub(from_int::<R>(-n)).neg(),
            );
            // gives: from_int(-n).sub(from_int(m)).neg().eqv(from_int(m).sub(from_int(-n)).neg().neg())
            additive_group_lemmas::lemma_neg_involution::<R>(from_int::<R>(m).sub(from_int::<R>(-n)));
            R::axiom_eqv_transitive(
                from_int::<R>(-n).sub(from_int::<R>(m)).neg(),
                from_int::<R>(m).sub(from_int::<R>(-n)).neg().neg(),
                from_int::<R>(m).sub(from_int::<R>(-n)),
            );

            // Chain: from_int(m+n) ≡ from_int(-(m+n)).neg() ... hmm this is getting circular.
            // Let me chain: from_int(-(m+n)).neg() ≡ (from_int(-n)-from_int(m)).neg()
            //               ≡ from_int(m) - from_int(-n)
            R::axiom_eqv_transitive(
                from_int::<R>(-(m + n)).neg(),
                from_int::<R>(-n).sub(from_int::<R>(m)).neg(),
                from_int::<R>(m).sub(from_int::<R>(-n)),
            );

            // from_int(m+n) ≡ from_int(-(m+n)).neg() ≡ from_int(m) - from_int(-n)
            R::axiom_eqv_transitive(
                from_int::<R>(m + n),
                from_int::<R>(-(m + n)).neg(),
                from_int::<R>(m).sub(from_int::<R>(-n)),
            );

            // from_int(m) - from_int(-n) = from_int(m) + from_int(-n).neg()
            R::axiom_sub_is_add_neg(from_int::<R>(m), from_int::<R>(-n));

            R::axiom_eqv_transitive(
                from_int::<R>(m + n),
                from_int::<R>(m).sub(from_int::<R>(-n)),
                from_int::<R>(m).add(from_int::<R>(-n).neg()),
            );

            // from_int(-n).neg() ≡ from_int(n)
            lemma_from_int_neg::<R>(-n);
            assert(-(-n) == n);
            R::axiom_eqv_symmetric(from_int::<R>(n), from_int::<R>(-n).neg());

            additive_group_lemmas::lemma_add_congruence_right::<R>(
                from_int::<R>(m),
                from_int::<R>(-n).neg(),
                from_int::<R>(n),
            );

            R::axiom_eqv_transitive(
                from_int::<R>(m + n),
                from_int::<R>(m).add(from_int::<R>(-n).neg()),
                from_int::<R>(m).add(from_int::<R>(n)),
            );
        }
    } else {
        // m < 0, n >= 0: use commutativity
        assert(m + n == n + m);
        lemma_from_int_add::<R>(n, m);
        R::axiom_add_commutative(from_int::<R>(n), from_int::<R>(m));
        R::axiom_eqv_transitive(
            from_int::<R>(m + n),
            from_int::<R>(n).add(from_int::<R>(m)),
            from_int::<R>(m).add(from_int::<R>(n)),
        );
    }
}

/// Helper: nat_mul(n, 1) * nat_mul(m, 1) ≡ nat_mul(n*m, 1).
proof fn lemma_nat_mul_mul_one<R: Ring>(n: nat, m: nat)
    ensures
        nat_mul::<R>(n, R::one()).mul(nat_mul::<R>(m, R::one())).eqv(nat_mul::<R>((n * m) as nat, R::one())),
    decreases n,
{
    if n == 0 {
        // 0 * nat_mul(m, 1) ≡ 0 = nat_mul(0, 1)
        ring_lemmas::lemma_mul_zero_left::<R>(nat_mul::<R>(m, R::one()));
    } else {
        let nm1: nat = (n - 1) as nat;
        // IH: nat_mul(n-1, 1) * nat_mul(m, 1) ≡ nat_mul((n-1)*m, 1)
        lemma_nat_mul_mul_one::<R>(nm1, m);

        // nat_mul(n, 1) = 1 + nat_mul(n-1, 1) [definitional]
        // (1 + nat_mul(n-1,1)) * nat_mul(m,1) ≡ 1*nat_mul(m,1) + nat_mul(n-1,1)*nat_mul(m,1)
        ring_lemmas::lemma_mul_distributes_right::<R>(
            R::one(), nat_mul::<R>(nm1, R::one()), nat_mul::<R>(m, R::one()),
        );

        // 1*nat_mul(m,1) ≡ nat_mul(m,1)
        ring_lemmas::lemma_mul_one_left::<R>(nat_mul::<R>(m, R::one()));

        // Combine: 1*nat_mul(m,1) + nat_mul(n-1,1)*nat_mul(m,1)
        //        ≡ nat_mul(m,1) + nat_mul((n-1)*m, 1)
        additive_group_lemmas::lemma_add_congruence::<R>(
            R::one().mul(nat_mul::<R>(m, R::one())), nat_mul::<R>(m, R::one()),
            nat_mul::<R>(nm1, R::one()).mul(nat_mul::<R>(m, R::one())), nat_mul::<R>((nm1 * m) as nat, R::one()),
        );

        R::axiom_eqv_transitive(
            nat_mul::<R>(n, R::one()).mul(nat_mul::<R>(m, R::one())),
            R::one().mul(nat_mul::<R>(m, R::one())).add(nat_mul::<R>(nm1, R::one()).mul(nat_mul::<R>(m, R::one()))),
            nat_mul::<R>(m, R::one()).add(nat_mul::<R>((nm1 * m) as nat, R::one())),
        );

        // nat_mul(m, 1) + nat_mul((n-1)*m, 1) ≡ nat_mul(m + (n-1)*m, 1)
        lemma_nat_mul_add::<R>(m, (nm1 * m) as nat, R::one());
        R::axiom_eqv_symmetric(
            nat_mul::<R>(m + (nm1 * m) as nat, R::one()),
            nat_mul::<R>(m, R::one()).add(nat_mul::<R>((nm1 * m) as nat, R::one())),
        );

        // m + (n-1)*m = n*m
        assert(m + nm1 * m == n * m) by (nonlinear_arith)
            requires n > 0, nm1 == n - 1;

        R::axiom_eqv_transitive(
            nat_mul::<R>(n, R::one()).mul(nat_mul::<R>(m, R::one())),
            nat_mul::<R>(m, R::one()).add(nat_mul::<R>((nm1 * m) as nat, R::one())),
            nat_mul::<R>((n * m) as nat, R::one()),
        );
    }
}

/// from_int(m * n) ≡ from_int(m) * from_int(n).
pub proof fn lemma_from_int_mul<R: Ring>(m: int, n: int)
    ensures
        from_int::<R>(m * n).eqv(from_int::<R>(m).mul(from_int::<R>(n))),
    decreases (if m < 0 { 2int } else if n < 0 { 1int } else { 0int }),
{
    if m >= 0 && n >= 0 {
        if m == 0 {
            // 0 * n = 0
            assert(0int * n == 0int);
            // from_int(0) * from_int(n) = 0 * from_int(n) ≡ 0 = from_int(0)
            ring_lemmas::lemma_mul_zero_left::<R>(from_int::<R>(n));
            R::axiom_eqv_symmetric(R::zero().mul(from_int::<R>(n)), R::zero());
        } else if n == 0 {
            assert(m * 0int == 0int);
            R::axiom_mul_zero_right(from_int::<R>(m));
            R::axiom_eqv_symmetric(from_int::<R>(m).mul(R::zero()), R::zero());
        } else {
            // Both positive
            assert(m * n > 0) by (nonlinear_arith) requires m > 0, n > 0;
            assert((m * n) as nat == (m as nat) * (n as nat)) by (nonlinear_arith) requires m > 0, n > 0;
            lemma_nat_mul_mul_one::<R>(m as nat, n as nat);
            R::axiom_eqv_symmetric(
                nat_mul::<R>(m as nat, R::one()).mul(nat_mul::<R>(n as nat, R::one())),
                nat_mul::<R>((m * n) as nat, R::one()),
            );
        }
    } else if m >= 0 && n < 0 {
        // from_int(m) * from_int(n) ≡ from_int(m) * from_int(-n).neg()
        //   ≡ (from_int(m) * from_int(-n)).neg()
        //   ≡ from_int(m*(-n)).neg()
        //   = from_int(-(m*n)).neg()
        //   ≡ from_int(m*n)

        assert(m * (-n) == -(m * n)) by (nonlinear_arith);

        // from_int(n) ≡ from_int(-n).neg()
        lemma_from_int_neg::<R>(-n);
        assert(-(-n) == n);
        // gives: from_int(n).eqv(from_int(-n).neg())
        R::axiom_eqv_symmetric(from_int::<R>(n), from_int::<R>(-n).neg());
        // gives: from_int(-n).neg().eqv(from_int(n))

        // from_int(m) * from_int(n) ≡ from_int(m) * from_int(-n).neg()
        R::axiom_eqv_symmetric(from_int::<R>(-n).neg(), from_int::<R>(n));
        ring_lemmas::lemma_mul_congruence_right::<R>(
            from_int::<R>(m),
            from_int::<R>(n),
            from_int::<R>(-n).neg(),
        );

        // a * neg(b) ≡ neg(a * b)
        ring_lemmas::lemma_mul_neg_right::<R>(from_int::<R>(m), from_int::<R>(-n));

        R::axiom_eqv_transitive(
            from_int::<R>(m).mul(from_int::<R>(n)),
            from_int::<R>(m).mul(from_int::<R>(-n).neg()),
            from_int::<R>(m).mul(from_int::<R>(-n)).neg(),
        );

        // IH: from_int(m*(-n)) ≡ from_int(m) * from_int(-n)
        lemma_from_int_mul::<R>(m, -n);
        // gives: from_int(m*(-n)).eqv(from_int(m).mul(from_int(-n)))
        R::axiom_eqv_symmetric(
            from_int::<R>(m * (-n)),
            from_int::<R>(m).mul(from_int::<R>(-n)),
        );
        // gives: from_int(m).mul(from_int(-n)).eqv(from_int(m*(-n)))

        R::axiom_neg_congruence(
            from_int::<R>(m).mul(from_int::<R>(-n)),
            from_int::<R>(m * (-n)),
        );
        // gives: from_int(m).mul(from_int(-n)).neg().eqv(from_int(m*(-n)).neg())

        R::axiom_eqv_transitive(
            from_int::<R>(m).mul(from_int::<R>(n)),
            from_int::<R>(m).mul(from_int::<R>(-n)).neg(),
            from_int::<R>(m * (-n)).neg(),
        );

        // from_int(m*(-n)) = from_int(-(m*n))
        // from_int(-(m*n)).neg() ≡ from_int(m*n)
        lemma_from_int_neg::<R>(m * n);
        // gives: from_int(-(m*n)).eqv(from_int(m*n).neg())
        R::axiom_neg_congruence(from_int::<R>(-(m * n)), from_int::<R>(m * n).neg());
        additive_group_lemmas::lemma_neg_involution::<R>(from_int::<R>(m * n));
        R::axiom_eqv_transitive(
            from_int::<R>(-(m * n)).neg(),
            from_int::<R>(m * n).neg().neg(),
            from_int::<R>(m * n),
        );

        R::axiom_eqv_transitive(
            from_int::<R>(m).mul(from_int::<R>(n)),
            from_int::<R>(m * (-n)).neg(),
            from_int::<R>(m * n),
        );

        R::axiom_eqv_symmetric(
            from_int::<R>(m).mul(from_int::<R>(n)),
            from_int::<R>(m * n),
        );
    } else if m < 0 && n >= 0 {
        // Symmetric via commutativity
        assert(m * n == n * m) by (nonlinear_arith);
        lemma_from_int_mul::<R>(n, m);
        R::axiom_mul_commutative(from_int::<R>(n), from_int::<R>(m));
        R::axiom_eqv_transitive(
            from_int::<R>(m * n),
            from_int::<R>(n).mul(from_int::<R>(m)),
            from_int::<R>(m).mul(from_int::<R>(n)),
        );
    } else {
        // Both negative: neg*neg = pos
        assert((-m) * (-n) == m * n) by (nonlinear_arith);

        // from_int(m) ≡ from_int(-m).neg()
        lemma_from_int_neg::<R>(-m);
        assert(-(-m) == m);
        R::axiom_eqv_symmetric(from_int::<R>(m), from_int::<R>(-m).neg());

        // from_int(n) ≡ from_int(-n).neg()
        lemma_from_int_neg::<R>(-n);
        assert(-(-n) == n);
        R::axiom_eqv_symmetric(from_int::<R>(n), from_int::<R>(-n).neg());

        // from_int(m)*from_int(n) ≡ from_int(-m).neg()*from_int(-n).neg()
        ring_lemmas::lemma_mul_congruence::<R>(
            from_int::<R>(m), from_int::<R>(-m).neg(),
            from_int::<R>(n), from_int::<R>(-n).neg(),
        );

        // neg(a)*neg(b) ≡ a*b
        ring_lemmas::lemma_neg_mul_neg::<R>(from_int::<R>(-m), from_int::<R>(-n));

        R::axiom_eqv_transitive(
            from_int::<R>(m).mul(from_int::<R>(n)),
            from_int::<R>(-m).neg().mul(from_int::<R>(-n).neg()),
            from_int::<R>(-m).mul(from_int::<R>(-n)),
        );

        // IH: from_int((-m)*(-n)) ≡ from_int(-m)*from_int(-n)
        lemma_from_int_mul::<R>(-m, -n);
        R::axiom_eqv_symmetric(
            from_int::<R>((-m) * (-n)),
            from_int::<R>(-m).mul(from_int::<R>(-n)),
        );

        R::axiom_eqv_transitive(
            from_int::<R>(m).mul(from_int::<R>(n)),
            from_int::<R>(-m).mul(from_int::<R>(-n)),
            from_int::<R>((-m) * (-n)),
        );

        // (-m)*(-n) == m*n
        R::axiom_eqv_symmetric(
            from_int::<R>(m).mul(from_int::<R>(n)),
            from_int::<R>(m * n),
        );
    }
}

/// Helper: from_int(n) ≥ 0 when n ≥ 0.
pub proof fn lemma_from_int_nonneg<R: OrderedRing>(n: int)
    requires
        n >= 0,
    ensures
        R::zero().le(from_int::<R>(n)),
{
    if n == 0 {
        R::axiom_le_reflexive(R::zero());
    } else {
        // from_int(n) = nat_mul(n, 1), n > 0
        // 0 < 1 → 0 ≤ 1
        ordered_ring_lemmas::lemma_zero_lt_one::<R>();
        R::axiom_lt_iff_le_and_not_eqv(R::zero(), R::one());
        lemma_nat_mul_nonneg::<R>(n as nat, R::one());
    }
}

/// Monotonicity: m ≤ n implies from_int(m).le(from_int(n)).
pub proof fn lemma_from_int_le_monotone<R: OrderedRing>(m: int, n: int)
    requires
        m <= n,
    ensures
        from_int::<R>(m).le(from_int::<R>(n)),
{
    // from_int(n) ≡ from_int(m) + from_int(n-m)
    assert(n == m + (n - m));
    lemma_from_int_add::<R>(m, n - m);
    // gives: from_int(n).eqv(from_int(m).add(from_int(n-m)))

    // from_int(n-m) ≥ 0
    lemma_from_int_nonneg::<R>(n - m);

    // from_int(m) ≤ from_int(m) + from_int(n-m)
    // Use: 0 ≤ from_int(n-m) → from_int(m)+0 ≤ from_int(m)+from_int(n-m)
    R::axiom_le_add_monotone(R::zero(), from_int::<R>(n - m), from_int::<R>(m));
    // gives: 0+from_int(m) ≤ from_int(n-m)+from_int(m)

    // 0+from_int(m) ≡ from_int(m)
    additive_group_lemmas::lemma_add_zero_left::<R>(from_int::<R>(m));
    // from_int(n-m)+from_int(m) ≡ from_int(m)+from_int(n-m)
    R::axiom_add_commutative(from_int::<R>(n - m), from_int::<R>(m));

    R::axiom_eqv_reflexive(from_int::<R>(m));
    R::axiom_le_congruence(
        R::zero().add(from_int::<R>(m)),
        from_int::<R>(m),
        from_int::<R>(n - m).add(from_int::<R>(m)),
        from_int::<R>(m).add(from_int::<R>(n - m)),
    );
    // gives: from_int(m) ≤ from_int(m)+from_int(n-m)

    // from_int(m)+from_int(n-m) ≡ from_int(n)
    R::axiom_eqv_symmetric(
        from_int::<R>(n),
        from_int::<R>(m).add(from_int::<R>(n - m)),
    );
    // gives: from_int(m).add(from_int(n-m)).eqv(from_int(n))

    R::axiom_eqv_reflexive(from_int::<R>(m));
    R::axiom_le_congruence(
        from_int::<R>(m),
        from_int::<R>(m),
        from_int::<R>(m).add(from_int::<R>(n - m)),
        from_int::<R>(n),
    );
}

/// Nonzero embedding (OrderedRing): n ≠ 0 implies ¬from_int(n).eqv(zero()).
pub proof fn lemma_from_int_nonzero<R: OrderedRing>(n: int)
    requires
        n != 0int,
    ensures
        !from_int::<R>(n).eqv(R::zero()),
    decreases (if n < 0 { 1int } else { 0int }),
{
    if n > 0 {
        // 0 < 1
        ordered_ring_lemmas::lemma_zero_lt_one::<R>();

        // 1 ≤ n → from_int(1) ≤ from_int(n)
        lemma_from_int_le_monotone::<R>(1, n);

        // from_int(1) ≡ 1
        lemma_from_int_one::<R>();
        // gives: from_int(1).eqv(R::one())

        // 1 ≤ from_int(n) via le_congruence
        ordered_ring_lemmas::lemma_le_congruence_left::<R>(
            from_int::<R>(1int), R::one(), from_int::<R>(n),
        );

        // 0 < 1 ≤ from_int(n) → 0 < from_int(n)
        ordered_ring_lemmas::lemma_lt_le_transitive::<R>(R::zero(), R::one(), from_int::<R>(n));
        R::axiom_lt_iff_le_and_not_eqv(R::zero(), from_int::<R>(n));
        // !0.eqv(from_int(n)). Symmetric gives !from_int(n).eqv(0).
        R::axiom_eqv_symmetric(R::zero(), from_int::<R>(n));
    } else {
        // n < 0
        lemma_from_int_nonzero::<R>(-n);
        // from_int(-n) ≠ 0

        // from_int(n) ≡ from_int(-n).neg() [from from_int_neg(-n)]
        lemma_from_int_neg::<R>(-n);
        assert(-(-n) == n);
        // gives: from_int(n).eqv(from_int(-n).neg())

        // If from_int(n).eqv(0):
        // Then from_int(-n).neg().eqv(0) [by transitivity]
        // Then from_int(-n).eqv(0) [since neg(0) = 0]
        // Contradiction with from_int(-n) ≠ 0
        if from_int::<R>(n).eqv(R::zero()) {
            R::axiom_eqv_symmetric(from_int::<R>(n), from_int::<R>(-n).neg());
            R::axiom_eqv_transitive(
                from_int::<R>(-n).neg(),
                from_int::<R>(n),
                R::zero(),
            );
            // from_int(-n).neg().eqv(0)
            // neg(0) ≡ 0, so 0 ≡ neg(0)
            additive_group_lemmas::lemma_neg_zero::<R>();
            R::axiom_eqv_symmetric(R::zero().neg(), R::zero());
            // 0.eqv(0.neg())
            R::axiom_eqv_transitive(
                from_int::<R>(-n).neg(),
                R::zero(),
                R::zero().neg(),
            );
            // from_int(-n).neg() ≡ 0.neg()
            // Apply neg_congruence (on the neg'd values) to get from_int(-n) ≡ 0
            // neg(neg(x)) ≡ x, neg(neg(0)) ≡ 0
            additive_group_lemmas::lemma_neg_involution::<R>(from_int::<R>(-n));
            // gives: from_int(-n).neg().neg().eqv(from_int(-n))
            R::axiom_eqv_symmetric(from_int::<R>(-n).neg().neg(), from_int::<R>(-n));
            // gives: from_int(-n).eqv(from_int(-n).neg().neg())

            additive_group_lemmas::lemma_neg_involution::<R>(R::zero());
            // gives: R::zero().neg().neg().eqv(R::zero())

            R::axiom_neg_congruence(from_int::<R>(-n).neg(), R::zero().neg());
            // gives: from_int(-n).neg().neg().eqv(0.neg().neg())
            R::axiom_eqv_transitive(
                from_int::<R>(-n),
                from_int::<R>(-n).neg().neg(),
                R::zero().neg().neg(),
            );
            R::axiom_eqv_transitive(
                from_int::<R>(-n),
                R::zero().neg().neg(),
                R::zero(),
            );
            // from_int(-n).eqv(0) — contradiction!
        }
    }
}

} // verus!
