# Prime Field: What Remains (110 verified, ~4 errors)

## Summary

All mathematical proofs are verified. All exec code compiles and passes overflow checks. The only remaining work is **connecting the verified chain lemma to the exec function's proof block** — purely mechanical wiring, no new math.

## The One Remaining Task

**File**: `verus-fixed-point/src/fixed_point/prime_field.rs`
**Function**: `mersenne_reduce_exec` (line ~750)
**Issue**: The final `proof { }` block has bare `assert` statements that aren't connected to the chain lemma.

### What needs to happen

Inside `mersenne_reduce_exec`'s proof block, call `lemma_reduce_chain` with the ghost values from the exec steps, then call `lemma_cond_sub` for the conditional subtract.

The chain lemma signature:
```rust
proof fn lemma_reduce_chain(
    lp: int, ci: int,
    prd: int, lov: int, hiv: int,        // product split values
    wlo: int, wt: int, wcy: int,          // wide fold values  
    f2-f8: int, c2-c8: int,               // fold values and carries
    fc: int,                               // final carry value
)
    requires [fold equations from exec postconditions]
    ensures (f8 + c8 * ci) as nat % p == prd as nat % p
```

### Steps to wire it up

1. **Establish vec_val connections** (already partially done, just needs scoping fix):
```rust
lemma_vec_val_split(product@, n as nat);
assert(sem_seq(lo@) =~= sem_seq(product@.subrange(0, n as int)));
assert(sem_seq(hi@) =~= sem_seq(product@.subrange(n as int, (2*n) as int)));
lemma_vec_val_pad(lo@, lo_pad@);
lemma_vec_val_split(wide@, n as nat);
assert(sem_seq(wide_lo@) =~= sem_seq(wide@.subrange(0, n as int)));
lemma_limb_power_add(1, n as nat);
reveal_with_fuel(limb_power, 2);
```

2. **Establish vec_val(wt_vec) = wide_top * c** (needs fundamental_div_mod):
```rust
assert(vec_val(wt_vec@) == wide_top as int * ci) by {
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        (wide_top as int * ci) as int, LIMB_BASE());
};
```

3. **Establish wide equation** (combines wide split + wide add):
```rust
assert(wlo + (wt + wcy * LIMB_BASE()) * lp == vec_val(lo@) + vec_val(hi@) * ci)
    by(nonlinear_arith) requires [4 equations from postconditions];
```

4. **Call chain lemma**:
```rust
lemma_reduce_chain(lp, ci,
    vec_val(product@), vec_val(lo@), vec_val(hi@),
    wlo, wt, wcy,
    vec_val(fold2@), cy2 as int,
    vec_val(fold3@), cy3 as int,
    ... all fold values ...
    vec_val(fold8@), _cy8 as int,
    final_c as int);
```

5. **Connect fold9 = fold8 + cy8*c** (since cy9 == 0):
```rust
assert(vec_val(fold9@) == vec_val(fold8@) + _cy8 as int * ci) by(nonlinear_arith)
    requires vec_val(fold9@) + cy9 as int * lp == vec_val(fold8@) + cy8_c as int,
        cy9 as int == 0, cy8_c as int == _cy8 as int * ci;
```

6. **Call conditional subtract lemma**:
```rust
lemma_vec_val_bounded(fold9@);
lemma_vec_val_bounded(d1@);
lemma_cond_sub(vec_val(fold9@), vec_val(d1@), p as int, lp, ci, bw1 as int);
```

### Why it's tricky

The carry folds are currently **inlined** into `mersenne_reduce_exec` (for chain visibility), making the function large. It has `#[verifier::rlimit(20)]` for extra budget. The proof block that connects everything needs to reference variables from BOTH the first fold (lo, hi, wide, etc.) and the carry fold rounds (fold3-fold9, cy3-cy9).

The main challenge is that `lemma_reduce_chain`'s preconditions reference `vec_val(fold3@)`, `vec_val(fold4@)`, etc. — all of which are exec variables from `generic_add_limbs` calls. The proof needs to establish that these match the chain lemma's requirements. Most of these are AUTOMATICALLY satisfied from `generic_add_limbs`'s postconditions, but Z3 needs the `vec_val` connections explicitly.

Additionally, `vec_val(wcy_vec@) == wide_cy * c * BASE` needs `pair_to_padded_vec`'s postcondition, and `vec_val(cy2_vec@) == cy2 * c` needs `scalar_to_padded_vec`'s postcondition. Both are already verified.

### The `mersenne_carry_folds` situation

There are TWO versions of the carry fold code:
1. **Split version**: `mersenne_carry_early` + `mersenne_carry_late` + `mersenne_carry_folds` wrapper — these are verified but have no modular postcondition.
2. **Inlined version**: the carry fold code is duplicated inside `mersenne_reduce_exec` to make all fold variables visible to the chain lemma.

The inlined version is what needs the proof. The split version can be kept for reference or removed after the inlined version works.

### What the chain lemma proves

`lemma_reduce_chain` proves:
```
(f8 + c8 * ci) as nat % ((lp - ci) as nat) == prd as nat % ((lp - ci) as nat)
```

Using step-by-step algebraic substitution:
1. f1 = product - (hi+c1+hct)*lp + hi*ci
2. f2 = f1 + hct*ci - c2*lp = product + (hi+wt)*ci - (hi+c1+hct+c2)*lp
3. ... (each step substitutes one fold equation)
4. f8 = product + A*ci - B*lp where A = hiv+wt+wcy*BASE+c2+...+c7, B = A+c8-hiv
5. A+c8 = hiv+B, so f8+c8*ci = product - (hiv+B)*(lp-ci) = product - K*p
6. Therefore (f8+c8*ci) % p == product % p

### What `mersenne_reduce_exec`'s postcondition needs

```rust
ensures
    out@.len() == n,
    valid_limbs(out@),
    vec_val(out@) as nat % ((limb_power(n as nat) - c as int) as nat)
        == vec_val(product@) as nat % ((limb_power(n as nat) - c as int) as nat),
    (vec_val(out@) as nat) < ((limb_power(n as nat) - c as int) as nat),
```

Once this is proved, `mul_mod`'s postcondition follows automatically (it just calls `mersenne_reduce_exec` + proves `gc == 0`).

## Architecture Overview

```
mul_mod
  └→ generic_mul_karatsuba (exact 2n product, gc==0)
  └→ mersenne_reduce_exec (2n → n limbs mod p)
       └→ split product: lo, hi
       └→ hi * c via generic_mul_by_limb
       └→ lo_pad + hi_c via generic_add_limbs (n+1 limbs)
       └→ split wide: wide_lo, wide_top
       └→ wide_top * c via mul2 + pair_to_padded_vec
       └→ fold2 = wide_lo + wt_vec via generic_add_limbs
       └→ [carry fold rounds: fold3-fold9 via scalar adds]
       └→ conditional subtract p
       └→ proof: lemma_reduce_chain + lemma_cond_sub

lemma_reduce_chain (VERIFIED)
  proves: (fold8 + cy8*c) % p == product % p
  method: step-by-step algebraic substitution of fold equations

lemma_cond_sub (VERIFIED)
  proves: conditional subtract gives val % p when val < 2*p

Helper lemmas (ALL VERIFIED):
  lemma_carry_le_1, lemma_scalar_carry_le_1, lemma_carry_mul_fits
  lemma_mersenne_int (int wrapper for pseudo_mersenne_reduce)
  pair_to_padded_vec, scalar_to_padded_vec, make_p_limbs
```

## Verified Function Counts

| Component | Verified | Status |
|-----------|----------|--------|
| SpecPrimeField Ring | 25 | Done |
| Mersenne reduction lemma | 2 | Done |
| Chain lemma | 1 | Done |
| Helper lemmas | 8 | Done |
| mersenne_carry_early | ~6 | Done |
| mersenne_carry_late | ~12 | Done |
| mersenne_carry_folds | 1 | Done |
| mersenne_reduce_exec | 0 | **2 asserts remaining** |
| add_mod | 1 | Done |
| neg_mod | 1 | Done |
| sub_mod | 1 | Done |
| mul_mod | 0 | **Cascades from reduce_exec** |
| make_p_limbs | 1 | Done |
| pair/scalar_to_padded_vec | 2 | Done |
| **Total** | **~110** | **~4 errors** |
