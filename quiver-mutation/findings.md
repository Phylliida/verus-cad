# Probe 6 findings — kernel vector & freeze test (Danielle's directions 1–2)

2026-07-04. Tests of the rank-5 leaky gadgets. Tags: **[lab]** computational.

## Direction 1 — rank-5 kernel vector is a dynamical companion

For 5×5 skew `B`, `Pf(B)=0`; the kernel is spanned by `v_i = (−1)^i Pf(B_î)`
(delete row/col i), and mutation `B↦EBEᵀ` carries `v ↦ E^{−T}v`.

- **Test:** is a gadget "secretly rank-4"? (`v` projectively fixed ⟹ dynamics on
  the rank-4 quotient `B|_{ℤ⁵/⟨v⟩}` ⟹ import rank-4 freezing.)
- **[lab] Result: `v` MOVES** — ~2450 distinct projective directions over 4000
  orbit steps, on all three families (leaky / decoupled / coupled). So the
  gadgets are **genuinely rank-5**, not degenerate; the negative ratchet searches
  are *not* a hidden rank-4 collapse. `probe6_kernel.py`.
- Integral invariants (`d₁,d₂`, elementary divisors; `d₁d₂` = rank-5 Pf analog)
  are 0 here — twin-hub is Pfaffian-degenerate, so SNF separates nothing.

## Direction 2 — freeze test (reversibility-corrected)

**Reversibility note:** `μ_k` is an involution, so `Δf ≥ 0` on every move ⟹
`Δf = 0` (the reverse move is also a move) ⟹ `f` is a true invariant. Hence a
one-sided "strict-on-fire" Lyapunov is **infeasible**. The correct content is:

> **ratchet-nonexistence ⟺ a separating invariant exists** (equality form).

(The directed fork/descent potential is a *separate* tool — it certifies
decidability, not ratchet-freeness.) So direction 2 becomes an invariant search.

**[lab] Freeze test** (`probe6b_freeze_test.py`): sample the orbit, find the
signed-monomial invariant ring, check if any invariant separates `T(5)`/`T(6)`.

| family | inv-dim deg≤2 | inv-dim deg≤3 | separates T(5)/T(6)? |
|---|---|---|---|
| twin-hub (rank-4 frozen, padded) | **138** | **1198** | no |
| leaky / decoupled / coupled | **1** | **1** | no |

- A *frozen/tame* family has a **rich** invariant ring (many conserved quantities
  ⟺ small orbit). The genuine rank-5 gadgets have **only constants** through
  degree 3 — orbits so spread that nothing low-degree is conserved. **This is the
  invariant-ring profile of a family that *could* host a machine**, and it rules
  out a cheap "secretly frozen" explanation for the search failures.

**Honest caveats:**
1. dim 1 is *consistent* with `T(5)~T(6)` (a counter) but does **not** prove it.
2. **Calibration limit:** the *known-frozen* twin-hub is also unseparated at
   degree ≤3 — its law is degree **4**. So degree ≤3 can't certify freezing
   either way; a clean rank-5 frozen-certificate needs the (expensive)
   degree-4-over-10-variables search.

## Net read

Both directions point the same way: the rank-5 gadgets are **genuinely rank-5**
and have a **trivial low-degree invariant ring** — the right profile for hosting a
machine, and no cheap obstruction found. Still not a proof of a counter (bounded
searches, degree ≤3), but the "they're secretly frozen/rank-4" explanations are
now ruled out.

**Next (from Danielle's list):** (3) piecewise-affine machine framing — freeze
small-entry control ⟹ affine register updates ⟹ induced PAM, reachability
undecidable in dim 2 (⚠️ Koiran–Cosnard–Garzon); (6) orbit-closure ideal
degree-by-degree — turn "dim 1 at deg ≤3" into a proof.

Files: `probe6_kernel.py`, `probe6b_freeze_test.py`.
