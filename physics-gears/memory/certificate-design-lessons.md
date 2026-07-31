# Certificate design lessons (2026-07-29, phys-05d)

Lessons from building check_contact_step + scene S4.

## 1. Watch out for vacuous spec disjuncts

The first C4 touching spec was `∃ ms: −tol_p ≤ ms ∧ ∀ edges: min_sep ≤ ms`
— looks like "penetration depth ≤ tol_p", but it's **always true** (take
ms = max(all values, −tol_p)). The bound must be a LOWER bound on the
max, not an upper bound on everything: the correct form is the
exists-edge-witness `∃ edge: min_sep(edge) ≥ −tol_p`. Read every
∃-spec twice for vacuity before proving toward it.

## 2. Checkers need bidirectional ensures

`ok ⟹ certified` alone is useless to scenes: `ok == true` is then
unprovable (the scene can't see inside the checker). The working shape
(mirror of step_free_flight's Some-guarantee): per-check exec fns with
`ok == spec_conjunct` EXACTLY, composed into
`ok == contact_checks_pass(...)`, plus `ok ⟹ certified` for the headline
claim. Exactness is achievable because every check is a decidable exact-
rational computation; the only subtle direction is C4's SAT result
(sep Some ⟺ ∃ witness, via min-attainment + min ≤ 0 contradiction).

## 3. new_checked is the convexity gate

The checker does NOT need a proven convexity-preservation theorem to
trust world polys: it computes world_verts_exec (exact transform) and
gates through ConvexPoly::new_checked (runtime invariant check, nlsat
pattern). The preservation lemma (proofs/world.rs) is still needed — but
only in the *proof* that new_checked returns Some, not in the checker's
trusted computing base. Generic and reusable: the rotation-cross identity
cross(Ru,Rv) ≡ (c²+s²)·cross(u,v) via cross bilinearity + vperp
identities (several of which are STRUCTURAL — D11's symmetry rule pays
off again).

## 4. Prefer abstract lemmas over closed eval in scenes

C3 for S4 fell out of `lemma_solve_row_c3` instantiated on the scene's
concrete values — zero closed evaluation. Closed eval is still needed for
the solver-side pins (λ == 1/2 structurally) and for C4's witnesses
(min_sep bounds per edge), but every claim that has an abstract lemma
behind it should go through it. Scene proof fns take the model values as
requires (lemma_s4_checks_pass has a long but mechanical requires list;
each pin is one assert at the call site).

## 5. Choose scene constants to keep dens structural

Side-2 squares (center (1,1), contact (2,1)) keep every anchor integral:
all closed forms stay `den == 0` and λ comes out STRUCTURALLY
`from_frac(1,2)`, making the final eq claims reflexive bridges. A side-1
square puts fracs in r_a/r_b, denominators explode combinatorially
(den = d1·d2 + d1 + d2 per op), and the scene claims become eqv-chains
instead of structural pins. Design scene geometry for the proof, not
just the physics.

## 6. rlimit: scene fns are Z3-context bombs

scene_s4 hit rlimit with ~35 asserts in one exec body. Split: exec scene
calls two proof fns (post-velocity facts; certificate-accepts) with
explicit requires lists. Also: `assert(c4_touch_witness(...))` existential
intro works by asserting the witness body, but bundle NO-witness proofs
into proof fns with forall-negation (proofs/cert.rs) — never inline them
in the exec fn.
