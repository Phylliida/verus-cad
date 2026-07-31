# Memory — physics-gears / verus-physics2d

Dated, durable lessons from implementation sessions. Distinct from
DESIGN.md/SPEC-phase1.md (which track *what* and *why*); this folder tracks
*how* — proof-engineering knowledge that was expensive to learn and cheap
to re-read. Newest first.

| Date | File | One-liner |
|---|---|---|
| 2026-07-29 | [certificate-design-lessons.md](certificate-design-lessons.md) | vacuous ∃-specs; bidirectional checker ensures; new_checked as convexity gate; abstract lemmas > closed eval; structural scene constants |
| 2026-07-28 | [module-checks-and-nla-opacity.md](module-checks-and-nla-opacity.md) | module checks trust dependency lemmas (full-crate green is the only green); NLA is spec-fn-opaque; eqv-chain call order |
| 2026-07-28 | [design-review-2026-07-28.md](design-review-2026-07-28.md) | two-round design review: ledger two-source bound (D9), canonicalize not normalize-on-write (D10), calc! not normalized specs (D11), local→global convexity (D12) |
| 2026-07-28 | [closed-eval-discipline.md](closed-eval-discipline.md) | Z3 won't evaluate closed rational chains for you; structural `*_closed_int` helpers + nlsat pins |
| 2026-07-28 | [mirror-proofs-and-perturbation.md](mirror-proofs-and-perturbation.md) | structural mirrors beat eqv mirrors; module perturbation breaks unrelated proofs; error caps hide root causes |
