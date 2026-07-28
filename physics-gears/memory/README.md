# Memory — physics-gears / verus-physics2d

Dated, durable lessons from implementation sessions. Distinct from
DESIGN.md/SPEC-phase1.md (which track *what* and *why*); this folder tracks
*how* — proof-engineering knowledge that was expensive to learn and cheap
to re-read. Newest first.

| Date | File | One-liner |
|---|---|---|
| 2026-07-28 | [closed-eval-discipline.md](closed-eval-discipline.md) | Z3 won't evaluate closed rational chains for you; structural `*_closed_int` helpers + nlsat pins |
| 2026-07-28 | [mirror-proofs-and-perturbation.md](mirror-proofs-and-perturbation.md) | structural mirrors beat eqv mirrors; module perturbation breaks unrelated proofs; error caps hide root causes |
