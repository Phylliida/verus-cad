---
title: "K=2 — Lean port: no_aperiodic_wang_cube_k2 on the same trust base"
status: todo
claimed_by:
created: 2026-07-16T17:27:36Z
updated: 2026-07-16T17:27:36Z
---

## Description

Re-instantiate the formalization at K=2 (24 bits). The engines are already
K-generic — Coverage, BalanceLaw/Wiring, `faceDecomp_of_data`,
`cert_admitsPeriodic`, `sym_reduction`, P_inv shape, CubeCover — so this is a
data-layer rebuild, and doing it proves the pipeline is reusable machinery
rather than a one-off (which the eventual paper wants to claim).

Work items, mirroring the K=3 data layer:

1. Export under `ARENA_K=2`: the 24 rotation perms on Fin 24, rotation
   orbits, iface pair tables, base patterns (`arena_perm_fragment.txt`-style
   exporters already exist in `arena2.py`). Note the orbit structure differs
   from K=3 (no face-center bits at K=2 — expect corner-type orbits only);
   the balance/orbit wiring must follow the real export, not copy K=3's
   24/24/6 split.
2. Rebuild ConcreteArena/HgeoInstance analogues; rect torus certs for the
   K=2 pattern library (Python cert finder exists: `certs_all.json` flow);
   `genArenaCNF` for the K=2 closing box; lex block; encode-completeness
   (reuse the 4 proven clause-type probes); CubeCover tree from anyk-02's
   split tree.
3. Assemble `no_aperiodic_wang_cube_k2` + the period bound analogue.
4. State (and prove if cheap — it should be: block-copy of bits, tilings
   biject) the refinement-lifting lemma, so K=1 is formally covered by
   either K=2 or K=3 rather than by a remark.

Build discipline from the K=3 run: no `lake build` (rebuilds Mathlib);
`lake env lean <file>` with oleans written to
`.lake/build/lib/lean/LeanFlocq/` in dep order. Function-generate all large
data (literals don't elaborate). Separate `native_decide` facts into their
own theorems with raised heartbeats.

**Done when:** theorem compiles; `#print axioms` = kernel + `ofReduceBool`/
`trustCompiler` + the single per-cube-UNSAT external axiom, nothing else.

**Blocked by:** anyk-02 (needs the final pattern library + certs + tree).
