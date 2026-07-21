"""anyk-02 endgame: build the K=2 static closure CNF as DIMACS.

Reuses cube_conquer3.build_cnf verbatim (Synth at the 4^3 box + the full
checkpointed pattern library + point-blocks + full-48 lex leaders) under
ARENA_K=2 — the cubic box makes full lex sound. UNSAT ⟹ the K=2 search is
closed: every balanced pattern-avoiding 4^3-tiler is one of the point-blocked
decorations (each separately refuted as a non-space-tiler in anyk-01).
SAT ⟹ a new candidate the CEGIS missed (feed back to the verifier).

Formal note for anyk-03: the point-blocks enter the closure statement, so
the K=2 Lean port needs the 8 point refutation certs (untileable5/8)
alongside the pattern certs.

Run:  ARENA_K=2 ./runpy.sh mine_k2_static.py    # writes k2_static.cnf
then: cadical k2_static.cnf                     # 10=SAT / 20=UNSAT
"""
import os

assert os.environ.get("ARENA_K") == "2", "run with ARENA_K=2"

from cube_conquer3 import build_cnf

cnf, nv, npat = build_cnf()
with open("k2_static.cnf", "w") as f:
    f.write(f"p cnf {nv} {len(cnf)}\n")
    for cl in cnf:
        f.write(" ".join(map(str, cl)) + " 0\n")
print(f"wrote k2_static.cnf: {nv} vars, {len(cnf)} clauses, "
      f"{npat} patterns", flush=True)
