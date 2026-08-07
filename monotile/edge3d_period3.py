"""Which T=2 edge decorations needed period 3 (the (3,3,3) witnesses)?

Run:  ./runpy.sh edge3d_period3.py
"""
import json
import sys

sys.argv = ["corner3d.py"]
import corner3d as C3  # noqa: F401
import edge3d as E

recs = [json.loads(l) for l in open("edge3d_T2_results.jsonl")]
decs = E.census(2)
for r in sorted(recs, key=lambda r: r["i"]):
    if r["rule"] == "equal" and r.get("d") == [3, 3, 3]:
        dec = decs[r["i"]]
        marks = [E.EDGES[p] for p in range(12) if dec[p] == 1]
        print(f"#{r['i']}: {len(marks)} marks {marks}")
        # do we also find a (2,2,2) torus for it? (sanity: no, sweep order)
        show = E.show_table(dec)
        for d in ((2, 2, 2), (1, 2, 2), (2, 2, 4)):
            ok, _ = E.edge_sat(show, d, "equal", True, 50_000)
            print(f"    torus {d}: {'SAT' if ok else 'UNSAT' if ok is False else '?'}")
