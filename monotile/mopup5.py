"""Final mop-up: box-5 (then box-6) pass over every STALL in the campaign
checkpoint. Appends resolved verdicts to classify3d_all.jsonl so the
checkpoint becomes the complete classification of the canonical census.

Run:  ./runpy.sh mopup5.py
"""
import json
import time

from arena2 import box_sat

canonical = json.load(open("anyk3d_canonical.json"))["canonical"]
census = json.load(open("faceeq3d_census.json"))
T2E = {}
for key, ei in census["triple_to_eq"].items():
    ax, o1, o2 = map(int, key.split(","))
    T2E[(ax, o1, o2)] = ei

stalls = []
for line in open("classify3d_all.jsonl"):
    r = json.loads(line)
    if r["verdict"] == "STALL":
        stalls.append(r["i"])
stalls = sorted(set(stalls))
print(f"bench: {len(stalls)} stalls", flush=True)

out = open("classify3d_all.jsonl", "a")
survivors = []
for ci in stalls:
    held = set(canonical[ci])
    bad = [[], [], []]
    for ax in range(3):
        for o1 in range(24):
            for o2 in range(24):
                if T2E[(ax, o1, o2)] not in held:
                    bad[ax].append((o1, o2))
    t0 = time.time()
    sb, _ = box_sat((5, 5, 5), bad, conf_budget=10_000_000)
    verdict = "empty5" if sb is False else None
    if verdict is None:
        sb6, _ = box_sat((6, 6, 6), bad, conf_budget=20_000_000)
        verdict = "empty6" if sb6 is False else "DEEP-SURVIVOR"
    print(f"  canon {ci}: {verdict} [{time.time() - t0:.0f}s]", flush=True)
    out.write(json.dumps({"i": ci, "verdict": verdict}) + "\n")
    out.flush()
    if verdict == "DEEP-SURVIVOR":
        survivors.append(ci)
print(f"MOPUP DONE: {len(stalls) - len(survivors)} killed, "
      f"survivors: {survivors}", flush=True)
