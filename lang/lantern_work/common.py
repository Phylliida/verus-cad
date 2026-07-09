"""Shared loaders for the lantern data."""

import csv
import os
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "lanterns")


def load_catalog():
    """flare_id -> dict of catalog fields (typed where useful)."""
    out = {}
    with open(os.path.join(DATA, "catalog.csv"), encoding="utf-8") as f:
        for row in csv.DictReader(f):
            row["n_flashes"] = int(row["n_flashes"])
            row["flare_len_s"] = float(row["flare_len_s"])
            # kept as string: mostly numeric, but dirty values exist (e.g. "6070/6068")
            row["beacon_id"] = row["beacon_id"].strip() or "0"
            row["since_dusk_s"] = float(row["since_dusk_s"]) if row["since_dusk_s"] else None
            row["shape_id"] = int(row["shape_id"]) if row["shape_id"] else None
            row["flourish"] = int(row["flourish"]) if row["flourish"] else None
            out[row["flare_id"]] = row
    return out


def load_gaps():
    """flare_id -> ordered list of dark gaps (floats, last-flash blank dropped)."""
    gaps = defaultdict(list)
    with open(os.path.join(DATA, "flares.csv"), encoding="utf-8") as f:
        for row in csv.DictReader(f):
            if row["dark_s"] != "":
                gaps[row["flare_id"]].append((int(row["flash_index"]), float(row["dark_s"])))
    return {fid: [g for _, g in sorted(v)] for fid, v in gaps.items()}


def lamp_timeline(catalog):
    """night -> list of flares sorted by since_dusk_s."""
    nights = defaultdict(list)
    for fid, c in catalog.items():
        if c["log"] == "LAMP" and c["since_dusk_s"] is not None:
            nights[c["night"]].append(c)
    for n in nights:
        nights[n].sort(key=lambda c: c["since_dusk_s"])
    return dict(nights)
