"""CLI: python -m xenolang <command> corpus.txt [options]"""

import argparse
import json
import sys

from . import corpus as corpus_mod
from . import stats as stats_mod
from . import segment as segment_mod
from . import morph as morph_mod
from . import cluster as cluster_mod
from . import typology as typology_mod
from . import report as report_mod


def main(argv=None):
    p = argparse.ArgumentParser(prog="xenolang",
                                description="Decipherment toolkit for unknown languages")
    sub = p.add_subparsers(dest="cmd", required=True)

    def add_common(sp):
        sp.add_argument("corpus", help="text file, one sentence per line")
        sp.add_argument("--lowercase", action="store_true")

    sp = sub.add_parser("report", help="run the full pipeline, write report.md + JSON artifacts")
    add_common(sp)
    sp.add_argument("-o", "--outdir", default="analysis")
    sp.add_argument("-k", "--clusters", type=int, default=20)
    sp.add_argument("--segment", choices=["auto", "yes", "no"], default="auto",
                    help="run character segmentation first (auto: only if no whitespace)")

    sp = sub.add_parser("stats", help="language-likeness statistics")
    add_common(sp)

    sp = sub.add_parser("segment", help="induce word boundaries, print segmented text")
    add_common(sp)

    sp = sub.add_parser("morph", help="affixes and paradigm signatures (JSON)")
    add_common(sp)

    sp = sub.add_parser("cluster", help="distributional word classes (JSON)")
    add_common(sp)
    sp.add_argument("-k", "--clusters", type=int, default=20)

    args = p.parse_args(argv)

    if args.cmd == "report":
        path = report_mod.build_report(args.corpus, args.outdir, k=args.clusters,
                                       segment_mode=args.segment,
                                       lowercase=args.lowercase)
        print(f"report written to {path}")
        return 0

    if args.cmd == "segment":
        with open(args.corpus, encoding="utf-8") as f:
            lines = [l.strip().replace(" ", "") for l in f if l.strip()]
        res = segment_mod.run(lines)
        for toks in res["segmented"]:
            print(" ".join(toks))
        print(f"# threshold={res['threshold']:.2f} lexicon={res['lexicon_size']} "
              f"mean_word_len={res['mean_word_length']:.2f}", file=sys.stderr)
        return 0

    corp = corpus_mod.load(args.corpus, lowercase=args.lowercase)

    if args.cmd == "stats":
        res = stats_mod.run(corp)
        for name, status, comment in res["verdicts"]:
            print(f"[{status:4s}] {name}: {comment}")
        print(json.dumps({k: v for k, v in res.items() if k != "verdicts"},
                         indent=1, ensure_ascii=False, default=str))
    elif args.cmd == "morph":
        print(json.dumps(morph_mod.run(corp.type_counts()), indent=1, ensure_ascii=False))
    elif args.cmd == "cluster":
        res = cluster_mod.run(corp, k=args.clusters)
        out = {"clusters": res["clusters"], "substitution_grid": res["substitution_grid"]}
        print(json.dumps(out, indent=1, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
