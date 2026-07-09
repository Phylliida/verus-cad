"""Generate a synthetic agglutinative SOV language with ground truth.

Used to validate the xenolang toolkit: we know every token's part of
speech and morpheme segmentation, so we can score what the tools
recover. Design: ergative-absolutive case marking, suffixing
morphology, SOV order, optional topic particle, Zipfian lexicon.

Outputs (in --outdir):
  corpus.txt          one sentence per line, space-separated
  corpus_nospace.txt  same sentences with spaces removed (segmenter test)
  gold.json           surface form -> {pos, stem, suffixes}
"""

import argparse
import json
import os
import random

CONS = "ptkmnsrlvz"
VOWELS = "aeiou"
CODAS = "nsr"


def make_stem(rng, syllables, used):
    while True:
        s = ""
        for _ in range(syllables):
            s += rng.choice(CONS) + rng.choice(VOWELS)
            if rng.random() < 0.2:
                s += rng.choice(CODAS)
        if s not in used and len(s) >= 2:
            used.add(s)
            return s


def zipf_weights(n):
    return [1.0 / (i + 1) for i in range(n)]


class Lang:
    # gold morphology
    CASES = {"erg": "ka", "dat": "mu", "loc": "su"}   # absolutive is unmarked
    PLURAL = "ne"
    TENSES = {"past": "ro", "npst": "hi"}
    EVID = "ku"

    def __init__(self, seed=7):
        rng = random.Random(seed)
        used = set()
        self.rng = rng
        self.gold = {}

        def forms_of(stem, kind):
            if kind == "noun":
                out = set()
                for pl in ("", self.PLURAL):
                    for case in ("", *self.CASES.values()):
                        out.add(stem + pl + case)
                return out
            if kind == "verb":
                return {stem + t + e for t in self.TENSES.values()
                        for e in ("", self.EVID)}
            return {stem}

        # Rejection-sample stems so no two surface forms ever collide.
        surfaces = set()

        def add_stems(n, syllables_fn, kind):
            stems = []
            while len(stems) < n:
                st = make_stem(rng, syllables_fn(), used)
                fs = forms_of(st, kind)
                if surfaces.isdisjoint(fs):
                    surfaces.update(fs)
                    stems.append(st)
                else:
                    used.discard(st)
            return stems

        self.nouns = add_stems(60, lambda: rng.choice([2, 2, 3]), "noun")
        self.verbs = add_stems(30, lambda: rng.choice([2, 2, 3]), "verb")
        self.adjs = add_stems(15, lambda: 2, "other")
        self.nums = add_stems(8, lambda: rng.choice([1, 2]), "other")
        self.temporals = add_stems(6, lambda: 2, "other")
        self.names = add_stems(12, lambda: 3, "noun")  # names take case too
        self.dem = add_stems(1, lambda: 1, "other")[0]    # demonstrative
        self.topic = add_stems(1, lambda: 1, "other")[0]  # topic particle
        self.neg = add_stems(1, lambda: 1, "other")[0]    # negation particle

    def _emit(self, surface, pos, stem, suffixes):
        prev = self.gold.get(surface)
        entry = {"pos": pos, "stem": stem, "suffixes": suffixes}
        # a surface form should never be ambiguous in this toy language
        assert prev is None or prev == entry, f"ambiguous surface form {surface}"
        self.gold[surface] = entry
        return surface

    def noun_form(self, stem, case, plural, pos="NOUN"):
        sufs = []
        s = stem
        if plural:
            s += self.PLURAL
            sufs.append(self.PLURAL)
        if case != "abs":
            s += self.CASES[case]
            sufs.append(self.CASES[case])
        return self._emit(s, pos, stem, sufs)

    def verb_form(self, stem, tense, evid):
        sufs = [self.TENSES[tense]]
        s = stem + self.TENSES[tense]
        if evid:
            s += self.EVID
            sufs.append(self.EVID)
        return self._emit(s, "VERB", stem, sufs)

    def np(self, case, allow_name=True):
        rng = self.rng
        toks = []
        if allow_name and rng.random() < 0.12:
            name = rng.choices(self.names, zipf_weights(len(self.names)))[0]
            toks.append(self.noun_form(name, case, plural=False, pos="NAME"))
            return toks
        if rng.random() < 0.15:
            toks.append(self._emit(self.dem, "DEM", self.dem, []))
        if rng.random() < 0.20:
            num = rng.choices(self.nums, zipf_weights(len(self.nums)))[0]
            toks.append(self._emit(num, "NUM", num, []))
        if rng.random() < 0.30:
            adj = rng.choices(self.adjs, zipf_weights(len(self.adjs)))[0]
            toks.append(self._emit(adj, "ADJ", adj, []))
        noun = rng.choices(self.nouns, zipf_weights(len(self.nouns)))[0]
        plural = rng.random() < 0.25
        toks.append(self.noun_form(noun, case, plural))
        return toks

    def sentence(self):
        rng = self.rng
        toks = []
        if rng.random() < 0.20:
            t = rng.choices(self.temporals, zipf_weights(len(self.temporals)))[0]
            toks.append(self._emit(t, "TEMP", t, []))
        transitive = rng.random() < 0.7
        subj_case = "erg" if transitive else "abs"
        toks += self.np(subj_case)
        if rng.random() < 0.30:
            toks.append(self._emit(self.topic, "PART", self.topic, []))
        if rng.random() < 0.20:
            toks += self.np(rng.choice(["loc", "dat"]), allow_name=False)
        if transitive:
            toks += self.np("abs", allow_name=False)
        if rng.random() < 0.12:
            toks.append(self._emit(self.neg, "PART", self.neg, []))
        verb = rng.choices(self.verbs, zipf_weights(len(self.verbs)))[0]
        tense = "past" if rng.random() < 0.55 else "npst"
        toks.append(self.verb_form(verb, tense, evid=rng.random() < 0.25))
        return toks


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", "--sentences", type=int, default=3000)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("-o", "--outdir", default="testdata")
    args = ap.parse_args()

    lang = Lang(seed=args.seed)
    sents = [lang.sentence() for _ in range(args.sentences)]

    os.makedirs(args.outdir, exist_ok=True)
    with open(os.path.join(args.outdir, "corpus.txt"), "w", encoding="utf-8") as f:
        for s in sents:
            f.write(" ".join(s) + "\n")
    with open(os.path.join(args.outdir, "corpus_nospace.txt"), "w", encoding="utf-8") as f:
        for s in sents:
            f.write("".join(s) + "\n")
    gold = {
        "lexicon": lang.gold,
        "true_suffixes": sorted({*Lang.CASES.values(), Lang.PLURAL,
                                 *Lang.TENSES.values(), Lang.EVID}),
        "order": "SOV, ergative-absolutive, suffixing",
    }
    with open(os.path.join(args.outdir, "gold.json"), "w", encoding="utf-8") as f:
        json.dump(gold, f, indent=1, ensure_ascii=False)

    n_tok = sum(len(s) for s in sents)
    print(f"wrote {len(sents)} sentences, {n_tok} tokens, "
          f"{len(lang.gold)} surface types to {args.outdir}/")


if __name__ == "__main__":
    main()
