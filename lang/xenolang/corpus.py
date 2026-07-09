"""Corpus loading and tokenization.

Expected input: UTF-8 text, one sentence per line. If the language
marks word boundaries, tokens are whitespace-separated. If not, use
segment.py first (the `report` command does this automatically).
"""

from collections import Counter
from dataclasses import dataclass, field

# Characters treated as detachable punctuation when they lead/trail a token.
PUNCT = set(".,;:!?\"'()[]{}«»…—–")

BOS = "<s>"
EOS = "</s>"


@dataclass
class Corpus:
    sentences: list = field(default_factory=list)  # list[list[str]]

    @property
    def tokens(self):
        for s in self.sentences:
            yield from s

    def token_count(self):
        return sum(len(s) for s in self.sentences)

    def type_counts(self) -> Counter:
        c = Counter()
        for s in self.sentences:
            c.update(s)
        return c

    def char_stream(self, sep=" "):
        """Characters of the corpus, tokens joined by `sep` within a sentence."""
        for s in self.sentences:
            yield sep.join(s)


def _split_token(tok, strip_punct):
    """Split detachable punctuation off a raw whitespace token."""
    if not strip_punct:
        return [tok]
    out = []
    lead = []
    while tok and tok[0] in PUNCT:
        lead.append(tok[0])
        tok = tok[1:]
    trail = []
    while tok and tok[-1] in PUNCT:
        trail.append(tok[-1])
        tok = tok[:-1]
    out.extend(lead)
    if tok:
        out.append(tok)
    out.extend(reversed(trail))
    return out


def load(path, lowercase=False, strip_punct=True, drop_punct_tokens=True):
    """Load a one-sentence-per-line corpus."""
    sentences = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if lowercase:
                line = line.lower()
            toks = []
            for raw in line.split():
                for t in _split_token(raw, strip_punct):
                    if drop_punct_tokens and all(ch in PUNCT for ch in t):
                        continue
                    toks.append(t)
            if toks:
                sentences.append(toks)
    return Corpus(sentences)


def whitespace_fraction(path, sample_lines=2000):
    """Fraction of nonempty lines containing internal whitespace.

    Used to auto-detect whether the corpus already marks word boundaries.
    """
    with_ws = 0
    total = 0
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            total += 1
            if any(ch.isspace() for ch in line):
                with_ws += 1
            if total >= sample_lines:
                break
    return (with_ws / total) if total else 0.0
