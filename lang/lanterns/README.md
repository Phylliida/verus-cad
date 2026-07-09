# 🏮 The Lantern Puzzle

Every night, the ghost-lanterns rise over the Hollow Valley.

No one carries them and no one lights them — they are pale, drifting spirits,
sentient little lights that float up out of the dark on their own and hang among
the hills. Each one flutters a quick flurry of blinks and goes still. And they are
plainly *answering each other*: watch long enough and you'll see one lantern blink,
and another blink back across the valley. They're talking. Nobody knows what about.

The strange part: the blinks themselves are all alike — the *pattern*, if there is
one, lives in the **lengths of darkness between them**.

A handful of us have spent years out on the hills writing down every flicker we
could catch. We've gotten pretty far! We worked out the **alphabet** — the flares
fall into a neat set of repeating shapes, and we can even tell you the little
"dials" each flare is built from. But after all this time we still have **no idea
what the lanterns are actually saying.**

That's the puzzle. **Can you read the lanterns?**

---

## What's in the box

| file | what it is |
|------|------------|
| `flares.csv` | the raw nightly log — one row per flash, just the timing |
| `catalog.csv` | everything *we* worked out, one row per flare |
| `field_guide.md` | what every column means |
| `manifest.json` | counts + stamps (so you know your copy is whole) |

Join the two files on `flare_id`. `flares.csv` is what the valley actually does;
`catalog.csv` is our homework. **We're giving you the homework** — start from
where we got stuck, not from scratch.

### Two logs, two kinds of clue
- **RIDGE** — watchers up on the far ridge. They see *lots* of lanterns at once
  but usually can't tell which lantern is which. What they *can* tell you is which
  **region** of the valley and which **cluster** a lantern drifted in — and they've
  tagged each flare with its **glyph**.
- **LAMP** — for a little while, a few of us managed to sit right beside a single
  lantern with a tiny clockwork recorder. Those entries know *exactly* which
  **beacon** blinked, and *exactly* how long after dusk. That's where you can watch
  lanterns **answer each other.**

The two logs are deliberately lopsided: RIDGE knows *where/what*, LAMP knows
*who/when*. You'll want both.

---

## What we already worked out (your headstart)

You are **not** staring at raw flashes:

1. **There's a finite alphabet.** Flares aren't random — they land on **35
   repeating glyphs**, built on **18 underlying shapes**. This is a real little
   writing system, not idle flicker.
2. **Each flare is built from a few dials**, which mix freely:
   - the **shape** (which of the 18 skeletons),
   - the **length** (slow or quick overall — `flare_len_s`),
   - a gentle **drift** (the rhythm eases faster or slower as the flare goes on),
   - an optional **flourish** (`flourish` — one extra flash, there or not).
   We can even *make up* believable new flares from these dials. We just can't
   *read* them.
3. **A map of the valley.** Two **regions** (R1, R2), split into **clusters**,
   down to single **beacons**.
4. **A timeline.** On the LAMP log, `beacon_id` + `since_dusk_s` + `night` let you
   put a night's flares back in the order they happened.

The alphabet: **done.** The meaning: **wide open.** That's the wall.

---

## Where to start

```
0 · Check        make sure your flares.csv / catalog.csv match manifest.json
1 · Alphabet     confirm the 35 glyphs / 18 shapes for yourself; play with the dials
2 · Take turns   on the LAMP log, sort by (night, since_dusk_s) and watch beacons
                 trade flares back and forth — who starts, who answers, how fast
3 · Who & where  which glyphs go with which region / cluster / beacon?
                 (hunt for a glyph that one beacon keeps repeating — almost like a name)
4 · Bridge       carry RIDGE's glyph labels over onto LAMP's unlabeled flares,
                 using the shapes they share
5 · ✦ Meaning ✦  work out what the lanterns are *saying*. Nobody's done it.
                 If you work it out, you'll feel it — the valley will start to make sense.
```

Steps 0–4 are all doable with what's in this box. Step 5 is the real prize, and
it's still out there.

Happy reading — and bring a thermos; the spirits keep late hours. 🔦
