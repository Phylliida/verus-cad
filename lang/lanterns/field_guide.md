# 🏮 Field Guide

Two files, joined on **`flare_id`**. A *flare* is one lantern's blink-burst; a
*flash* is one blink inside it. All times are in **seconds**.

## `flares.csv` — the raw nightly log (one row per flash)

| column | meaning |
|--------|---------|
| `flare_id` | which flare this flash belongs to, `FLR-#####` (the join key) |
| `log` | `RIDGE` or `LAMP` — who recorded it |
| `flash_index` | 1, 2, 3… position of the flash within its flare |
| `dark_s` | seconds of darkness from this flash to the **next** one in the same flare; **blank on the last flash** of each flare |

A flare with *n* flashes has *n−1* dark gaps. The darkness is the whole message —
the flashes themselves all look the same.

## `catalog.csv` — our worked-out notes (one row per flare)

| column | meaning | filled in on |
|--------|---------|--------------|
| `flare_id` | the flare (join key) | every flare |
| `log` | `RIDGE` / `LAMP` | every flare |
| `n_flashes` | how many flashes the flare had | every flare |
| `flare_len_s` | how long the whole flare lasted (its overall **pace**) | every flare |
| `beacon_id` | which lantern blinked it. **`0` = we couldn't tell.** Numbers are **per-log** — RIDGE beacon 3 is *not* LAMP beacon 3 | every flare (often `0` on RIDGE) |
| `night` | which night's watch the flare belongs to, `N-###` | LAMP |
| `since_dusk_s` | how long after dusk the flare's first flash happened. **This is your turn-taking clock.** | LAMP |
| `glyph` | the letter we read the whole flare as (e.g. `5R3`, `1+1+3`, `*-SMUDGE`) | RIDGE |
| `shape_id` | which of the 18 underlying shapes (`0–17`) | LAMP |
| `flourish` | `1` if the flare had the extra little flash, else `0` | LAMP |
| `region` | which side of the valley, `R1` / `R2` | RIDGE |
| `cluster` | which group of beacons (a letter) | RIDGE |
| `cluster_num` | the group's number | RIDGE |
| `date_seen` | the night's date (mixed `dd/mm/yyyy` and `dd-mm-yyyy` — tidy it before parsing) | RIDGE |

### Notes from the watchers
- **The two logs don't overlap in what they know.** RIDGE has *glyphs + where in
  the valley*; LAMP has *who + exactly when*. Joining their strengths (step 4) is
  half the fun.
- **Glyphs are only on RIDGE.** LAMP flares are unlabeled — but they share the same
  18 shapes, so you can carry the labels across.
- **`*-SMUDGE` glyphs** are flares we logged as messy / couldn't read cleanly.
  Keep or toss them as you like — a few have odd zero-length or near-instant gaps.
- **`beacon_id = 0`** means "we couldn't tell which lantern," not "lantern #0."
- **Don't trust the row order** in `flares.csv` — flares got shuffled together when
  we typed up the logs. Re-order a night with `(night, since_dusk_s)`.
