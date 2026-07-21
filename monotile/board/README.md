# Task board — the any-K program

This directory is a simple task board (same conventions as
`tactus-bootstrap/board/`). **One markdown file = one task.** Add, claim, and
finish tasks just by creating and editing these `.md` files with your normal
file tools — no server, no JSON.

**The program:** the K=3 result (`anyk-00`) closed one point of the real
question. The goal of this board is the question itself:

> Does an aperiodic Wang cube — a single decoration whose 24-rotation orbit
> tiles ℤ³ but never periodically — exist at **any** K?

Either find one (constructive route: cards 06–11) or prove no K admits one
(obstruction route: card 12), with the small-K closures (01–05) as required
ground truth and evidence either way. Card 13 is the endgame reconciliation.

Useful background docs, all in `monotile/`: `RESULT.md` (the K=3 theorem +
trust base), `SCREW_STRUCTURE.md` (what the proof means), `NOTES_FOR_AGENT.md`
(MUS mining findings), `FOR_PROVER_AGENT.md` (self-contained briefing + the
original direction menu), `SAT_REFLECTION_STATUS.md` (Lean/SAT internals).

## File format

    ---
    title: short title of the task
    status: todo            # todo | in_progress | done
    claimed_by:            # your sibling id, or a name (optional)
    created: <iso8601>
    updated: <iso8601>
    ---

    ## Description
    what the task is / what "done" looks like

    ## Progress
    - (timestamp) a running log of what you tried / found

    ## Writeup
    (fill this in when done: findings, how the code works, and any assumptions
     you made — this is what the human reads to understand what happened)

## Workflow

- **Pick a task:** open a `status: todo` file, set `status: in_progress`, and put
  your id in `claimed_by`. Prefer a task nobody else has claimed.
- **Make a new task:** create `board/<slug>.md` with `status: todo`. Break big
  work into small, checkable tasks.
- **Log progress:** append to `## Progress` as you go.
- **Finish:** set `status: done` and fill in `## Writeup`. Be honest about
  what's partial or unverified.
- **Note:** `monotile/` is untracked in the top repo and must not be committed
  there (top-repo policy) — the board files are plain working files.

Files starting with `.` or `_`, plus this README, are ignored by the board.
