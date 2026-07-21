# Can a single bumpy cube tile space without ever repeating?

*A plain-language guide to what this project proved, for readers with
everyday maths and no tiling theory. (For the technical versions see
RESULT.md, RESULTS-2d-anyk.md, and DESIGN-anyk-lean.md.)*

---

## 1. The question

Think of bathroom tiles. Square tiles cover a wall in an obvious way: the
pattern repeats, like wallpaper. Shift the whole wall one tile over and it
looks exactly the same. Patterns like that are called **periodic**.

Now ask a stranger question: is there a single tile shape that *can* cover
the whole plane — no gaps, no overlaps — but only in ways that **never
repeat**? Not "can be laid irregularly if you feel like it" (lots of
shapes allow both), but a shape where repetition is *impossible*: every
valid way of laying it goes on forever without the wallpaper property.

Such a shape is called an **aperiodic monotile**, nicknamed an
**einstein** (German *ein Stein*, "one stone" — the pun is the point, not
the physicist). For fifty years nobody knew whether one existed. In 2023
it was famously found for the flat plane: the "hat" tile. That was
front-page mathematics news.

**In three dimensions — filling space with copies of one solid shape —
the question is still open.** That's the mountain this project climbs one
particular face of.

## 2. Our tiles: cubes with bumps and dents

Arbitrary 3D shapes are hard to search. So we study a natural, precise
family — think LEGO or jigsaw pieces:

Take a cube. On each of its 6 faces, draw a K×K grid (K = 1, 2, 3, …).
In each grid cell put either a **bump** or a **dent**. Two cubes may sit
next to each other only if their touching faces *fit*: every bump meets a
dent and every dent meets a bump, like jigsaw pieces clicking together.

You get **one** cube design and unlimited copies of it, and you may
**rotate** copies (a cube has 24 rotations). No mirror images. The
question becomes:

> Is there a bump-pattern such that copies of that one cube fill all of
> space — but never in a repeating pattern?

Each K gives a finite (huge) family: at K=3 a cube has 54 grid cells, so
2⁵⁴ ≈ 18 quadrillion designs. And there are infinitely many K's.

## 3. What was already known (the K=3 theorem)

Earlier this project settled K=3 (3×3 bumps per face): **no such cube
exists**. Every K=3 bump-cube that fills space at all can also fill it
periodically. That took months: a search program swept the quadrillions of
designs using a SAT solver (a program that exhaustively checks logical
puzzles), and the result was then *machine-checked* (more on what that
means in §7).

But K=3 says nothing about K=4, or K=100. Each K is a separate infinite…
no — each K is a separate *finite but enormous* search, and there are
infinitely many K's. You cannot sweep them one by one forever. A new idea
was needed to ask the question **for all K at once**.

## 4. The key idea: the bumps don't matter — the rulebook does

Here is the insight the whole "any K" result stands on.

When you lay cubes next to each other, all that matters about a
neighbouring pair is: **do their touching faces fit?** Once you fix the
cube design, you can sit down (or make a computer sit down) and write out
a *rulebook*: for each of the 24 rotations placed on the left and each of
the 24 on the right, "allowed" or "not allowed". Same for up/down and
front/behind.

Once the rulebook is written, **the bumps have done their entire job.**
Whether space can be filled, and whether it can be filled without
repeating, depends only on the rulebook — laying cubes is exactly the
game of assigning one of 24 rotations to every position in a 3D grid so
that all neighbour pairs are "allowed".

So the infinite question "is there an aperiodic cube at *some* K?"
becomes: "is there an *achievable rulebook* whose game can be played
forever but never periodically?"

And now the miracle: **only finitely many rulebooks are achievable, no
matter how large K gets.** Why? Whether two faces fit turns out to be
governed by simple *relations between the six face patterns* — statements
like "face A is the mirror-image negative of face B". There are exactly
**84** such elementary relations for a cube, and a rulebook is determined
by which of the 84 hold. Making K bigger gives you finer bumps but no new
*kinds* of relation — the alphabet of possible rulebooks saturates. A
careful count (using the algebra of how relations chain together —
if A is locked to B and B to C, then A is forced into a relation with C)
shows exactly **1,445,865 rulebooks** can ever arise, across every K from
one to infinity.

Infinitely many cube families, collapsed into 1.4 million finite
questions. Each one small enough for a computer to answer.

## 5. The answers

Each rulebook was put through two tests:

* Can its game be played at all? (If even a small box can't be filled,
  the answer is no — and "no" means that rulebook can never produce a
  space-filling cube, so it's harmless.)
* If it can be played, does it admit a *repeating* solution? (The
  computer looks for a small repeating block — like finding the wallpaper
  unit.)

Results, checked for all 1,445,865 (organised into 66,134 truly-distinct
classes once rotations of the whole setup are accounted for):

* **56,771 classes can't fill space at all** (every one already fails in
  a box of size 6×6×6 or smaller);
* **9,363 classes fill space and always admit a repeating pattern**
  (a repeating block of at most 64 cubes — most far smaller);
* **0 classes fill space only aperiodically.**

That last line is the result:

> **No cube with bump-and-dent faces — at any resolution K, forever — is
> an einstein. Anything that tiles, also tiles periodically.**

The same method was run first in two dimensions (a square with K bumpy
edges, rotated in the plane): same answer, no aperiodic square at any K —
and that 2D case has already been taken all the way to a fully
machine-checked theorem.

## 6. Why does it come out this way? (the screw intuition)

There's a satisfying reason behind the mountain of case-checking.

When identical cubes fill space, the pattern locally advances by "shift
and maybe twist" moves — imagine each layer reproducing the previous one
after a small rotation, like a spiral staircase: a **screw motion**. For
the pattern to avoid repeating forever, the screw would have to turn
without *ever* coming back to a previous orientation — an *irrational*
twist, like an angle that never divides evenly into a full turn.

But our cube has only **24 rotations**. Any screw built from a finite set
of rotations must return to its starting orientation after a few steps —
at most 64 in the very worst case we found — and a screw that closes is
precisely a repetition. The bumps can *delay* the repetition (the last
two rulebooks standing hid their repeat behind a skewed 64-cube block),
but they can never *abolish* it.

Notably, the one known aperiodic-ish solid in classical mathematics (the
Schmitt–Conway–Danzer tile) achieves its non-repetition exactly by an
irrational screw — the single move a bumpy cube can never make. Our
result says, in effect: *within this family, that's the only trick, and
it's unavailable.*

## 7. What "machine-checked" means, and why we bother

Search programs can have bugs. Solvers can have bugs. To trust a result
of this size, the field's gold standard is a **proof assistant** — we use
**Lean**. You rewrite the entire argument (definitions, lemmas, the lot)
in a formal language, and a small, heavily-scrutinised program (the
*kernel*) checks every logical step down to the axioms of mathematics.
Nothing is taken on faith: not our search code, not the solver, not our
enthusiasm at 2am.

Status of that formal work:

| result | status |
|---|---|
| 2D, every K ("no aperiodic bumpy square") | **fully machine-checked theorem** — the checker re-verifies all certificates itself; no external tool is trusted |
| 3D, K=3 | machine-checked (one standard, verified-checker step for the giant search) |
| 3D, K ≤ 2 | closing now (same pipeline) |
| 3D, every K | **machine-checked theorem** (`no_aperiodic_wang_cube_anyK`): Lean re-derives the census of 1,445,865 rulebooks itself, re-checks the coverage of every rulebook by the 3,745-element frontier, validates all 340 periodic certificates, and the 3,405 emptiness facts are backed by 3,758 certificates re-checked by a formally verified proof checker (the K=3 trust profile — the SAT solver itself is never trusted) |

## 8. What is NOT claimed

Honesty section. This result does **not** solve the 3D einstein problem.
It says: *if* a 3D einstein exists, it is not a rotated bump-and-dent
cube, at any bump resolution. Exotic shapes, mirror reflections, other
matching rules, non-cubic solids — all still open, and the true 3D
einstein (if it exists) must live out there. What this work contributes
is the complete closure of one natural, infinite family — and a
transferable method: *collapse infinitely many tile families into
finitely many rulebooks, then check the rulebooks.*

## 9. One-paragraph summary

You can't make an einstein out of a bumpy cube. However fine you carve
the bumps, a cube's copies can only relate to each other in 1,445,865
essentially different ways, and a computer — double-checked by a proof
assistant that trusts nothing but logic — has looked at every single one:
whatever fills space also fills it periodically, with a repeating block
of at most 64 cubes. The staircase always comes back around.
