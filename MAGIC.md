# Nano-Magic — thaumic physics for geological simulation

Speculative companion to [`GEOLOGY.md`](GEOLOGY.md), [`CLOUDS.md`](CLOUDS.md),
[`BIOMES.md`](BIOMES.md), and [`WATER.md`](WATER.md). Same nano spirit (smallest
readable code that captures the mechanism) — but here *you invent the laws*.

---

## The lawgiver principle

The whole project rests on one idea: **rich appearance emerges from a few simple
governing rules.** Magic is not a departure from that — it's its purest form,
because you're no longer *discovering* the rules, you're *writing* them.

The discipline that makes invented magic feel real (rather than cosmetic) is
exactly the move that `life` made in `GEOLOGY.md` Part 5:

> **Magic = new fields, new terms, or new conservation laws coupled into the
> existing equations.** Add the rule; let the consequences emerge.

Cosmetic magic (glow textures on ordinary rock) has no causal link to formation
and looks pasted-on. **Lawful magic** — magic expressed as modifications to the
governing PDEs/energy functionals/rate laws — gives you *emergent magical
geology* for free: floating islands as erosional remnants, magical minerals as
free-energy minima, glowing caverns that grew toward their power source.

---

## Coupling table

Magic enters the four regimes (+ LEM, petrology, life) the same way life did — as
source/sink/rate terms, new fields, or new conserved quantities:

| Mechanism | The new physics | Couples to | What emerges |
|---|---|---|---|
| **Mana field** | a scalar field with its own PDE (diffuse + source + decay) | everything (it's read by all the others) | mana pools, **ley lines**, conductive vs. insulating rock |
| **Aether component** | one extra axis in the Gibbs free-energy minimization | petrology / facies | magical minerals as stable assemblages; a 3-axis (P, T, mana) facies diagram |
| **Levitium** | negative effective density → buoyancy term in uplift | LEM | **floating islands** as erosional remnants of buoyant ore |
| **Chronal field τ(x)** | local scaling of `dt` in any integrator | *all* sims | fast-aged badlands beside **frozen-time** pristine pockets |
| **Sympathetic growth** | a *nonlocal* coupling in crystal growth | faceted growth (gems) | eerie over-ordered lattices mirroring their neighbors |
| **Thaumic precipitation/dissolution** | a mana term in the rate law | accretion + caves | mana-stalactites with mana-cycle laminae; caves that grow toward mana |
| **Lithovores / mana-coral** | magical biological agents | life couplings | creature-built or creature-eaten magical rock |
| **Petrifaction** | a life→rock conversion process | life ↔ rock | basilisk fields, frozen forests, creeping stone |

The substrate is the **mana field**: most other mechanisms just *read* it. Build
it first.

---

## Mechanisms

### Mana field — the substrate

A scalar field `m(x, t)` evolving by its own PDE: `∂m/∂t = D∇²m + S − λm`
(diffusion + sources − decay). Sources at ley nodes/leylines; some rock types are
**conductive** (high `D`), some **insulating** (low `D`) → mana channels and pools
form where conductivity and sources interact. Every downstream mechanism reads
`m`.

> **Nano (~60 lines).** A grid + the diffusion-decay update, with source cells and
> per-rock-type `D`. Render `m` as an emissive overlay to see ley lines.

### Aether component — magical petrology *(deep dive)*

Real petrology finds the stable mineral assemblage by **minimizing total Gibbs
free energy** `G = Σ nᵢ μᵢ` over phase amounts `nᵢ`, subject to bulk-composition
mass balance, at given `(P, T)`. To add magic, add **one component** — "aether" —
to the composition vector, and define magical phases that consume it (e.g.
`manite = silicate + aether`) whose chemical potentials depend on `(P, T, mana
activity)`, with the mana activity set by the local field `m`.

Then run the **same minimization, unchanged**. The consequence is automatic: in
high-mana regions the free-energy-minimizing assemblage *includes* magical
minerals, and there's a phase boundary in `(P, T, m)` space — a literal 3-axis
facies diagram. Magic minerals aren't placed; they're the energetic ground truth.

> **Nano (~+40 lines on nano-petrology).** In the fractional-crystallization loop,
> add aether-bearing minerals that saturate when `m` exceeds a (temperature-
> dependent) threshold — they crystallize at their slot in an extended Bowen
> series. Skip the real activity model; use idealized saturation in `(T, m)`.

### Levitium — floating islands, earned

Rock with high levitium content has **negative effective density**. In the LEM,
the uplift source term gains a buoyancy contribution `∝ −ρ_eff`. Where levitium
ore concentrates, the buoyancy outpaces gravity; the *ordinary* surrounding rock
erodes away by the normal stream-power + diffusion process — leaving the buoyant
ore behind as a **floating island**. It's an erosional remnant, like a mesa or
hoodoo, just with the sign of gravity locally flipped. Earned, not drawn.

> **Nano (~+20 lines on nano-LEM).** Add a levitium concentration field; add its
> buoyancy to the uplift term; let erosion run. Islands emerge where ore + erosion
> coincide.

### Chronal field — spatial time *(deep dive)*

Every sim here is an explicit integration: `state ← state + dt · f(state)`.
Introduce a field `τ(x) ≥ 0`, the local time-rate, and replace `dt` with
`dt · τ(x)` per cell. `τ > 1` → fast-forwarded geology (rapid erosion, aged rock,
fully-grown crystals); `τ → 0` → **frozen pockets** (pristine, unweathered).
Consequences emerge for free: a slow-time bubble preserves a soft spire while the
fast-time terrain around it erodes into badlands.

Two subtleties worth knowing:
- **Stability.** Explicit integration has a CFL limit, so you must cap
  `dt · τ_max` and **substep** the fast regions, or they blow up.
- **Reversal (`τ < 0`) is dangerous on purpose.** Negative time runs geology
  backwards — un-erosion, crystals dissolving back into melt. It's evocative, but
  it breaks the **well-founded ordering** every termination argument relies on
  (see the Verus note below): a `decreases` clause has nothing to decrease when
  time can go up. A great teaching moment about what "lawful" really costs.

> **Nano (~+5 lines per integrator + a substep guard).** One field, one
> multiply, one cap. The cheapest mechanism with the largest payoff.

### Sympathetic growth — resonant crystals

A **nonlocal** coupling in the faceted-growth model: a crystal's growth direction/
rate is biased toward matching nearby crystals (a kernel over neighbors). The
result is unnaturally *ordered* formations — lattices that echo each other across
gaps, the visual signature of "this place is enchanted." Genuinely non-physical
(real growth is local), which is the point.

> **Nano (~+30 lines on nano-gem).** Add a neighbor-orientation term to the Wulff/
> growth-competition step.

### Thaumic precipitation & dissolution — living caverns

Add a mana term to the accretion and dissolution rate laws (`GEOLOGY.md` Part 4).
Precipitation of *mana-mineral* where thaumic flux degasses → glowing speleothems
**banded by mana cycles** (mana-laminae as a paleo-mana record, exactly as real
laminae record climate). Dissolution rate coupled to `∇m` → caves that grow
*toward* mana sources, self-organizing into deliberate-looking, almost-designed
networks.

> **Nano (~+30 lines total** on the speleothem and cave models).** A mana
> multiplier on the rate; for caves, bias the channelization toward `∇m`.

### Lithovores & mana-coral — magical agents

The life couplings of Part 5, extended: creatures that biomineralize mana-crystal
(coral that builds *glowing* reef) or that eat specific minerals (rock-golems,
the magical cousin of the parrotfish-as-sand-factory). Same source/sink terms,
new biology.

### Petrifaction — life becomes rock

A conversion *process*: a field (a basilisk's gaze, a curse front) that turns
biological material into stone at some rate — coupling the `BIOMES.md` vegetation/
creature layer into the rock layer. Frozen forests, creeping stone, basilisk
fields as a propagating front.

---

## Design discipline — what makes invented magic feel real

Borrowing the spirit of "hard magic" design and good simulation hygiene, three
self-imposed laws keep emergent magic coherent:

1. **Conservation.** Mana is conserved (or sourced/sunk by *explicit* rules).
   Levitium buoyancy can't manufacture energy. No free lunch — that's what makes a
   world feel lawful rather than arbitrary.
2. **Locality + propagation.** Effects spread through fields and fluxes (the mana
   PDE), not by fiat. Influence has a speed and a falloff.
3. **Consequence / tradeoff.** Using magic costs something the simulation tracks
   (drains a mana pool, ages rock via the chronal field). Power with a ledger.

If a mechanism violates all three, it's cosmetic; if it obeys them, it composes
with everything else.

---

## Formally-verified thaumodynamics *(the on-brand kicker)*

This is a Verus repo — so **lawful magic can be provable magic.** The invented
laws are exactly the kind of invariant Verus is built to machine-check:

- **Mana conservation** — write the field update in flux form and prove the global
  sum is invariant absent explicit sources (a `spec fn total_mana` with an
  `ensures` that it's preserved by `step`).
- **No energy from nothing** — prove the levitium buoyancy term can't produce a
  net positive energy cycle.
- **Termination under the chronal field** — `τ ≥ 0` keeps the simulation's
  `decreases` measure well-founded; `τ < 0` provably does not. The verifier
  *enforces* the boundary between safe time-dilation and paradox.

Formally-verified worldbuilding: the magic system whose conservation laws are
machine-checked.

---

## Suggested build order

1. **Mana field** — the substrate everything reads (~60 lines).
2. **Chronal field** — one multiply per integrator; huge payoff, near-zero cost.
3. **Aether component** — reuses the nano-petrology loop.
4. **Levitium** — reuses the nano-LEM.
5. **Thaumic precipitation/dissolution** + **sympathetic growth** — reuse the
   Part-4 regime models.
6. **Lithovores / petrifaction** — once the life couplings exist.
7. **Verified invariants** — add the conservation/termination proofs as you go.

All add-ons to existing nano-models plus one new field, so the marginal cost stays
small — magical geology for a few hundred extra lines on top of the real thing.

---

## Inspiration

- **Emergence:** the same principle as every other doc here — simple rules, rich
  results.
- **Hard-magic design:** Sanderson's Laws (a magic system's interest scales with
  how well its *limits* are understood) — the fiction-writer's version of
  "conservation + consequence."
- **The real physics being bent:** Gibbs free-energy minimization (petrology),
  stream-power erosion (LEM), reaction-transport (caves) — magic is most
  convincing as a *modification* of a real law, not a replacement.
