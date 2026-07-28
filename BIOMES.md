# Nano-Biomes (stub)

Minimal educational models of **how plants and ecosystems are generated** — same
spirit as [`GEOLOGY.md`](GEOLOGY.md) and [`CLOUDS.md`](CLOUDS.md): smallest
readable code that captures the real mechanism. Stub — to be fleshed out.

## The hook: biome = f(temperature, precipitation)

The **Whittaker diagram** is the cleanest "type = f(2 variables)" grid anywhere:
plot mean annual temperature against precipitation and the biomes partition the
plane — desert, grassland, savanna, temperate forest, taiga, tundra, tropical
rainforest. Hand it a climate field (which you already get from terrain altitude +
latitude + the cloud/water cycle) and it returns a biome map.

> **Nano (~30 lines).** A Whittaker classifier: `(T, P) → biome` via region
> lookup. Feeds everything downstream (which plants to instantiate where).

## Plant form = f(a small grammar)

A single plant's shape is the canonical "emergence from simple rules":

- **L-systems** — a rewriting grammar + turtle interpretation; `form = f(rules,
  iterations)`. The original Lindenmayer use case was literally plant growth.
- **Space colonization** (Runions et al.) — scatter attraction points, grow
  branches toward them; produces strikingly natural trees.
- (Cross-ref: the `synthetic-sylviculture` project already explores procedural
  tree growth — a fuller physiological model.)

> **Nano (~80 lines).** An L-system interpreter + turtle graphics → a tree/fern.
> Or space-colonization for more natural crowns.

## Ecosystem distribution

Climate field → Whittaker biome map → instantiate species (with density/size from
local conditions) → optional succession dynamics over time.

> **Nano:** scatter plants by biome with Poisson-disk sampling; weight species by
> local `(T, P, soil)`.

## To expand later

- Succession / competition dynamics (cellular or agent-based).
- Coupling back to the LEM (vegetation modifies erosion — see `GEOLOGY.md` Part 5).
- Animal/ecosystem layers (food webs, herbivory pressure on vegetation).

## References

- Whittaker, *Communities and Ecosystems* (biome diagram).
- Prusinkiewicz & Lindenmayer, *The Algorithmic Beauty of Plants* (L-systems).
- Runions et al. (space colonization for trees).
