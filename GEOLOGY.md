# Nano-Geology

Minimal, educational physical models of **how rock things form** — in the spirit
of [nanoGPT](https://github.com/karpathy/nanoGPT) and the
[$1 Unistroke Recognizer](https://depts.washington.edu/acelab/proj/dollar/index.html):
the smallest readable code that captures the *real* mechanism, not a production
reimplementation.

Companion to [`CLOUDS.md`](CLOUDS.md) — same two philosophies below.

---

## Philosophy

Three ideas run through every topic here:

1. **Type ≈ f(a few variables).** Clouds = f(altitude, stability). Landforms =
   f(uplift, erosion). Rock type = f(composition, T, P, cooling rate,
   environment). The taxonomy is large but the *generative* parameter space is
   small. Sweep the few variables and you visit every named region.

2. **Physical sim (emergent) vs. noise fake (phenomenological).** Games fake
   rock/cave/marble with Perlin noise — gorgeous, but the appearance has no
   causal link to formation. The interesting, unfilled niche is the opposite:
   *appearance derived from the actual process*. That's what these nano-models
   target.

3. **One shared back end.** Every regime feeds the same renderer: a **signed
   distance field** (the geometry) textured with a **per-mineral PBR material
   library** (the optics). The geometry *generator* is what swaps between rock
   types; the renderer is universal. (Both `verus-ray-marching` (SDF) and
   `verus-geometry` (Voronoi/Delaunay) already provide foundations.)

The "nano" target throughout: a few hundred readable lines per model, capturing
the essence, with the production complexity (full thermodynamic databases, 3D
high-res solvers, validated kinetics) explicitly left out.

---

## Part 1 — Rock type formation (petrology)

*Which* rock forms, as a function of physical conditions. Three classes:

### Igneous — composition × cooling rate

Molten rock solidifies. Silica content sets chemistry; cooling rate sets grain
size (slow/deep → coarse; fast/surface → fine; quenched → glass):

| | **Felsic** (high SiO₂) | **Intermediate** | **Mafic** | **Ultramafic** |
|---|---|---|---|---|
| **Intrusive** (slow, coarse) | granite | diorite | gabbro | peridotite |
| **Extrusive** (fast, fine) | rhyolite | andesite | basalt | komatiite |

Texture specials: obsidian (quenched glass), pumice (frothy felsic), scoria
(frothy mafic).

The "which mineral forms *when*" law is **Bowen's reaction series** — the
temperature-ordered crystallization sequence: olivine → pyroxene → amphibole →
biotite (with Ca→Na plagioclase in parallel), converging to K-feldspar →
muscovite → **quartz last**.

### Sedimentary — material × environment × energy

Clastic sorts by transport energy → grain size: gravel→conglomerate,
sand→sandstone, silt→siltstone, clay→shale. Chemical/biochemical: limestone
(CaCO₃), chert, evaporites (salt/gypsum), coal. Then compaction + cementation
(diagenesis).

### Metamorphic — protolith × (P, T) ← literally a phase diagram

Existing rock transformed by heat + pressure. **Metamorphic facies** is a P–T
diagram partitioned into regions, each with a characteristic assemblage:
greenschist → amphibolite → granulite (rising T); blueschist (high P/low T);
eclogite (extreme). Directed pressure adds **foliation** with a grade
progression: slate → phyllite → schist → gneiss. Non-foliated: limestone→marble,
sandstone→quartzite. Index minerals (chlorite→biotite→garnet→staurolite→
kyanite→sillimanite) mark grade.

### The unifying law + real tools

**Gibbs free-energy minimization**: given bulk composition, P, and T, the stable
assemblage is the one minimizing free energy. Real software: **MELTS /
rhyolite-MELTS** (igneous crystallization), **Perple_X / THERMOCALC /
Theriak-Domino** (metamorphic pseudosections).

> **Nano implementation (~100–150 lines).** Skip the thermodynamic database. For
> igneous, simulate **fractional crystallization**: start with a melt
> composition, step temperature down, remove minerals in Bowen order as each
> saturates, track the residual melt. This is a small loop (Rayleigh
> fractionation) that genuinely predicts *which minerals appear when* and the
> resulting rock. For metamorphic, a P–T → facies lookup that returns the
> assemblage. For sedimentary, an energy/chemistry decision tree. What you skip:
> real activity models and the full mineral database — you hard-code ~10
> minerals and idealized saturation temperatures.

---

## Part 2 — Landform evolution (LEMs)

How *terrain* forms over geological time. Realistic landforms emerge from three
terms:

- **Stream-power law** (fluvial incision): `E = K · Aᵐ · Sⁿ` — erosion vs.
  drainage area `A` and slope `S`. Carves valleys, branching river networks.
- **Hillslope diffusion**: `∂z/∂t = D ∇²z` — soil creep smooths ridges.
- **Tectonic uplift** as a source term — mountains organize themselves as
  erosion fights uplift.

Real software: **Landlab** (Python, modular), **Fastscape** (O(n) drainage),
**Badlands** (adds sediment transport + deposition → stratigraphy).

> **Nano implementation (~150–200 lines).** A heightfield `z[i,j]` and a loop:
> (1) **D8 flow routing** — each cell drains to its steepest lower neighbor;
> (2) **drainage accumulation** — sum upstream cells (Fastscape's O(n)
> topological-sort trick is the elegant minimal core); (3) **erode** by the
> stream-power law; (4) **diffuse**; (5) **add uplift**; iterate. Produces real
> drainage networks and mountain ranges. Skip: implicit time-stepping,
> multiple-flow-direction routing, sediment mass conservation.

---

## Part 3 — Petrogenesis → texture (the appearance bridge)

Petrology gives a **recipe** (which minerals, what fractions, what order); a
rendered texture needs **geometry** (grain arrangement) + **optics** (per-mineral
look). Three bridges:

1. **Science → ingredients** (solved): MELTS/Perple_X → mineral modes +
   crystallization order + composition.
2. **Ingredients → microstructure** (borrow from materials science):
   - **Johnson–Mehl tessellation** — a Voronoi variant where seeds nucleate at
     staggered times and grow until they collide. Seed it in **crystallization
     order**: early phases → large euhedral grains; late phases → small,
     interstitial, anhedral. Reproduces igneous texture directly.
   - **Crystal Size Distribution (CSD) theory** (Marsh, Cashman) — quantitatively
     links cooling/nucleation/growth to grain-size statistics. This is the law
     that scales grain size from cooling rate (basalt = many small, gabbro = few
     large).
   - **Strain ellipse** — flatten the tessellation to make **foliation**
     (slate→schist→gneiss); grow **porphyroblasts** (garnet) over the matrix for
     metamorphic.
3. **Microstructure → pixels**: assign each grain a PBR material from a
   per-mineral library (quartz grey, K-feldspar pink, biotite black, olivine
   green…). For a cut face, render a **2D slice** through the 3D grain model. The
   one exotic optical piece: **birefringence under crossed polars** (the
   Michel-Lévy interference colors of a thin section) — fully characterized
   physics, the most striking payoff.

> **Nano implementation (~100 lines).** A 2D **time-seeded weighted Voronoi**:
> seed N points with birth-times in Bowen order, assign each pixel to the seed
> minimizing `dist − growth·(t − birth)`, color by mineral. That alone gives
> recognizably-correct granite vs. basalt vs. gabbro *from the physics*. Add the
> strain-ellipse coordinate scaling (a few lines) and the metamorphic series
> comes nearly free. Reuses `verus-geometry`'s Voronoi. Skip: 3D, phase-field
> growth, real birefringence (start with flat per-mineral colors).

---

## Part 4 — Four growth/removal regimes

"What kind of rock thing" is really a question of *which geometry generator*
feeds the shared renderer. There are four:

| Regime | Geometry | Examples | Generator |
|---|---|---|---|
| **Impingement** | grains grow until they collide | granite, basalt, schist | time-seeded Voronoi (Part 3) |
| **Free faceted growth** | crystals grow outward into void | gems, geode crystals, vein quartz | Wulff/habit + growth competition |
| **Layered accretion** | material deposits in laminae | stalactites, agate, flowstone | free-boundary / accretion sim |
| **Dissolution (removal)** | rock is dissolved away | karst caves | reactive transport |

### Gems — free faceted growth

Some gems are already in the pipeline: **porphyroblast** gems (garnet, ruby) come
from the metamorphic step; **pegmatite** gems (emerald, tourmaline, topaz) are
just the low-nucleation tail of the igneous CSD model (few giant crystals).
What's new: **crystal habit** (external faceted shape from the crystal system),
**growth into cavities** (geometric selection → geode comb texture), and **gem
optics** — color from trace **chromophores** (Cr³⁺ → ruby/emerald; Fe–Ti → blue
sapphire), **dispersion** ("fire"), **asterism/chatoyancy** (oriented
inclusions).

> **Nano implementation (~50–80 lines).** Crystal habit via **Wulff
> construction**: intersect half-spaces, one per crystal face (orientations from
> the crystal's symmetry, offset ∝ growth rate) → a convex faceted polytope.
> Render with a colored, transparent material. Skip: real space-group symmetry
> tables (hard-code a couple of habits), spectral dispersion, inclusions.

### Speleothems — layered accretion (the *forward* carbonate reaction)

Chemical precipitation from dripping water as CO₂ degasses: stalactites,
stalagmites, columns, flowstone, draperies. Defining features: **macroscopic
shape from a fluid/drip process** (Short et al. 2005 showed stalactites converge
to a *universal shape* — a free-boundary problem) and **layered banding**
(concentric laminae that even record paleoclimate). Same accretion model gives
**agate** (rhythmic Liesegang banding), travertine, oolites.

> **Nano implementation (~80 lines).** An **axisymmetric accretion** profile:
> radius(height) grows per timestep by a deposition rate from a thin-film
> thickness law; record each layer for banding. Captures the stalactite taper
> and internal laminae. Skip: full free-boundary fluid dynamics; use the
> idealized growth law.

### Caves — dissolution (the *inverse* carbonate reaction)

Most caves are limestone **dissolved** by mildly acidic water — the exact inverse
of speleothems (same chemistry backwards; often the same cave). The crux physics:
calcite dissolution kinetics are **steeply nonlinear near saturation** (≈4th
order; Dreybrodt) — this is *why caves exist*, letting aggressive water stay
reactive deep along a fracture until a conduit **breaks through**. Uniform
dissolution is unstable → **channelization** (reactive-infiltration instability,
Szymczak & Ladd; same family as viscous fingering). **Pattern = f(recharge)**
(Palmer): branchwork / network-maze / ramiform. Sub-types: sulfuric-acid
hypogenic (Carlsbad, Lechuguilla). Non-dissolution cousins: lava tubes (primary
void), sea caves (wave erosion), glacier caves.

Realism move: caves follow **fractures + bedding**, so seed a **discrete fracture
network** as the substrate rather than isotropic noise.

> **Nano implementation (~150 lines).** A 2D grid of apertures; inject water at
> inlets; dissolve walls where flow × undersaturation is high, with the nonlinear
> near-saturation rate; iterate → channels self-organize (the instability appears
> on its own). Extract the void isosurface → SDF → render. Optionally seed a
> fracture network for anisotropy. Skip: full 3D reactive transport, real
> hydrochemistry (use a one-line rate law).

### The satisfying closer: a cave composes all four

A simulated cave scene uses every regime through one SDF + PBR back end:
1. **Dissolution sim** → the void geometry (a cave *is* an SDF — native to
   `verus-ray-marching`).
2. **Impingement pipeline** → the limestone wall material.
3. **Accretion sim** → stalactites/flowstone on the walls.
4. **Faceted growth** → calcite crystals lining vugs.

---

## Part 5 — Life ↔ rock interactions

Plants, animals, and microbes are major geological agents — the fields are
**biogeomorphology**, **geomicrobiology**, and **biomineralization**. The elegant
fit: **life is not a fifth regime — it enters as coupling terms (source / sink /
rate-modifier) on the four regimes above**, plus *soil* as a new integrative
interface.

| Life process | Couples to regime | Enters the model as |
|---|---|---|
| Lichen/root/borer weathering | Dissolution (caves) | rate multiplier (localized to colonized cells) |
| Reefs, stromatolites, chalk | Accretion + impingement | biological deposition source |
| Nacre, shell | Faceted growth | organic template on nucleation |
| Vegetation, bioturbation | Landform evolution (LEM) | modifies erosion `K`, diffusion `D` |
| Pedogenesis (soil) | *new* bio↔rock interface | f(CLORPT) column model |

### Life destroys rock — couples to dissolution

**Bioerosion / biological weathering** accelerates and *directs* dissolution:
- **Lichens & roots** — physical (root wedging, hyphae in cracks) + chemical
  (oxalic/"lichen acids," root-respiration CO₂ → carbonic acid). Dominant on
  exposed rock; leaves characteristic biopitting ("biokarst").
- **Endoliths** — organisms living *inside* rock, dissolving minerals for
  nutrients.
- **Marine borers** — sponges (*Cliona*), piddocks, urchins, and **parrotfish**
  (bite + excrete coral → a major carbonate-sand factory; a large fish can
  produce hundreds of kg of sand/year).

> **Nano (~+30 lines on the cave model).** Add a **biological rate multiplier**
> to dissolution, localized to colonized surface cells. Optional: spread a lichen
> colony by reaction-diffusion/CA that locally boosts weathering → emergent
> biopitting.

### Life builds rock — couples to accretion + impingement

**Bioconstruction / biomineralization** — life as a rock factory:
- **Stromatolites** — cyanobacterial mats trapping sediment + precipitating
  carbonate: **layered accretion with a microbial mat as the deposition front**
  (oldest fossils, microbe-built rock).
- **Reefs** — corals secrete aragonite → reef limestone.
- **Chalk** = coccolithophore shells; **limestone** from forams/shells;
  **diatomite/chert** from diatom/radiolarian silica — biogenic sediments are
  grain packings of skeletons.
- **Banded Iron Formations** — photosynthetic O₂ oxidized dissolved iron → the
  world's iron ore.

> **Nano (~80 lines).** A **stromatolite CA**: a height-map mat growing upward
> with a phototropism + sediment-trapping rule, recording laminae → domal layered
> structures. Biogenic sediments reuse the Part-3 Voronoi/packing pipeline with
> *shell* grains.

### Life templates crystals — couples to faceted growth

Organisms direct nucleation/growth with organic matrices. **Nacre**
(mother-of-pearl) is aragonite tablets in a brick-and-mortar arrangement with
protein mortar — a *designed* microstructure; the Part-4 crystallization physics,
biologically steered.

> **Nano (~few dozen lines).** An offset "brick-wall" tiling of aragonite tablets
> with mortar gaps.

### Life shapes landforms — couples to the LEM (Part 2)

**Biogeomorphology**: vegetation binds soil and cuts erosion (it modifies
stream-power `K` and diffusion `D` directly), with feedbacks:
- **Vegetated dunes** — marram grass stabilizes sand; the sand↔plant feedback
  produces nebkha and parabolic dunes (Baas & Nield's cellular **DECAL** model).
- **Beavers, termite mounds, earthworm bioturbation** — animals as geomorphic
  agents (Darwin's last book was on earthworms building soil).

> **Nano (~+30 lines on the LEM, or ~150 standalone).** Add a **vegetation field
> `V`** to the nano-LEM: it grows where slopes are stable and locally suppresses
> erosion → a coupled bio-LEM. Or the standalone DECAL vegetated-dune CA.

### Soil — the integrative bio↔rock interface (new layer)

**Pedogenesis** is the master example and another *type = f(a few variables)*:
**Jenny's equation** `S = f(climate, organisms, relief, parent material, time)`
(CLORPT). Roots, mycorrhizae, microbes, humus, and bioturbation transform rock →
regolith → layered **horizons** (O/A/B/C).

> **Nano (~100 lines).** A **soil-column** model: a weathering front descends into
> parent rock, organic matter accumulates from the top, bioturbation mixes →
> emergent horizons.

---

## Suggested build order

Dependency-ordered, smallest wins first:

1. **Shared foundations** — SDF renderer (`verus-ray-marching` ✓) + Voronoi
   (`verus-geometry` ✓). Already present.
2. **Nano rock-slice** (Part 3 Voronoi) — quickest visual payoff; granite from
   physics in ~100 lines.
3. **Nano LEM** (Part 2) — fully self-contained heightfield sim; no dependency on
   the others.
4. **Nano petrology** (Part 1) — the fractional-crystallization loop; feeds the
   rock-slice's mineral list.
5. **Nano gem** (Part 4) — Wulff polytope; standalone.
6. **Nano speleothem** (Part 4) — axisymmetric accretion; standalone.
7. **Nano cave** (Part 4) — dissolution → SDF; then *composes* 2, 4, 6 into one
   scene as the capstone.
8. **Nano life couplings** (Part 5) — mostly *add-ons* to existing models (a rate
   multiplier on the cave; a `V` field on the LEM) plus two standalones
   (stromatolite CA, soil column). Cheapest to add last, once their host models
   exist.

Rough total: well under ~1000 lines for the whole suite of standalone educational
models — each independently readable, in the nanoGPT spirit.

---

## References

- **Petrology:** Bowen, *The Evolution of the Igneous Rocks* (reaction series);
  Ghiorso & Sack (MELTS); Connolly (Perple_X); Holland & Powell (THERMOCALC).
- **CSD / microstructure:** Marsh, Cashman (crystal size distributions);
  Johnson–Mehl–Avrami (tessellation kinetics).
- **Landforms:** Howard (stream-power); Braun & Willett (Fastscape);
  Tucker/Gasparini (Landlab); Salles (Badlands); Cordonnier et al. 2016 (the
  graphics ↔ geomorphology bridge).
- **Speleothems:** Short et al. 2005, *Stalactite growth as a free-boundary
  problem*.
- **Caves:** Dreybrodt (dissolution kinetics); Palmer 1991 (cave pattern
  classification); Szymczak & Ladd (reactive-infiltration instability).
- **Appearance:** Dorsey et al. 1999, *Modeling and Rendering of Weathered
  Stone*; Musgrave et al. 1989 (eroded fractal terrains).
- **Life ↔ rock:** Viles (biogeomorphology); Konhauser, *Introduction to
  Geomicrobiology*; Lowenstam & Weiner, *On Biomineralization*; Grotzinger &
  Knoll (stromatolites); Hans Jenny, *Factors of Soil Formation* (CLORPT); Baas &
  Nield (vegetated dunes / DECAL).
