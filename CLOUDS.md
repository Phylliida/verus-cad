# Procedurally Generating Cloud Types

Notes on whether (and how) you can procedurally generate the full range of
cloud types. Two senses of "procedural" — **noise modeling** (graphics) and
**physical simulation** (atmospheric science). This document focuses on the
physical route, with the noise route summarized for contrast.

---

## 1. The key insight: type ≈ (altitude, morphology, precipitation)

There's no closed-form generator that *enumerates* the cloud taxonomy, but the
problem is tractable because cloud type is a **low-dimensional** function of a
couple of physical variables. The WMO classification has 10 genera, but they
live on a small grid:

|                                   | **Layered (stratiform / stable air)** | **Heaped (cumuliform / unstable air)** |
| --------------------------------- | -------------------------------------- | --------------------------------------- |
| **High (cirro-, ~6–13 km, ice)**  | cirrostratus                           | cirrus / cirrocumulus                   |
| **Mid (alto-, ~2–7 km)**          | altostratus                            | altocumulus                             |
| **Low (~0–2 km)**                 | stratus                                | cumulus                                 |
| **Vertical / precipitating**      | nimbostratus                           | cumulonimbus, stratocumulus             |

So **genus ≈ (altitude band) × (stable-vs-convective) + a precipitation flag.**
Species and varieties (fibratus, lenticularis, undulatus…) are second-order
modifiers on top. A generator only has to walk a ~2–3 dimensional parameter
space, not produce 100 bespoke shapes.

**Honest caveat:** "all the different types" is bounded by the *human* taxonomy,
which is fuzzy and overlapping (stratocumulus ↔ cumulus is a continuum). No
algorithm provably enumerates a complete discrete set. What you *can* build is a
parameterized generator whose input space, swept fully, lands in every named
region.

---

## 2. Approach A — Physical simulation (types *emerge*) ← the interesting one

Simulate atmospheric thermodynamics and the morphology falls out of initial
conditions. Nothing is hard-coded as "this is a cumulus."

The physical determinants:

- **Temperature lapse rate vs. the moist adiabat → stability.** Stable air →
  flat layered sheets (stratus family); unstable → convective towers (cumulus
  family).
- **Humidity + a lifting mechanism** (thermal convection, orographic, frontal) →
  where condensation starts and how high it goes.
- **Wind shear** → cirrus streaks, lenticular caps, anvil spreading on
  cumulonimbus.
- **Condensation level + freezing level** → low/mid/high band and ice-vs-water
  character.

Vary those few inputs and you get the whole grid without ever naming a type.

### What the physics actually requires

This decomposition tells you what's "free" and what's expensive:

1. **A fluid solver** — usually the *anelastic* approximation (filters out sound
   waves so you can take big timesteps), Navier–Stokes + buoyancy. Standard.
2. **Moist thermodynamics** — track potential temperature and water-vapor mixing
   ratio.
3. **Saturation adjustment** — the one-line heart of cloud formation: if a
   parcel is supersaturated, condense the excess vapor to cloud water and
   release latent heat. *This alone, plus buoyancy, gives you cumulus.*
4. **Microphysics** — what distinguishes "blob of condensate" from a real cloud.
   Tiers of fidelity:
   - **Kessler warm-rain** (1969) — vapor → cloud → rain, ~3 equations. Trivial
     to implement; gets you cumulus → rain.
   - **Single/double-moment bulk** (WSM6, Thompson, Morrison) — adds
     ice/snow/graupel. *This is what unlocks cirrus and the high-cloud genera.*
   - **Bin / Lagrangian (super-droplet)** schemes — resolve the droplet size
     distribution. Research-grade, expensive.
5. **Radiation** (optional but matters) — cloud-top radiative cooling is
   literally what *drives* stratocumulus; needed for the diurnal cycle.

**The free lunch:** once moist thermodynamics + even Kessler microphysics is in
your fluid solver, the convective morphologies (cumulus, stratocumulus,
cumulonimbus) appear on their own from the input sounding and forcing. Ice
microphysics is what's needed for the high clouds.

### Existing libraries

Two camps, and the gap between them matters.

**Real atmospheric-science codes (heavyweight, Fortran, scientifically validated):**

- **CM1** (George Bryan, NCAR) — a *cloud-resolving model* built for idealized
  cloud/storm simulation. Hand it a single atmospheric sounding (temp + humidity
  vs. height) and a trigger, and it grows the cloud. Closest off-the-shelf thing
  to "watch a cumulonimbus develop." Ships with canonical test cases.
- **SAM** (System for Atmospheric Modeling, Khairoutdinov) — anelastic
  cloud-resolving model, widely used for cloud studies.
- **WRF** — the operational mesoscale workhorse. Overkill unless you want
  real-world geography + reanalysis input (GFS/ERA5).
- **DALES**, **PALM**, **MicroHH** — Large-Eddy Simulation codes for
  boundary-layer clouds (shallow cumulus, stratocumulus). **MicroHH** is
  C++/CUDA and GPU-capable.

**Modern, hackable ones:**

- **PyCLES** — Python/Cython LES designed for clouds; far more readable than the
  Fortran codes.
- **PySDM** — Pythonic super-droplet Lagrangian microphysics; elegant if you
  care about droplet-distribution physics specifically.
- **CliMA** (`ClimaAtmos.jl`, `Oceananigans.jl`) — Julia, GPU-first, the most
  modern and inspectable codebase in the field.

**Catch:** the "real" codes output NetCDF fields, not pictures. You're a *user*
configuring domains and soundings; visualization is a separate problem. Getting
cloud *types* out means knowing which idealized case produces which — and those
already exist as standard intercomparisons:

- **BOMEX / RICO** → trade / shallow cumulus
- **DYCOMS-II** → stratocumulus
- **Weisman–Klemp sounding** → supercell cumulonimbus
- **ARM** → diurnal cumulus over land

### How much work

| Goal | Effort | Notes |
| --- | --- | --- |
| **Run an existing model** (CM1/SAM/PyCLES) on canonical soundings | Days→weeks | No coding; effort is build/config/learning + separate viz. Scientifically real clouds. |
| **Write a 2D toy** — anelastic solver + saturation adjustment + Kessler | A few weeks | The "warm bubble rising in unstable air" exercise. Grows a convective cloud that rains. Grad-assignment scale for someone comfortable with PDE solvers. |
| **3D toy, GPU, convincing cumulus/Cb** | 1–3 months | Resolution + performance is the cost. In reach of the existing GPU-dispatch infrastructure. |
| **Span the full taxonomy with your own code** (ice microphysics + radiation + enough resolution for layered *and* heaped regimes) | Months→years | Exactly why people use SAM/WRF rather than rolling their own. |

### Recommendation

- **Goal = understanding / watching types emerge:** grab **CM1** and run a
  couple of its idealized soundings. Fastest path to real clouds, zero
  solver-writing.
- **Goal = build it yourself:** write the **Tier-1 toy** — a 2D anelastic solver
  with saturation adjustment and Kessler microphysics. Bounded and well
  documented; a cloud growing within a few weeks; push to 3D on the GPU later.
  The "span all types" ambition comes later by swapping Kessler for an ice
  scheme.

**References for the toy:** Klemp & Wilhelmson (1978) for the classic
formulation; Markowski & Richardson, *Mesoscale Meteorology in Midlatitudes*,
for the physics.

---

## 3. Approach B — Procedural noise modeling (graphics) — for contrast

This is the route with a literal **"cloud type" knob**. Canonical reference:
Andrew Schneider's *"Real-Time Volumetric Cloudscapes"* (Guerrilla Games,
Horizon Zero Dawn — GPU Pro 7 / SIGGRAPH 2015–2017):

1. **Base density field** from tiling **Perlin–Worley** noise (Perlin for
   billows, inverted Worley/cellular for cauliflower erosion).
2. A **weather texture** with channels for *coverage*, *cloud type*, and
   *wetness/precipitation*.
3. The **cloud-type channel drives a height-gradient remap**: at type=0 density
   is squashed into a thin low slab (stratus); at ~0.5 a mid puffy blob
   (stratocumulus/cumulus); at 1.0 a tall column wide at the base, spreading at
   top (cumulonimbus). That single remap *is* the "all types from one algorithm"
   mechanism.
4. **Curl noise** distorts edges for wispy detail; higher altitude + thinner
   field → cirrus-like streaks.

Other references: Inigo Quílez's volumetric raymarched clouds (iquilezles.org);
Fredrik Häggström's thesis *"Real-time rendering of volumetric clouds"*;
Sébastien Hillaire's physically-based atmosphere work for Frostbite.

This fits the `verus-ray-marching` crate directly — it's a density function
raymarched exactly like the existing SDF scenes, just with soft density instead
of a hard surface.
