# Nano-Water (stub)

Minimal educational models of **water in its forms** — the missing classical
element after air ([`CLOUDS.md`](CLOUDS.md)) and earth ([`GEOLOGY.md`](GEOLOGY.md)).
Same nano spirit. Stub — to be fleshed out.

Water is several regimes, each with its own minimal model and a shared SDF + PBR
(+ refraction) renderer:

## Oceans / waves

The classic result: a wind-driven ocean surface is a **sum of sinusoids with a
statistical spectrum**.

- **Gerstner waves** — a handful of trochoidal waves summed; the cheap, readable
  version.
- **FFT ocean** (Tessendorf) — synthesize a height spectrum (Phillips), inverse-
  FFT to a tiling heightfield. The industry-standard look.

> **Nano (~80 lines).** Sum ~6 Gerstner waves → animated heightfield + normals.
> Upgrade path: Phillips spectrum + inverse FFT.

## Rivers / flowing water

Couples directly to the LEM (you already have stream-power in `GEOLOGY.md` Part 2).

- **Shallow-water equations** (height-averaged Navier–Stokes) — the principled
  model for flow over terrain.
- **Pipe / virtual-pipe model** — a fast cellular approximation (water columns
  exchange flux through "pipes"); the standard nano route, also drives hydraulic
  erosion.

> **Nano (~120 lines).** Pipe-model water over a heightfield → flow + pooling;
> reuse for erosion.

## Ice / glaciers

Ice is a **very viscous fluid**; glaciers flow and carve terrain (U-shaped
valleys, cirques) — couples to the LEM as an erosion+transport agent.

- **Glen's flow law** (non-Newtonian) + the **shallow-ice approximation** — the
  minimal glacier model: ice thickness evolves by mass balance (accumulation −
  melt) and gravity-driven flow.

> **Nano (~120 lines).** Shallow-ice on a heightfield: accumulate, flow, erode
> the bed → glacial valleys. (Cf. Cordonnier's glacier terrain work.)

## Snow

> **Nano:** accumulation as deposition weighted by slope/aspect/temperature;
> dynamics (avalanche/settling) via a simple angle-of-repose redistribution, like
> thermal erosion.

## Optics (the renderer side)

Refraction + **caustics** + absorption (Beer–Lambert depth tint) + foam. Largely
the shared raymarched back end with a transmissive material; caustics are the one
specialized addition.

## References

- Tessendorf, *Simulating Ocean Water* (FFT ocean).
- Mei et al. / Št'ava et al. (pipe-model erosion & water).
- Cuffey & Paterson, *The Physics of Glaciers*; shallow-ice approximation.
