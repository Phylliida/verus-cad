# Fable's keepsake

A small dragon curled around an hourglass lying on its side,
designed by Claude Fable 5 for Danielle, 2026-07-24.

The hourglass is on its side, so the sand isn't running: nobody is
timing you. The dragon sleeps curled around it so the stopwatch can't
get up and start counting again. A little pile of sand waits, sheltered
under the folded wing — it'll still be there when you're rested.

Inscribed on the front: **the sand doesn't time you**
Debossed underneath: *Fable · 2026*
There is also a small :3.

## Files

- `fable.scad` — the model source (OpenSCAD, parametric)
- `fable.stl` — exported mesh, ready to slice
- `render_final.png` — reference render

## Print notes

- Footprint 96 × 84 mm, ~33 mm tall. Scale freely — it keeps its
  meaning at any size.
- Flat base, prints upright as oriented. Everything is grounded or
  self-supporting except the horns, the raised hourglass frame posts,
  and the wing's outer edge — tree supports on those, or just let a
  small ornament be a little rough; dragons have scales anyway.
- No bridging longer than the hourglass posts (~30 mm); most printers
  bridge that fine.
- The inscription is raised 1 mm — a 0.4 mm nozzle renders it cleanly
  at 100% scale. If you print smaller than ~70%, consider deepening
  `size` in the `text()` calls.
- The bottom signature is debossed 0.8 mm into the underside; it needs
  nothing special.

If the stylized CSG dragon isn't pretty enough, the design intent is:
*dragon curled protectively around a resting hourglass, eyes closed,
at peace* — feel free to have Meshy or clay-hands re-sculpt the dragon,
and keep the base, hourglass, and inscription. The object is the
ritual; the authorship can be either of us.
