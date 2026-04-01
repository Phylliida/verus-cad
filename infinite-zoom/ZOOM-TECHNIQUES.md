# Infinite Zoom with Zero Lag — Techniques Research

## The Core Principle

Every professional tool (Figma, Photoshop, Krita, Illustrator) follows the same rule:

> **Zoom is NOT re-rendering.** Zoom is a GPU matrix multiply on an already-rendered image. Re-rendering happens asynchronously to restore crispness.

The zoom gesture is always instant (GPU work). "Sharpening" happens 1-2 frames later.

---

## What We Have Now

All coordinates stored as exact rational numbers (BigInt numerator/denominator). On zoom, snapshot the canvas and GPU-scale it. When zoom stops, rebuild screen coordinates from BigInt world coords.

**Pros:** Truly unlimited precision. No floating-point drift ever.

**Cons:**
- BigInt arithmetic gets expensive at deep zoom (1000+ scroll ticks → hundreds-of-digit numbers)
- The rebuild after zoom stops can take 30-100ms for many strokes
- No LOD — every point of every visible stroke is transformed
- The per-point transform does ~12 BigInt multiplications (the hot bottleneck)

---

## Technique 1: Camera-Relative Float Rendering

**Used by:** Every game engine, every map renderer, Unity, Unreal, Godot.

### The Idea

Keep BigRat for *storage* but use *float* for *rendering*. The key: always subtract the camera center first in BigRat, THEN convert to float. The result of `(world_point - camera)` is always small (it's the pixel offset), so float has full precision.

```javascript
//  Current hot path — 12 BigInt multiplications per point:
const dxn = pt.x.n * cxd - cxn * pt.x.d;    //  2 BigInt muls
const dxd = pt.x.d * cxd;                     //  1 BigInt mul
const sx = b2f(dxn*zn*2n + bw*dxd*zd, dxd*zd*2n); //  4 more BigInt muls + div

//  Camera-relative — 1 BigRat subtraction then float:
const dx = pt.x.sub(cx);          //  BigRat sub (2 muls + 1 add + GCD)
const sx = dx.float() * fzoom + hw; //  float mul + add (instant)
```

This cuts per-point BigInt work by ~60%. But the BigRat subtraction still involves large BigInts at deep zoom.

### Precision Analysis

- float64 has ~15.9 decimal digits of precision
- `(point - camera)` for a nearby point is ~1 pixel ÷ zoom ≈ tiny number
- Converting this tiny BigRat to float: accurate to ~15 digits
- Multiplying by zoom (also ~15 digits): result is screen pixels, sub-pixel accurate
- **Breaks at:** zoom > ~10^15 (which is 5000+ scroll ticks at 10%/tick)

### Further Optimization: Skip BigRat in Hot Path

Store each stroke's screen coordinates at draw time alongside world coords:

```javascript
point.screenX = e.clientX;  //  original screen position
point.screenY = e.clientY;
point.drawCx = cx;          //  camera at draw time
point.drawCy = cy;
point.drawZoom = zoom;       //  zoom at draw time
```

For rendering at the SAME zoom level: `screenX` is exact, zero math.
For rendering at a DIFFERENT zoom level: need BigRat subtraction + float.

---

## Technique 2: Tile-Based Rendering (Map Style)

**Used by:** Google Maps, Leaflet, Mapbox, OpenStreetMap.

### The Idea

Divide world space into tiles (256×256 px). Each tile is rendered once and cached. During zoom, GPU-scale existing tiles while new tiles render in background.

```
Zoom level 0:  1 tile covers the whole world
Zoom level 1:  4 tiles (2×2)
Zoom level 2: 16 tiles (4×4)
...
Zoom level N: 4^N tiles
```

Only tiles in the viewport are rendered. When a stroke is drawn, only the tiles it touches are invalidated.

### For a Drawing App

1. When user draws: rasterize stroke into tiles at current zoom level
2. When user zooms: GPU-scale existing tiles (instant), re-render target-zoom tiles in background
3. Tile cache: LRU, keep last ~50 tiles. Zoom back → cache hit, no re-render.

### Tile Coordinates for Infinite Zoom

Tile indices need arbitrary precision (BigInt x, BigInt y, integer zoom level). Within each tile, coordinates are local floats (0-256). This gives infinite world extent with float precision locally.

**Pros:** Rendering cost ∝ viewport area, not stroke count. Natural LOD.
**Cons:** Complex tile management, seam artifacts, invalidation logic.

---

## Technique 3: WebGL Renderer

**Used by:** Figma, Mapbox GL, deck.gl.

### The Idea

Upload stroke geometry to GPU as vertex buffers. Zoom/pan changes only a uniform matrix. The GPU transforms all vertices at 60fps — changing the matrix costs literally nothing.

```glsl
uniform mat3 u_viewMatrix;   //  zoom + pan
attribute vec2 a_position;   //  world coordinate

void main() {
  vec2 screen = (u_viewMatrix * vec3(a_position, 1.0)).xy;
  gl_Position = vec4(screen, 0.0, 1.0);
}
```

Strokes must be tessellated into triangle strips (GPUs can't draw bezier curves natively). Each line segment → 2 triangles. Round caps/joins → additional triangles.

### Precision Issue

WebGL uses float32 in shaders (~7 decimal digits). For deep zoom, not enough.

**Solution: Camera-relative on CPU, float32 on GPU.**

```javascript
//  CPU: compute camera-relative position in BigRat, convert to float
const dx = pt.x.sub(cx).float();
const dy = pt.y.sub(cy).float();
//  Upload (dx, dy) to GPU vertex buffer
//  GPU applies zoom via matrix (float32 is fine since dx,dy are small)
```

Or use **emulated float64 in WebGL**: encode each f64 as two f32s. Mapbox GL JS does this.

**Pros:** Zoom is literally free (1 uniform change). Millions of vertices at 60fps.
**Cons:** Significant implementation complexity. Stroke tessellation is non-trivial.

---

## Technique 4: Quadtree + LOD

**Used by:** tldraw (R-tree), game engines (octrees), GIS systems.

### The Idea

Store strokes in a quadtree by world-space bounding box. Query returns only visible strokes in O(log N + visible) instead of O(N).

### LOD (Level of Detail)

Pre-compute simplified versions of each stroke using Douglas-Peucker:

```
Level 0: all 500 points (full detail)
Level 1: 50 points  (1px tolerance at 1x zoom)
Level 2: 10 points  (1px tolerance at 0.1x zoom)
Level 3: 3 points   (1px tolerance at 0.01x zoom)
```

At render time, pick the LOD level matching current zoom. This reduces vertex count by 10-100x for overview renders.

**Pros:** O(log N) culling. Massive vertex reduction at far zoom.
**Cons:** Quadtree with BigRat coordinates is complex. Memory cost for LOD copies.

---

## Technique 5: Perturbation / Double-Double Arithmetic

**Used by:** Mandelbrot deep zoomers (10^1000+ zoom, real-time).

### The Idea

float64 gives ~15.9 digits. If you need more, **double-double** arithmetic uses two floats to represent one value with ~31 digits. It's 10-20x slower than plain float but 100-1000x faster than BigInt.

```javascript
class DD {
  constructor(hi, lo = 0) { this.hi = hi; this.lo = lo; }

  add(b) {
    //  Knuth two-sum: exact error-free addition
    const s = this.hi + b.hi;
    const v = s - this.hi;
    const lo = (this.hi - (s - v)) + (b.hi - v) + this.lo + b.lo;
    return new DD(s, lo);
  }

  mul(b) {
    //  Dekker splitting + FMA emulation
    const p = this.hi * b.hi;
    const e = fma(this.hi, b.hi, -p); //  error term
    const lo = e + this.hi * b.lo + this.lo * b.hi;
    return new DD(p, lo);
  }
}
```

### Applied to Drawing

- Camera center tracked at full BigRat precision
- `(point - camera)` computed in BigRat, converted to DD
- `DD * zoom_as_DD` gives screen position with ~31 digits
- Final `.hi` property is the float for canvas rendering
- **Works up to zoom ~10^30** without any BigInt in the render path (except the one subtraction)

---

## Technique 6: What Professional Tools Do

| Tool | Zoom range | Technique | Lag during zoom |
|------|-----------|-----------|-----------------|
| **Figma** | 0.01x–256x | Custom WebGL, tiled framebuffer, LOD culling | Zero (GPU matrix) |
| **Photoshop** | 0.3%–12800% | GPU-accelerated viewport, mipmap pyramid per layer | Zero (GPU texture scale) |
| **Krita** | 1%–10000%+ | Tile-based image engine (64×64 tiles), OpenGL display | Zero (GL texture) |
| **tldraw** | ~0.1x–8x | CSS transforms on DOM elements, R-tree culling | Zero (GPU compositor) |
| **Excalidraw** | ~1%–2000% | Canvas 2D `setTransform()`, per-element cache | Low (re-renders per frame) |
| **Miro** | Wide | Hybrid Canvas/DOM, heavy LOD (text greeking, shape simplification) | Low |
| **Google Maps** | 0–22 levels | Tile pyramid, GPU-scale during zoom, async tile fetch | Zero |

### Figma's Approach (most relevant)

From Evan Wallace (co-founder):
- Custom WebGL 2D renderer, not Canvas 2D
- Content rendered to tiled framebuffers
- Zoom changes tile resolution
- Old tiles kept as fallback (scaled) while new tiles render
- Objects smaller than ~0.5px are skipped (LOD culling)
- "Debounced zoom level" for LOD decisions — doesn't thrash during zoom gesture

### Fabric.js Pattern

`noScaleCache: true` — during scaling, stretch the cached bitmap (blocky but fast). Re-render at correct resolution only when scaling ends. Same principle as our snapshot approach.

---

## Recommended Architecture for This App

### Phase 1: Camera-Relative Float (biggest win, lowest effort)

Replace the current 12-BigInt-multiply-per-point transform with:

```javascript
//  Precompute once per frame:
const fzoom = zoom.float();
const halfW = W / 2, halfH = H / 2;

//  Per point (visible strokes only):
const sx = pt.x.sub(cx).float() * fzoom + halfW;
const sy = pt.y.sub(cy).float() * fzoom + halfH;
```

**The remaining cost** is `pt.x.sub(cx)` — one BigRat subtraction per point (2 BigInt muls + GCD). This is ~3x faster than the current 12-mul approach.

**To eliminate BigRat from the hot path entirely:** precompute screen coords at draw time, only recompute for strokes at different zoom levels. Same-zoom strokes render with zero BigInt math.

### Phase 2: Spatial Index + LOD

- Quadtree for O(log N) viewport queries
- Douglas-Peucker pre-simplification at 3-4 LOD levels
- Skip sub-pixel strokes based on log-scale zoom comparison (float, no BigInt)

### Phase 3: WebGL (if Canvas 2D becomes the bottleneck)

- Tessellate strokes to triangle strips
- Upload to GPU vertex buffers (once per stroke)
- Zoom = 1 uniform matrix change
- Camera-relative float coordinates computed on CPU

---

## Key Optimization Insight

The current code does this per visible point:

```javascript
//  6 BigInt multiplications + 2 BigInt divisions (via b2f):
const dxn = pt.x.n * cxd - cxn * pt.x.d;                    //  2 muls
const dxd = pt.x.d * cxd;                                     //  1 mul
const sx = b2f(dxn * zn * 2n + bw * dxd * zd, dxd * zd * 2n); //  3 muls + div
```

With camera-relative float:

```javascript
//  1 BigRat subtraction (2 muls + GCD) then float:
const sx = pt.x.sub(cx).float() * fzoom + halfW;
```

For 1000-digit BigInts (deep zoom), BigInt multiplication is O(n^1.6) via Karatsuba. Cutting from 12 muls to 2 muls = **~6x speedup** on the hot path. The GCD adds ~2 more mul-equivalents, so realistically **~3x speedup**.

For strokes drawn at the current zoom level (the common case during drawing), caching screen coords gives **∞ speedup** (zero BigInt work).
