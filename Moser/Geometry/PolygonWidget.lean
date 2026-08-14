module

public import Moser.Geometry.Polygon
public meta import Moser.Geometry.Polygon
public meta import ProofWidgets.Data.Svg
public meta import ProofWidgets.Component.HtmlDisplay
public meta import Batteries.Data.Rat.Float

public section

/-!
# Visualising convex polygons

This file provides utilities to render `ConvexPolygon ℚ` values (and lists of
them) as pictures in the InfoView, using the ProofWidgets SVG framework.

The main entry points are:

* `ConvexPolygon.toHtml` — draw a single polygon;
* `ConvexPolygon.listToHtml` — draw a whole collection of polygons in one
  picture (each in a distinct colour), automatically fitting them to a shared
  frame.

Use them with the `#html` command, e.g.

```
#html ConvexPolygon.listToHtml [p, q, r]
```

which pops open an SVG picture in the InfoView.
-/

namespace ConvexPolygon

open ProofWidgets ProofWidgets.Svg

/-- Convert a rational planar point to a `(Float × Float)` pair. -/
private meta def vertexToFloat (p : Point ℚ) : Float × Float := (p 0, p 1)

/-- A small palette of distinct stroke colours, cycled through when drawing
several polygons at once. Values are RGB components in `[0,1]`. -/
private meta def palette : Array Svg.Color := #[
  (0.85, 0.10, 0.10),   -- red
  (0.10, 0.35, 0.85),   -- blue
  (0.10, 0.65, 0.20),   -- green
  (0.85, 0.55, 0.10),   -- orange
  (0.55, 0.20, 0.75),   -- purple
  (0.10, 0.65, 0.70)    -- teal
]

/-- Bounding box `(xmin, ymin, xmax, ymax)` of a (non-empty) list of float
points. Returns the unit box `(0,0,1,1)` for the empty list. -/
private meta def boundingBox (pts : List (Float × Float)) : Float × Float × Float × Float :=
  match pts with
  | [] => (0.0, 0.0, 1.0, 1.0)
  | (x₀, y₀) :: rest =>
    rest.foldl
      (fun (acc : Float × Float × Float × Float) (p : Float × Float) =>
        let (xmin, ymin, xmax, ymax) := acc
        (min xmin p.1, min ymin p.2, max xmax p.1, max ymax p.2))
      (x₀, y₀, x₀, y₀)

/-- Build a `Svg.Frame` of pixel width `pxWidth` that snugly fits the given
bounding box, leaving a 10% margin on all sides and preserving aspect ratio. -/
private meta def frameForBox (pxWidth : Nat) :
    Float × Float × Float × Float → Svg.Frame
  | (xmin, ymin, xmax, ymax) =>
    let w := xmax - xmin
    let h := ymax - ymin
    -- guard against a degenerate (zero-area) box
    let w := if w ≤ 0.0 then 1.0 else w
    let h := if h ≤ 0.0 then 1.0 else h
    let padX := 0.1 * w
    let padY := 0.1 * h
    let xSize := w + 2.0 * padX
    let ySize := h + 2.0 * padY
    let pixelSize := xSize / pxWidth.toFloat
    let pxHeight := (ySize / pixelSize).ceil.toUInt64.toNat
    { xmin := xmin - padX
      ymin := ymin - padY
      xSize := xSize
      width := pxWidth
      height := max 1 pxHeight }

/-- The SVG elements (filled-and-outlined polygon plus vertex dots) for a single
polygon drawn in colour `c` within frame `f`. -/
private meta def elementsFor (f : Svg.Frame) (c : Svg.Color) (verts : List (Point ℚ)) :
    Array (Svg.Element f) :=
  let pts : Array (Svg.Point f) :=
    (verts.map fun v => let (x, y) := vertexToFloat v; (Svg.Point.abs x y)).toArray
  let body : Svg.Element f :=
    (Svg.polygon pts).setStroke c (.px 2)
  let dots : Array (Svg.Element f) :=
    pts.map fun p => (Svg.circle p (.px 3)).setFill c
  #[body] ++ dots

/--
Render a list of convex polygons as a single SVG picture, fitting them all to a
shared frame. Each polygon is drawn (outline + vertices) in a distinct colour
cycled from `palette`.

This is the main tool for visualising the *sets* of polygons produced by the
constructions in this development.
-/
meta def listToHtml (polys : List (ConvexPolygon ℚ)) (pxWidth : Nat := 500) : ProofWidgets.Html :=
  let vertLists : List (List (Point ℚ)) := polys.map ConvexPolygon.vertex_list
  let allPts : List (Float × Float) := vertLists.flatten.map vertexToFloat
  let f : Svg.Frame := frameForBox pxWidth (boundingBox allPts)
  let elements : Array (Svg.Element f) :=
    (vertLists.zipIdx.foldl
      (fun acc (vl, i) =>
        acc ++ elementsFor f (palette[i % palette.size]?.getD (0.0, 0.0, 0.0)) vl)
      #[])
  (Svg.toHtml { elements := elements : Svg f })

/-- Render a single convex polygon as an SVG picture. -/
meta def toHtml (poly : ConvexPolygon ℚ) (pxWidth : Nat := 400) : ProofWidgets.Html :=
  listToHtml [poly] pxWidth

end ConvexPolygon

end
