module

public import Moser.Real.Certificate
public import Moser.Real.CertificateTen
public import Moser.Geometry.PolygonWidget
public meta import Moser.Real.Certificate
public meta import Moser.Real.CertificateTen
public meta import Moser.Geometry.PolygonWidget
public meta import ProofWidgets.Data.Svg
public meta import ProofWidgets.Component.HtmlDisplay
public meta import Batteries.Data.Rat.Float

public section

/-!
# Visualising a lower-bound certificate

A certificate (`Moser.IsCoverCertificate`) is a finite list of convex sets, every
Moser cover containing an isometric copy of one of them. When the sets are hulls
of rational points — as they are for `Moser.certList` — the collection can be
drawn.

Two views are provided, for any certificate presented as a list of rational
polygons:

* `Moser.certificateOverlayHtml` — all the sets superimposed in one frame, with
  the shared part emphasised. This shows *why* the collection is a certificate:
  one sees the pinned worm hull common to every set, and the ring of directions
  the case analysis runs over.
* `Moser.certificateGridHtml` — small multiples, one cell per set, on a shared
  scale, so the individual sets can be compared and counted.

For the certificate of `Moser.Real.Certificate` these are pre-applied as
`Moser.certOverlayHtml` and `Moser.certGridHtml`; see `Visualize.lean`.
-/

namespace Moser

open ProofWidgets ProofWidgets.Svg ConvexPolygon

/-! ## Generic certificate pictures -/

/--
Superimpose a whole certificate in one frame: every set is drawn faintly, and
the sets in `emphasis` are drawn on top in strong colours. `dots` are marked
with a small disc, and `discs` are drawn as circles (used for an inscribed
disc).
-/
meta def certificateOverlayHtml (polys : List (ConvexPolygon ℚ))
    (emphasis : List (ConvexPolygon ℚ) := []) (dots : List (Point ℚ) := [])
    (discs : List (Point ℚ × ℚ) := []) (pxWidth : Nat := 620) : ProofWidgets.Html :=
  let vertLists : List (List (Point ℚ)) := polys.map ConvexPolygon.vertex_list
  let emphLists : List (List (Point ℚ)) := emphasis.map ConvexPolygon.vertex_list
  let allPts : List (Float × Float) :=
    (vertLists.flatten ++ emphLists.flatten ++ dots).map vertexToFloat
  let f : Svg.Frame := frameForBox pxWidth (boundingBox allPts)
  let toPt : Point ℚ → Svg.Point f := fun v => let (x, y) := vertexToFloat v; Svg.Point.abs x y
  let faint : Svg.Color := (0.62, 0.66, 0.72)
  let strong : Svg.Color := (0.10, 0.25, 0.75)
  let mark : Svg.Color := (0.85, 0.12, 0.12)
  let discCol : Svg.Color := (0.10, 0.60, 0.35)
  let bodies : Array (Svg.Element f) :=
    vertLists.foldl
      (fun acc vl => acc.push (((Svg.polygon (vl.map toPt).toArray)).setStroke faint (.px 1)))
      #[]
  let emphs : Array (Svg.Element f) :=
    emphLists.foldl
      (fun acc vl => acc.push (((Svg.polygon (vl.map toPt).toArray)).setStroke strong (.px 3)))
      #[]
  let circles : Array (Svg.Element f) :=
    discs.foldl
      (fun acc (c, r) => acc.push ((Svg.circle (toPt c) (.abs r)).setStroke discCol (.px 2)))
      #[]
  let points : Array (Svg.Element f) :=
    dots.foldl (fun acc p => acc.push ((Svg.circle (toPt p) (.px 3)).setFill mark)) #[]
  (Svg.toHtml { elements := bodies ++ emphs ++ circles ++ points : Svg f })

/-- Small multiples of a certificate: one cell per set, numbered, on a shared
scale. -/
meta def certificateGridHtml (polys : List (ConvexPolygon ℚ)) (cols : Nat := 12)
    (cellPx : Nat := 92) : ProofWidgets.Html :=
  gridToHtml polys cols cellPx ((List.range polys.length).map fun i => s!"{i}")

/-- Small multiples of a certificate, captioned with each set's area (four
decimal places) — the least of which is the lower bound the certificate
proves. -/
meta def certificateAreaGridHtml (polys : List (ConvexPolygon ℚ)) (cols : Nat := 8)
    (cellPx : Nat := 120) : ProofWidgets.Html :=
  gridToHtml polys cols cellPx
    (polys.map fun p => toString (((((p.area * 10000).floor : ℤ) : ℚ) / 10000).toFloat))

/-! ## The certificate of `Moser.Real.Certificate` -/

/-- The 96 polygons of `certList`, as rational polygons. -/
meta def certPolys : List (ConvexPolygon ℚ) :=
  (List.range 96).filterMap certPolygon

/-- The 96 far points of the certificate. -/
meta def certFarPoints : List (Point ℚ) :=
  (List.range 96).map fun i => hexCenter + farPt i

/-- **The certificate, superimposed.** The 96 sets in grey, the pinned hexagonal
worm hull in blue, its inscribed disc in green, and the 96 far points in red. -/
meta def certOverlayHtml : ProofWidgets.Html :=
  certificateOverlayHtml certPolys [HexWormPoly] certFarPoints [(hexCenter, hexRho)]

/-- **The certificate, as small multiples**: all 96 sets, numbered. -/
meta def certGridHtml : ProofWidgets.Html := certificateGridHtml certPolys 12 92

/-- The hexagonal worm itself (the pinned base) together with its hull. -/
meta def hexWormHtml : ProofWidgets.Html := ConvexPolygon.toHtml HexWormPoly

/-! ## The compressed certificate of `Moser.Real.CertificateTen` -/

/-- The ten merged polygons of `groupList`. -/
meta def groupPolys : List (ConvexPolygon ℚ) :=
  (List.range 10).filterMap groupPolygon

/-- **The ten merged sets, superimposed** on the same picture as the 96: each is
the intersection of a contiguous arc of the 96, so it still contains the pinned
worm hull (blue) and a blunted spike towards its arc of far points (red). -/
meta def groupOverlayHtml : ProofWidgets.Html :=
  certificateOverlayHtml groupPolys [HexWormPoly] certFarPoints [(hexCenter, hexRho)]

/-- **The ten merged sets**, side by side, captioned with their areas; the least
of them is the bound `817/5000 = 0.1634`. -/
meta def groupGridHtml : ProofWidgets.Html := certificateAreaGridHtml groupPolys 5 170

/-- The `g`-th merged set drawn on top of the arc of sets it replaces, so one can
see how much area the merge costs. -/
meta def groupWithArcHtml (g : ℕ) (arc : List ℕ) : ProofWidgets.Html :=
  certificateOverlayHtml (arc.filterMap certPolygon) (groupPolygon g).toList
    (arc.map fun i => hexCenter + farPt i) [(hexCenter, hexRho)]

end Moser

end
