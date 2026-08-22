/-
Scratch file for visualizing polygons with ProofWidgets.

Open this file in VS Code and put your cursor on any `#html` line below —
the SVG picture appears in the InfoView panel on the right.

This file lives at the project root (outside `Moser/`), so it is NOT part of
the library build. Edit it freely.
-/
import Moser.Constants
import Moser.Geometry.PolygonWidget
import Moser.Real.CertificateWidget

open Moser ProofWidgets

/-! ## The hardcoded constants -/

-- A single polygon
#html ConvexPolygon.toHtml LocationRange

-- The three worm shapes, each in its own colour, fitted to a shared frame
#html ConvexPolygon.listToHtml
  [IsocelesRightTriangleWorm, SquareWorm, RightTriangleOneThirdWorm]

-- The initial worm sitting inside its location range
#html ConvexPolygon.listToHtml [InitialWorm, LocationRange]


/-! ## Building polygons on the fly from raw points

`ConvexPolygon.ofList` returns `Option`, so use `filterMap id` to drop any
point sets that don't form a polygon. -/

def myPolys : List (ConvexPolygon ℚ) :=
  ([ [![0, 0], ![2, 0], ![2, 2], ![0, 2]],   -- a square
     [![1, 1], ![4, 1], ![2, 4]] ] :         -- a triangle
    List (List (Point ℚ))).filterMap ConvexPolygon.ofList

#html ConvexPolygon.listToHtml myPolys


/-! ## The lower-bound certificate

`Moser.certList` is a list of 96 convex sets such that every Moser cover
contains an isometric copy of one of them (`Moser.isCoverCertificate_certList`),
which is what proves `41/250 ≤ M` (`Moser.certificate_le_moserCoverNumber`).

`Moser.certPolygon i` is the rational polygon whose region is the `i`-th set —
`Moser.certPolygon_realHull` proves that — so the pictures below really do show
the certificate.
-/

-- All 96 sets superimposed. Blue: the pinned hexagonal worm hull, common to
-- every set. Green: the disc inscribed in it. Red: the 96 far points, one of
-- which every cover must contain (up to the placement of the blue hull).
#html Moser.certOverlayHtml

-- The same 96 sets as small multiples, numbered, on a shared scale.
#html Moser.certGridHtml

-- A closer look at a dozen of them, captioned with their areas; the least area
-- over all 96 is the lower bound the certificate proves.
#html Moser.certificateAreaGridHtml (Moser.certPolys.take 12) 6 150

-- The worm hull that every one of the sets contains.
#html ConvexPolygon.toHtml Moser.HexWormPoly

/-! Any other certificate displays the same way: present it as a list of
`ConvexPolygon ℚ` and call `Moser.certificateOverlayHtml` or
`Moser.certificateGridHtml`. -/


/-! ## The certificate compressed to ten sets

Merging a group of certificate sets into their intersection is sound
(`Moser.IsCoverCertificate.refine`), and consecutive sets above overlap so much
that ten sets still give `0.1634` — against `0.164` for all 96.
-/

-- The ten merged sets superimposed on the same frame as before.
#html Moser.groupOverlayHtml

-- The ten sets side by side, captioned with their areas.
#html Moser.groupGridHtml

-- Group 4 (the widest arc: it merges 30 of the 96) drawn over the sets it replaces.
#html Moser.groupWithArcHtml 4 (List.range' 26 30)
