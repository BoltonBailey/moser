/-
Scratch file for visualizing polygons with ProofWidgets.

Open this file in VS Code and put your cursor on any `#html` line below —
the SVG picture appears in the InfoView panel on the right.

This file lives at the project root (outside `Moser/`), so it is NOT part of
the library build. Edit it freely.
-/
import Moser.Constants
import Moser.Geometry.PolygonWidget

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
