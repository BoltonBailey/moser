import Moser.Geometry.Polygon

/-!
# Polygon Area Computation

This file implements the shoelace formula for computing the area of a polygon.
-/

namespace Moser

/-- Compute the signed area of a polygon using the shoelace formula -/
def shoelaceArea (vertices : List Point) : ℚ :=
  if h : vertices.length < 3 then 0
  else
    let cyclic := vertices ++ [vertices.head!]
    let pairs := List.zip cyclic cyclic.tail
    let sum := pairs.foldl (fun acc (p, q) => acc + (p.1 * q.2 - q.1 * p.2)) 0
    abs sum / 2

namespace ConvexPolygon

/-- Compute the area of a convex polygon -/
def area (poly : ConvexPolygon) : ℚ :=
  shoelaceArea poly.vertices

end ConvexPolygon

-- Example computation: area of InitialSquare
example : shoelaceArea Constants.InitialSquare = 1 / 9 := by
  native_decide

end Moser
