import Mathlib
import Moser.Geometry.Polygon

/-!
# Polygon Area Computation

This file implements the shoelace formula for computing the area of a polygon.
-/


open Rat

/-- Compute the signed area of a polygon using the shoelace formula -/
def shoelaceArea (vertices : List RationalPoint) : ℚ :=
  if vertices.length < 3 then 0
  else
    let cyclic := vertices ++ [vertices.head!]
    let pairs := List.zip cyclic cyclic.tail
    let sum := pairs.foldl (fun acc (p, q) => acc + (p 0 * q 1 - q 0 * p 1)) 0
    abs sum / 2

namespace ConvexPolygon




/-- Compute the area of a convex polygon -/
def area (poly : ConvexPolygon) : ℚ :=
  shoelaceArea poly.vertex_list


end ConvexPolygon
