import Moser.Geometry.Point
import Mathlib.Data.Real.Basic

/-!
# Worms

This file defines worms as piecewise linear paths of unit length.
-/

namespace Moser

/-- Compute the Euclidean distance between two points -/
def distance (p q : Point) : ℚ :=
  -- Approximate sqrt using rational arithmetic
  -- For now, we'll use squared distances and require exact unit length squared
  sorry

/-- Compute the total length of a path given by vertices -/
def totalLength (vertices : List Point) : ℚ :=
  if vertices.length < 2 then 0
  else
    let pairs := List.zip vertices vertices.tail
    pairs.foldl (fun acc (p, q) => acc + distance p q) 0

/-- A worm is a piecewise linear path of unit length -/
structure Worm where
  /-- The vertices defining the path -/
  vertices : List Point
  /-- The path has at least 2 vertices -/
  nonempty : vertices.length ≥ 2
  /-- The total length is exactly 1 -/
  unitLength : totalLength vertices = 1

namespace Worm

/-- Convert a worm to a set in ℝ² (union of line segments) -/
def toPath (w : Worm) : Set (ℝ × ℝ) :=
  -- Union of line segments between consecutive vertices
  sorry

/-- Get the convex hull of the worm's vertices -/
def convexHull (w : Worm) : Set (ℝ × ℝ) :=
  Mathlib.Analysis.Convex.Hull.convexHull ℝ
    (Set.range (fun i : Fin w.vertices.length =>
      Point.toReal (w.vertices.get ⟨i, by omega⟩)))

/-- Convert worm vertices to a convex polygon (if they form one) -/
def toConvexPolygon (w : Worm) : Option ConvexPolygon :=
  if h : w.vertices.length ≥ 3 then
    some { vertices := w.vertices, nonempty := h }
  else
    none

end Worm

end Moser
