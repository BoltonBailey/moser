import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.MetricSpace.Basic
import Moser.Geometry.Point

/-!
# Convex Polygons

This file defines convex polygons as ordered lists of rational vertices.
-/

namespace Moser

/-- A convex polygon represented by its vertices in counterclockwise order -/
structure ConvexPolygon where
  /-- The vertices of the polygon in counterclockwise order -/
  vertices : List Point
  /-- The polygon has at least 3 vertices -/
  nonempty : vertices.length ≥ 3
  -- TODO: Add proofs that vertices form a convex polygon in counterclockwise order
  -- convex : IsConvex vertices
  -- counterclockwise : IsCounterclockwise vertices

namespace ConvexPolygon

/-- Convert a polygon to a set in ℝ² via convex hull -/
def toSet (poly : ConvexPolygon) : Set (ℝ × ℝ) :=
  convexHull ℝ (Set.range (fun i : Fin poly.vertices.length =>
    Point.toReal (poly.vertices.get ⟨i, by omega⟩)))

/-- Get the edges of the polygon as pairs of consecutive vertices -/
def edges (poly : ConvexPolygon) : List (Point × Point) :=
  List.zipWith (fun p q => (p, q))
    poly.vertices
    (poly.vertices.tail ++ [poly.vertices.head!])

/-- Get the number of vertices -/
def numVertices (poly : ConvexPolygon) : ℕ := poly.vertices.length

/-- Check if all vertices satisfy a predicate -/
def allVertices (poly : ConvexPolygon) (p : Point → Bool) : Bool :=
  poly.vertices.all p

end ConvexPolygon

end Moser
