import Moser.Geometry.Polygon

/-!
# Containment Tests

This file implements point-in-polygon and polygon containment tests.
-/

namespace Moser

/-- Check if a point is on the left side (or on) a directed edge -/
def isLeftOfEdge (p : Point) (v1 v2 : Point) : Bool :=
  Point.crossProduct (v2 - v1) (p - v1) ≥ 0

/-- Check if a point is inside or on the boundary of a convex polygon -/
def pointInConvexPolygon (p : Point) (poly : ConvexPolygon) : Bool :=
  let edges := poly.edges
  edges.all fun (v1, v2) => isLeftOfEdge p v1 v2

namespace ConvexPolygon

/-- Check if a point is contained in the polygon -/
def contains (poly : ConvexPolygon) (p : Point) : Bool :=
  pointInConvexPolygon p poly

/-- Check if all vertices of another polygon are contained -/
def containsPolygon (poly : ConvexPolygon) (other : ConvexPolygon) : Bool :=
  other.vertices.all (poly.contains ·)

end ConvexPolygon

end Moser
