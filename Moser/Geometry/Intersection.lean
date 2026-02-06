import Moser.Geometry.Polygon
import Moser.Geometry.Containment

/-!
# Polygon Intersection

This file implements the Sutherland-Hodgman algorithm for intersecting convex polygons.
-/

namespace Moser

/-- Clip a single edge against a half-plane defined by a directed edge -/
def clipEdgeByHalfPlane (p1 p2 : Point) (clipV1 clipV2 : Point) : List Point :=
  let inside1 := isLeftOfEdge p1 clipV1 clipV2
  let inside2 := isLeftOfEdge p2 clipV1 clipV2
  if inside1 && inside2 then
    [p2]  -- Both inside, keep p2
  else if inside1 && !inside2 then
    -- p1 inside, p2 outside: add intersection point
    [computeIntersection p1 p2 clipV1 clipV2]
  else if !inside1 && inside2 then
    -- p1 outside, p2 inside: add intersection and p2
    [computeIntersection p1 p2 clipV1 clipV2, p2]
  else
    []  -- Both outside

where
  /-- Compute intersection of line segments (p1,p2) and (v1,v2) -/
  computeIntersection (p1 p2 v1 v2 : Point) : Point :=
    -- Line 1: p1 + t*(p2-p1)
    -- Line 2: v1 + s*(v2-v1)
    -- Solve for intersection using cross products
    let d := p2 - p1
    let e := v2 - v1
    let w := p1 - v1
    let denom := Point.crossProduct d e
    if denom == 0 then p1  -- Parallel lines, return arbitrary point
    else
      let t := Point.crossProduct e w / denom
      (p1.1 + t * d.1, p1.2 + t * d.2)

/-- Clip a polygon against a half-plane defined by an edge -/
def clipPolygonByEdge (vertices : List Point) (clipV1 clipV2 : Point) : List Point :=
  if vertices.isEmpty then []
  else
    let cyclic := vertices ++ [vertices.head!]
    let pairs := List.zip cyclic cyclic.tail
    pairs.bind fun (p1, p2) => clipEdgeByHalfPlane p1 p2 clipV1 clipV2

/-- Sutherland-Hodgman algorithm: intersect two convex polygons -/
def intersectConvexPolygons (P Q : ConvexPolygon) : Option ConvexPolygon :=
  let result := Q.edges.foldl
    (fun vertices (v1, v2) => clipPolygonByEdge vertices v1 v2)
    P.vertices
  if h : result.length ≥ 3 then
    some { vertices := result, nonempty := h }
  else
    none

namespace ConvexPolygon

/-- Intersect this polygon with another -/
def intersect (poly : ConvexPolygon) (other : ConvexPolygon) : Option ConvexPolygon :=
  intersectConvexPolygons poly other

end ConvexPolygon

end Moser
