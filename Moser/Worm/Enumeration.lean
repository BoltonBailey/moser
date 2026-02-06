import Moser.Worm.Basic
import Moser.Isometry.Discretization

/-!
# Worm Enumeration

This file enumerates candidate worms by their convex hulls (equiangular polygons).
-/

namespace Moser

/-- Generate all partitions of a rational into k positive parts -/
def partitionRational (total : ℚ) (k : ℕ) (granularity : ℚ) : List (List ℚ) :=
  -- For simplicity, use equal partitions for now
  -- TODO: Implement proper enumeration of all partitions
  [[total / k] * k]

/-- Construct an equiangular k-gon with given edge lengths -/
def constructEquiangularPolygon (edgeLengths : List ℚ) : Option ConvexPolygon :=
  if h : edgeLengths.length < 3 then none
  else
    let k := edgeLengths.length
    let angle := 2 * piApprox / k  -- Angle between consecutive edges

    -- Start at origin, build polygon by adding edges
    let vertices := edgeLengths.foldl
      (fun (state : List Point × ℚ) len =>
        let (verts, currentAngle) := state
        let lastPoint := verts.getLast!
        let newPoint := (
          lastPoint.1 + len * cosApprox currentAngle,
          lastPoint.2 + len * sinApprox currentAngle
        )
        (verts ++ [newPoint], currentAngle + angle))
      ([(0, 0)], 0)

    if h' : vertices.1.length ≥ 3 then
      some { vertices := vertices.1, nonempty := by simp at h'; exact h' }
    else
      none

/-- Enumerate equiangular polygons with k vertices and given perimeter -/
def enumerateEquiangularPolygons (k : ℕ) (perimeter : ℚ) (granularity : ℚ) : List ConvexPolygon :=
  let partitions := partitionRational perimeter k granularity
  partitions.filterMap constructEquiangularPolygon

/-- Enumerate candidate worms by enumerating convex hulls -/
def enumerateWormsByConvexHull (maxVertices : ℕ) (granularity : ℚ) : List ConvexPolygon :=
  (List.range maxVertices).bind fun k =>
    if k < 3 then []
    else enumerateEquiangularPolygons (k + 3) 1 granularity

/-- Default worm enumeration with reasonable parameters -/
def defaultWormEnumeration : List ConvexPolygon :=
  enumerateWormsByConvexHull 6 (1 / 20)

end Moser
