module

public import Mathlib
public import Moser.Geometry.PolygonArea
meta import Mathlib
meta import Moser.Geometry.Polygon
meta import Moser.Geometry.PolygonArea

@[expose] public section

/-!
# Constants for Moser's Worm Problem

This file defines the key constants used in the computational approach:
- `areaThreshold`: Maximum area for candidate Moser sets
- `distanceCutoff`: Maximum distance from origin for polygon vertices

These concrete polygons live over `ℚ`, since their well-formedness proofs
(`nodup`, `vertices_extremePoints`) are discharged by `native_decide`,
which only computes over a concrete decidable representation.
-/

namespace Moser

/--
Area threshold for candidate Moser sets (0.232240)
This is the number we are trying to beat with our working set polygons.
-/
def areaThreshold : ℚ := 232240 / 1000000

/--
The isoceles right triangle with legs of length 1/2.
-/
def IsocelesRightTriangleWorm : ConvexPolygon ℚ where
  vertex_count := 3
  vertex_count_pos := inferInstance
  three_le_vertex_count := by norm_num
  vertices := fun i =>
    match i with
    | ⟨0, _⟩ => ![0, 0]
    | ⟨1, _⟩ => ![1 / 2, 0]
    | ⟨2, _⟩ => ![0, 1 / 2]
    | _ => ![0, 0] -- This case won't happen due to the finiteness of vertex_count
  nodup := by native_decide
  vertices_extremePoints := by native_decide

/--
A square of side length 1/3.
-/
def SquareWorm : ConvexPolygon ℚ where
  vertex_count := 4
  vertex_count_pos := inferInstance
  three_le_vertex_count := by norm_num
  vertices := fun i =>
    match i with
    | ⟨0, _⟩ => ![0, 0]
    | ⟨1, _⟩ => ![1 / 3, 0]
    | ⟨2, _⟩ => ![1 / 3, 1 / 3]
    | ⟨3, _⟩ => ![0, 1 / 3]
    | _ => ![0, 0] -- This case won't happen due to the finiteness of vertex_count
  nodup := by native_decide
  vertices_extremePoints := by native_decide

/--
A right triangle with legs of length 1/3 and 2/3.
TODO parameterize this and the above worms by leg lengths, and then optimize over those parameters.
-/
def RightTriangleOneThirdWorm : ConvexPolygon ℚ where
  vertex_count := 3
  vertex_count_pos := inferInstance
  three_le_vertex_count := by norm_num
  vertices := fun i =>
    match i with
    | ⟨0, _⟩ => ![0, 0]
    | ⟨1, _⟩ => ![1 / 3, 0]
    | ⟨2, _⟩ => ![0, 2 / 3]
    | _ => ![0, 0] -- This case won't happen due to the finiteness of vertex_count
  nodup := by native_decide
  vertices_extremePoints := by native_decide

/--
The "initial worm" is a worm that we
assume any set in our working set must contain an unshifted copy of.

This makes it convenient to exclude points from working set polygons
on the basis of containing a point
such that the hull of such a point with the initial worm would have area > threshold.

We could consider redefining this when optimizing.
For now, we take it to be the isoceles right triangle worm,
since this seems to work well.
-/
def InitialWorm : ConvexPolygon ℚ := IsocelesRightTriangleWorm

-- Example computation: area of InitialWorm
example : InitialWorm.area = 1 / 8 := by
  native_decide


/-- Extent of `LocationRange` along the "wide" sides (positive `x`, positive `y`,
and the long edge `x + y = offset`), scaled from the area threshold. -/
def offset : ℚ := areaThreshold * 4

/-- Extent of `LocationRange` along the "narrow" sides (negative `x`, negative `y`,
and the short edge `x + y = -narrowOffset`). Equals `offset - 1/2`, where `1/2`
is the leg length of `InitialWorm`. -/
def narrowOffset : ℚ := offset - 1 / 2

/--
A convex polygon describing exactly the points that can be added to `InitialWorm`
without pushing the area of the resulting convex hull above `areaThreshold`.

Concretely it is the hexagon with vertices

  (offset, -narrowOffset), (offset, 0),       (0, offset),
  (-narrowOffset, offset), (-narrowOffset, 0), (0, -narrowOffset).

Every edge of this hexagon lies on the level set
`area(hull(InitialWorm ∪ {p})) = areaThreshold`, so any point strictly outside
exceeds the threshold (witness: `area_hull_initialWorm_insert_gt_areaThreshold`).
The asymmetry comes from `InitialWorm` being the right triangle with legs along
the positive axes: outside the hypotenuse `x + y = 1/2` the hull grows fastest,
so the hexagon extends to `offset` there, while in the third quadrant — where
the hull only loses the origin vertex — it extends only to `narrowOffset`.
-/
def LocationRange : ConvexPolygon ℚ where
  vertex_count := 6
  vertex_count_pos := inferInstance
  three_le_vertex_count := by norm_num
  vertices := fun i =>
    match i with
    | ⟨0, _⟩ => ![offset, -narrowOffset]
    | ⟨1, _⟩ => ![offset, 0]
    | ⟨2, _⟩ => ![0, offset]
    | ⟨3, _⟩ => ![-narrowOffset, offset]
    | ⟨4, _⟩ => ![-narrowOffset, 0]
    | ⟨5, _⟩ => ![0, -narrowOffset]
    | _ => ![0, 0] -- This case won't happen due to the finiteness of vertex_count
  nodup := by native_decide
  vertices_extremePoints := by native_decide

/-- A rational upper bound on `√2`, accurate to 15 decimal places. -/
def upperBoundSqrtTwo : ℚ  := 1414213562373095 / 1000000000000000

/--
An upper bound on the distance from the origin for points in the LocationRange
-/
def distanceCutoff : ℚ := offset * upperBoundSqrtTwo

/--
If a point `p` lies outside `LocationRange`, then the convex hull of
`p` together with the vertices of `InitialWorm` has area strictly greater than
`areaThreshold`.

This is the defining property of `LocationRange`: it bounds the set of points
that any convex polygon containing `InitialWorm` can also include without
exceeding the area threshold.
-/
theorem area_hull_initialWorm_insert_gt_areaThreshold
    {p : Point ℚ} (hp : LocationRange.contains p = false) :
    shoelaceArea (convexHullPoints (p :: InitialWorm.vertex_list)) >
      areaThreshold := by
  sorry

end Moser

end
