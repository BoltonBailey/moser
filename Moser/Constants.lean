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

/-- The vertex-index pairs of the six directed edges of `LocationRange`. -/
def lrEdges : List (Fin LocationRange.vertex_count × Fin LocationRange.vertex_count) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]

/-- `LocationRange.contains` evaluated: the half-space test of each directed edge. -/
lemma locationRange_contains_eq (p : Point ℚ) :
    LocationRange.contains p =
      lrEdges.all (fun e =>
        decide (0 ≤ Point.dotProduct (Point.rotate90Counterclockwise
          (LocationRange.vertices e.2 - LocationRange.vertices e.1))
          (p - LocationRange.vertices e.1))) := rfl

lemma lrv0 : LocationRange.vertices 0 = ![offset, -narrowOffset] := rfl
lemma lrv1 : LocationRange.vertices 1 = ![offset, 0] := rfl
lemma lrv2 : LocationRange.vertices 2 = ![0, offset] := rfl
lemma lrv3 : LocationRange.vertices 3 = ![-narrowOffset, offset] := rfl
lemma lrv4 : LocationRange.vertices 4 = ![-narrowOffset, 0] := rfl
lemma lrv5 : LocationRange.vertices 5 = ![0, -narrowOffset] := rfl

/-- The six half-space tests of `LocationRange` say exactly that `x`, `y` and
`x + y` all lie between `-narrowOffset` and `offset`. -/
lemma locationRange_contains_iff (p : Point ℚ) :
    LocationRange.contains p = true ↔
      (p 0 ≤ offset ∧ p 0 + p 1 ≤ offset ∧ p 1 ≤ offset ∧
        -narrowOffset ≤ p 0 ∧ -narrowOffset ≤ p 0 + p 1 ∧ -narrowOffset ≤ p 1) := by
  rw [locationRange_contains_eq]
  simp only [lrEdges, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq, lrv0, lrv1, lrv2, lrv3, lrv4, lrv5, Point.dotProduct,
    Point.rotate90Counterclockwise, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have ho : (0 : ℚ) < offset := by norm_num [offset, areaThreshold]
  have hn : (0 : ℚ) < narrowOffset := by norm_num [narrowOffset, offset, areaThreshold]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [a1, a2, a3, a4, a5, a6, ho, hn]
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith [a1, a2, a3, a4, a5, a6, ho, hn]

/-!
### The defining property of `LocationRange`

If a point `p` lies outside `LocationRange`, then the convex hull of `p`
together with the vertices of `InitialWorm` has area strictly greater than
`areaThreshold`. Stating this about `shoelaceArea (convexHullPoints …)` would be
stating it about the *output of an unverified algorithm*
(see `convexHullPoints_convex` in `Moser.Geometry.Polygon`), so the property is
proved downstream, in `Moser.LowerBound`, in two forms:

* `Moser.lt_volume_convexHull_insert_initialWorm` — the geometric statement,
  about the Lebesgue measure of the real convex hull;
* `Moser.areaThreshold_lt_area_of_ofListChecked` — the computational statement,
  for the run-time-verified hull `ConvexPolygon.ofListChecked`.

The bridge from `LocationRange.contains` to the six inequalities on the
coordinates is `locationRange_contains_iff` above.
-/

end Moser

end
