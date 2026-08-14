import Moser.Geometry.HalfSpaces
import Moser.Geometry.Polygon
import Moser.Geometry.PolygonArea

/-!
# Allowable Additions

Given a convex polygon `P`, an area threshold `A_*`, and a tolerance `τ > 0`,
this file describes the region of the plane such that adjoining a point in
that region to `P` and taking the convex hull keeps the resulting area below
`A_*`. The region is described as the intersection of a finite collection of
closed half-spaces, one for each ordered pair of (distinct) vertices of `P`.

For each ordered pair of vertices `(V_i, V_j)` we compute the *growable
distance* `d`: a number in `K`, within tolerance `τ` of the unique exact
value `d_*` for which `A_R + T(d_*) = A_*`, where

* `A_R` is the area of `P` weakly to the right of the directed line `V_i → V_j`,
* `T(d)` is the area of the triangle with base `V_i V_j` and height `d`.

Equivalently, the area of the convex hull of `P ∪ {p}` where `p` is at
left-distance `d_*` from the directed line `V_i V_j` equals `A_*`. The
*growth half-space* of `(V_i, V_j)` is the closed half-space of points at
signed left-distance at most `d` from the directed line: it is bounded by the
line parallel to `V_i V_j` at perpendicular distance `d` on its left, and lies
weakly to the right of that shifted line. The *growth half-space intersection*
is the intersection over all ordered pairs of distinct vertices.

Although `d_* = 2·(A_* − A_R)/|V_i V_j|` is irrational, the growth half-space
itself is exactly rational: `p` is at left-distance at most `d_*` iff
`crossProduct (V_j − V_i) (p − V_i) ≤ 2·(A_* − A_R)` (both sides are twice a
triangle area over the base `V_i V_j`). So `growthHalfspace` is exact and
tolerance-free; the tolerance only enters `growableDistance`, which converts
the constraint into an explicit distance and is kept for the blueprint spec.

The main lemma is that any point lying strictly outside the growth
half-space intersection produces a convex hull whose area exceeds `A_*`.
-/

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [DecidableEq K]

namespace ConvexPolygon

/--
The area of the convex polygon `P` lying weakly to the right of the directed
line through vertices `V_i → V_j` (not necessarily adjacent).

Implementation: Sutherland–Hodgman clipping of the (counterclockwise, cyclic)
vertex chain against the closed half-plane weakly to the right of the directed
line `V_i → V_j`, followed by the shoelace formula. For each directed edge
`a → b` of `P` we emit `a` when `a` is weakly right, and the intersection of
`a b` with the line when the edge crosses it. Since `V_i` and `V_j` lie on the
line, the clipped chain is nonempty; when `P` lies weakly left of the line the
clipped chain is degenerate and the area is `0`, as intended.
-/
def areaWeaklyRightOfVertexPair
    (poly : ConvexPolygon K) (i j : Fin poly.vertex_count) (_hij : i ≠ j) : K :=
  let vi := poly.vertices i
  let d := poly.vertices j - vi
  -- signed side: positive strictly left of the directed line, negative strictly right
  let side : Point K → K := fun p => Point.crossProduct d (p - vi)
  let pts := poly.vertex_list
  let clipped := (pts.zip (pts.rotate 1)).flatMap fun ab =>
    let sa := side ab.1
    let sb := side ab.2
    (if sa ≤ 0 then [ab.1] else []) ++
    (if decide (sa ≤ 0) != decide (sb ≤ 0) then
      [ab.1 + (sa / (sa - sb)) • (ab.2 - ab.1)] else [])
  shoelaceArea clipped

/--
The growable distance to the left of the directed line `V_i → V_j` at
tolerance `τ`. This is a nonnegative element `d` such that
`A_R + T(d) ≥ A_*` (where `A_R` is the area of `P` weakly to the right of
the directed line `V_i V_j` and `T(d)` is the area of the triangle with
vertices `V_i, V_j` and a point at perpendicular distance `d` to the left of
the line), and such that `d` is within tolerance `τ` of the unique exact
value `d_*` for which equality `A_R + T(d_*) = A_*` holds.

Implementation: the exact value is `d_* = 2·(A_* − A_R)/L` with `L = |V_i V_j|`
irrational, so we return `2·(A_* − A_R)/L₋` for a rational lower approximation
`L₋ ≤ L` produced by `findRationalWithSquareBetween`, giving `d ≥ d_*` (so
`A_R + T(d) ≥ A_*` errs on the safe side). The approximation window shrinks
with `tolerance` (via the `ratio` factor below) so that the overshoot `d − d_*`
is within the tolerance. When `A_R ≥ A_*` we return `0`.

Specialised to `ℚ` because the lower approximation of the irrational edge
length uses `findRationalWithSquareBetween` (cf. `ClosedHalfSpace.moveInward`).
-/
def growableDistance
    (poly : ConvexPolygon ℚ) (areaThreshold tolerance : ℚ) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) : ℚ :=
  let lenSq := Point.lengthSq (poly.vertices j - poly.vertices i)
  have hlen : 0 < lenSq :=
    Point.lengthSq_pos_of_ne _
      (sub_ne_zero.mpr fun h => hij (poly.nodup h).symm)
  let excess := areaThreshold - areaWeaklyRightOfVertexPair poly i j hij
  if hex : excess ≤ 0 then 0
  else
    have hex' : 0 < excess := lt_of_not_ge hex
    let m := min lenSq 1
    have hm : 0 < m := lt_min hlen one_pos
    let ratio := tolerance * m / (tolerance * m + 2 * excess)
    have hden : 0 < tolerance * m + 2 * excess := by positivity
    have hratio1 : ratio < 1 := by
      rw [div_lt_one hden]
      nlinarith
    have hratio0 : 0 < ratio := by positivity
    2 * excess /
      findRationalWithSquareBetween (lenSq * (1 - ratio)) lenSq
        (by nlinarith) (by nlinarith)

/-- The growable distance is nonnegative. -/
lemma growableDistance_nonneg
    (poly : ConvexPolygon ℚ) (areaThreshold tolerance : ℚ) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) :
    0 ≤ growableDistance poly areaThreshold tolerance htol i j hij := by
  simp only [growableDistance]
  split_ifs with hex
  · exact le_rfl
  · exact le_of_lt (div_pos (by linarith [lt_of_not_ge hex])
      (findRationalWithSquareBetween_positive _ _ _ _))

/--
The growth half-space of the ordered pair of vertices `(V_i, V_j)`: the closed
half-space of points at signed left-distance at most `growableDistance` (as
`tolerance → 0`) from the directed line `V_i → V_j` — that is, the half-space
bounded by the line parallel to `V_i → V_j` at perpendicular distance `d_*` on
its left, lying weakly to the *right* of that shifted line. A point strictly
outside it is so far to the left of `V_i → V_j` that the hull of `P ∪ {p}`
contains, beyond the part of `P` weakly right of the line (area `A_R`), a
triangle over the base `V_i V_j` of height `> d_*`, pushing the area past the
threshold.

The construction is exact and rational (see the module docstring): the
half-space is `{p | crossProduct (V_j − V_i) (p − V_i) ≤ 2·(A_* − A_R)}`,
realized by shifting the basepoint of the weakly-right half-space of
`V_i → V_j` to the left by `(2·excess / |V_i V_j|²) · rot90(V_j − V_i)`.
When `A_R ≥ A_*` the excess is clamped to `0`, giving the half-space weakly
to the right of the directed segment itself (a conservative superset of the
true, empty-interior constraint — always on the safe side for the containment
spec).
-/
def growthHalfspace
    (poly : ConvexPolygon K) (areaThreshold : K)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) : ClosedHalfSpace K :=
  let vi := poly.vertices i
  let vj := poly.vertices j
  let excess := max 0 (areaThreshold - areaWeaklyRightOfVertexPair poly i j hij)
  let leftNormal := Point.rotate90Counterclockwise (vj - vi)
  { basepoint := vi + (2 * excess / Point.lengthSq (vj - vi)) • leftNormal
    normal := Point.rotate90Counterclockwise (vi - vj)
    normal_pos := by
      rw [Point.lengthSq_rotate90Counterclockwise]
      exact Point.lengthSq_pos_of_ne _ (sub_ne_zero.mpr fun h => hij (poly.nodup h)) }

/--
A computable wrapper around `growthHalfspace` that does not depend on a proof
that `i ≠ j`. When `i = j` we return an arbitrary default closed half-space
(the whole-plane representation is not at hand, so we just pick a fixed
half-space to keep this total). This is only used to enumerate the per-pair
half-spaces over `List.finRange poly.vertex_count` without carrying the
`i ≠ j` proof through the iteration.
-/
def growthHalfspaceOfPair
    (poly : ConvexPolygon K) (areaThreshold : K)
    (i j : Fin poly.vertex_count) : ClosedHalfSpace K :=
  if hij : i ≠ j then
    growthHalfspace poly areaThreshold i j hij
  else
    -- Default: a fixed half-space, chosen so the structure is well-formed.
    -- Concretely, the closed half-space `{ p | p₀ ≥ 0 }`.
    { basepoint := ![0, 0]
      normal := ![1, 0]
      normal_pos := by
        unfold Point.lengthSq
        simp }

/--
**Threshold violated outside a growth half-space.**

Let `P` be a convex polygon with vertices in `K`, `A_*` an area
threshold, `τ > 0` a tolerance, and `(V_i, V_j)` an ordered pair of
distinct vertices of `P`. If a point `p` lies strictly outside the
growth half-space to the left of `(V_i, V_j)` associated with `P`, `A_*`,
and `τ`, then the area of the convex hull of `P ∪ {p}` is strictly greater
than `A_*`.

The hypothesis "strictly outside" is encoded as `¬ (growthHalfspace …).contains p`,
i.e. the closed-half-space membership predicate returns `false`.
-/
lemma threshold_violated_outside_growth_halfspace
    (poly : ConvexPolygon K) (areaThreshold : K)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) (p : Point K)
    (hp : ¬ (growthHalfspace poly areaThreshold i j hij).contains p) :
    ∀ hull : ConvexPolygon K,
      ConvexPolygon.ofList (p :: poly.vertex_list) = some hull →
      areaThreshold < hull.area := by
  sorry

/--
The growth half-space intersection associated to `P`, `A_*`, and `τ`: the
convex polygon (if any) obtained by intersecting the per-pair growth
half-spaces over all ordered pairs `(V_i, V_j)` of distinct vertices of `P`.

The pair list is enumerated by iterating `List.finRange poly.vertex_count`
twice and filtering to ordered pairs `i ≠ j`. The resulting list of closed
half-spaces is fed to `ConvexPolygon.ofHalfSpaces`, which returns `none` if
the intersection is degenerate.
-/
def growthHalfspaceIntersection
    (poly : ConvexPolygon K) (areaThreshold : K) :
    Option (ConvexPolygon K) :=
  let indices := List.finRange poly.vertex_count
  let halfSpaces : List (ClosedHalfSpace K) :=
    indices.flatMap (fun i =>
      (indices.filter (fun j => decide (i ≠ j))).map (fun j =>
        growthHalfspaceOfPair poly areaThreshold i j))
  ConvexPolygon.ofHalfSpaces halfSpaces

/--
**Threshold violated outside the growth half-space intersection.**

Let `P` be a convex polygon with vertices in `K`, `A_*` an area
threshold, and `τ > 0` a tolerance. If
`growthHalfspaceIntersection` returns `some intersectionPoly` and a
point `p` lies outside `intersectionPoly`, then the area of the convex hull
of `P ∪ {p}` is strictly greater than `A_*`.
-/
lemma threshold_violated_outside_growth_intersection
    (poly : ConvexPolygon K) (areaThreshold : K)
    (p : Point K) (intersectionPoly : ConvexPolygon K)
    (h_inter : growthHalfspaceIntersection poly areaThreshold
      = some intersectionPoly)
    (hp : ¬ intersectionPoly.contains p) :
    ∀ hull : ConvexPolygon K,
      ConvexPolygon.ofList (p :: poly.vertex_list) = some hull →
      areaThreshold < hull.area := by
  sorry

end ConvexPolygon
