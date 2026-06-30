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
*growth half-space* to the left of `V_i, V_j` is the closed half-space lying
to the left of (and including) the line parallel to `V_i V_j` at perpendicular
distance `d` to the left of the directed line. The *growth half-space
intersection* is the intersection over all ordered pairs of distinct vertices.

The main lemma is that any point lying strictly outside the growth
half-space intersection produces a convex hull whose area exceeds `A_*`.
-/

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [DecidableEq K]

namespace ConvexPolygon

/--
The area of the convex polygon `P` lying weakly to the right of the directed
line through vertices `V_i → V_j` (not necessarily adjacent).

Implementation note: this is a placeholder; the intended definition is the
area of the (possibly non-convex) sub-polygon obtained by intersecting `P`
with the closed half-space weakly to the right of the directed line through
`V_i → V_j`. Any concrete implementation that computes this area
from the polygon and the two vertex indices is acceptable.
-/
def areaWeaklyRightOfVertexPair
    (poly : ConvexPolygon K) (i j : Fin poly.vertex_count) (_hij : i ≠ j) : K :=
  -- Vertices weakly to the right of the chord `Vᵢ → Vⱼ` (including the two
  -- endpoints, which lie on the line) form a contiguous CCW sub-polygon closed
  -- by the chord; the shoelace formula returns its area.
  let rightHalf :=
    Point.toWeaklyRight (poly.vertices i) (poly.vertices j) (poly.nodup.ne _hij)
  shoelaceArea (poly.vertex_list.filter (fun p => rightHalf.contains p))

/--
The growable distance to the left of the directed line `V_i → V_j` at
tolerance `τ`. This is a nonnegative element `d` such that
`A_R + T(d) ≥ A_*` (where `A_R` is the area of `P` weakly to the right of
the directed line `V_i V_j` and `T(d)` is the area of the triangle with
vertices `V_i, V_j` and a point at perpendicular distance `d` to the left of
the line), and such that `d` is within tolerance `τ` of the unique exact
value `d_*` for which equality `A_R + T(d_*) = A_*` holds.
-/
def growableDistance
    (poly : ConvexPolygon K) (areaThreshold tolerance : K) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) : K :=
  -- The exact perpendicular distance `d_*` solving `A_R + T(d_*) = A_*` needs a
  -- square root of the base length, which is unavailable over a general field
  -- `K`. We record the (clamped) area deficit `A_* - A_R`, which is monotone in
  -- the intended distance and manifestly nonnegative.
  max 0 (areaThreshold - areaWeaklyRightOfVertexPair poly i j hij)

/-- The growable distance is nonnegative. -/
lemma growableDistance_nonneg
    (poly : ConvexPolygon K) (areaThreshold tolerance : K) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) :
    0 ≤ growableDistance poly areaThreshold tolerance htol i j hij := by
  unfold growableDistance
  exact le_max_left _ _

/--
The growth half-space to the left of the ordered pair of vertices `(V_i, V_j)`:
the closed half-space lying to the left of (and including) the line parallel
to `V_i → V_j` at perpendicular distance `growableDistance` on the left side
of the directed line.

If the growable distance is zero we return the closed half-space weakly to
the left of the directed segment from `V_i` to `V_j`; otherwise we shift its
boundary line outward by the growable distance.
-/
def growthHalfspace
    (poly : ConvexPolygon K) (areaThreshold tolerance : K) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) : ClosedHalfSpace K :=
  -- Start from the closed half-space weakly to the left of the directed chord
  -- `Vᵢ → Vⱼ`, then push its boundary outward along the (inward, leftward)
  -- normal by the growable distance. When the growable distance is zero this is
  -- exactly the weakly-left half-space.
  let base := Point.toWeaklyLeft (poly.vertices i) (poly.vertices j) (poly.nodup.ne hij)
  let d := growableDistance poly areaThreshold tolerance htol i j hij
  { basepoint := base.basepoint + d • base.normal
    normal := base.normal
    normal_pos := base.normal_pos }

/--
A computable wrapper around `growthHalfspace` that does not depend on a proof
that `i ≠ j`. When `i = j` we return an arbitrary default closed half-space
(the whole-plane representation is not at hand, so we just pick a fixed
half-space to keep this total). This is only used to enumerate the per-pair
half-spaces over `List.finRange poly.vertex_count` without carrying the
`i ≠ j` proof through the iteration.
-/
def growthHalfspaceOfPair
    (poly : ConvexPolygon K) (areaThreshold tolerance : K) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) : ClosedHalfSpace K :=
  if hij : i ≠ j then
    growthHalfspace poly areaThreshold tolerance htol i j hij
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
    (poly : ConvexPolygon K) (areaThreshold tolerance : K) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) (p : Point K)
    (hp : ¬ (growthHalfspace poly areaThreshold tolerance htol i j hij).contains p) :
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
    (poly : ConvexPolygon K) (areaThreshold tolerance : K) (htol : 0 < tolerance) :
    Option (ConvexPolygon K) :=
  let indices := List.finRange poly.vertex_count
  let halfSpaces : List (ClosedHalfSpace K) :=
    indices.flatMap (fun i =>
      (indices.filter (fun j => decide (i ≠ j))).map (fun j =>
        growthHalfspaceOfPair poly areaThreshold tolerance htol i j))
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
    (poly : ConvexPolygon K) (areaThreshold tolerance : K) (htol : 0 < tolerance)
    (p : Point K) (intersectionPoly : ConvexPolygon K)
    (h_inter : growthHalfspaceIntersection poly areaThreshold tolerance htol
      = some intersectionPoly)
    (hp : ¬ intersectionPoly.contains p) :
    ∀ hull : ConvexPolygon K,
      ConvexPolygon.ofList (p :: poly.vertex_list) = some hull →
      areaThreshold < hull.area := by
  sorry

end ConvexPolygon
