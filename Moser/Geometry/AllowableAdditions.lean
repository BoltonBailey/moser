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
distance* `d`: a rational number, within tolerance `τ` of the unique exact
value `d_*` for which `A_R + T(d_*) = A_*`, where

* `A_R` is the area of `P` weakly to the right of the directed line `V_i → V_j`,
* `T(d)` is the area of the triangle with base `V_i V_j` and height `d`.

Equivalently, the area of the convex hull of `P ∪ {p}` where `p` is at
left-distance `d_*` from the directed line `V_i V_j` equals `A_*`. The
*growth half-space* to the left of `V_i, V_j` is the closed half-space lying
to the left of (and including) the line parallel to `V_i V_j` at perpendicular
distance `d` to the left of the directed line. The *growth half-space
intersection* is the intersection over all ordered pairs of distinct vertices.

The main lemma is that any rational point lying strictly outside the growth
half-space intersection produces a convex hull whose area exceeds `A_*`.
-/

namespace ConvexPolygon

/--
The area of the convex polygon `P` lying weakly to the right of the directed
line through vertices `V_i → V_j` (not necessarily adjacent).

Implementation note: this is a placeholder; the intended definition is the
area of the (possibly non-convex) sub-polygon obtained by intersecting `P`
with the closed half-space weakly to the right of the directed line through
`V_i → V_j`. Any concrete implementation that computes this rational area
from the polygon and the two vertex indices is acceptable.
-/
noncomputable def areaWeaklyRightOfVertexPair
    (poly : ConvexPolygon) (i j : Fin poly.vertex_count) (_hij : i ≠ j) : ℚ :=
  sorry

/--
The growable distance to the left of the directed line `V_i → V_j` at
tolerance `τ`. This is a nonnegative rational number `d` such that
`A_R + T(d) ≥ A_*` (where `A_R` is the area of `P` weakly to the right of
the directed line `V_i V_j` and `T(d)` is the area of the triangle with
vertices `V_i, V_j` and a point at perpendicular distance `d` to the left of
the line), and such that `d` is within tolerance `τ` of the unique exact
value `d_*` for which equality `A_R + T(d_*) = A_*` holds.
-/
noncomputable def growableDistance
    (poly : ConvexPolygon) (areaThreshold tolerance : ℚ) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) : ℚ :=
  sorry

/-- The growable distance is nonnegative. -/
lemma growableDistance_nonneg
    (poly : ConvexPolygon) (areaThreshold tolerance : ℚ) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) :
    0 ≤ growableDistance poly areaThreshold tolerance htol i j hij := by
  sorry

/--
The growth half-space to the left of the ordered pair of vertices `(V_i, V_j)`:
the closed half-space lying to the left of (and including) the line parallel
to `V_i → V_j` at perpendicular distance `growableDistance` on the left side
of the directed line.

If the growable distance is zero we return the closed half-space weakly to
the left of the directed segment from `V_i` to `V_j`; otherwise we shift its
boundary line outward by the growable distance.
-/
noncomputable def growthHalfspace
    (poly : ConvexPolygon) (areaThreshold tolerance : ℚ) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) : ClosedHalfSpace :=
  sorry

/--
**Threshold violated outside a growth half-space.**

Let `P` be a convex polygon with rational vertices, `A_*` a rational area
threshold, `τ > 0` a rational tolerance, and `(V_i, V_j)` an ordered pair of
distinct vertices of `P`. If a rational point `p` lies strictly outside the
growth half-space to the left of `(V_i, V_j)` associated with `P`, `A_*`,
and `τ`, then the area of the convex hull of `P ∪ {p}` is strictly greater
than `A_*`.

The hypothesis "strictly outside" is encoded as `¬ (growthHalfspace …).contains p`,
i.e. the closed-half-space membership predicate returns `false`.
-/
lemma threshold_violated_outside_growth_halfspace
    (poly : ConvexPolygon) (areaThreshold tolerance : ℚ) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) (p : RationalPoint)
    (hp : ¬ (growthHalfspace poly areaThreshold tolerance htol i j hij).contains p) :
    ∀ hull : ConvexPolygon,
      ConvexPolygon.ofList (p :: poly.vertex_list) = some hull →
      areaThreshold < hull.area := by
  sorry

/--
The growth half-space intersection associated to `P`, `A_*`, and `τ`: the
set of rational points `p` such that for every ordered pair `(V_i, V_j)` of
distinct vertices of `P`, the point `p` lies in the growth half-space to the
left of `(V_i, V_j)`.
-/
noncomputable def growthHalfspaceIntersection
    (poly : ConvexPolygon) (areaThreshold tolerance : ℚ) (htol : 0 < tolerance) :
    Set RationalPoint :=
  { p | ∀ (i j : Fin poly.vertex_count) (hij : i ≠ j),
      (growthHalfspace poly areaThreshold tolerance htol i j hij).contains p }

/--
**Threshold violated outside the growth half-space intersection.**

Let `P` be a convex polygon with rational vertices, `A_*` a rational area
threshold, and `τ > 0` a rational tolerance. If a rational point `p` lies
outside the growth half-space intersection of `P`, `A_*`, and `τ`, then the
area of the convex hull of `P ∪ {p}` is strictly greater than `A_*`.
-/
lemma threshold_violated_outside_growth_intersection
    (poly : ConvexPolygon) (areaThreshold tolerance : ℚ) (htol : 0 < tolerance)
    (p : RationalPoint)
    (hp : p ∉ growthHalfspaceIntersection poly areaThreshold tolerance htol) :
    ∀ hull : ConvexPolygon,
      ConvexPolygon.ofList (p :: poly.vertex_list) = some hull →
      areaThreshold < hull.area := by
  sorry

end ConvexPolygon
