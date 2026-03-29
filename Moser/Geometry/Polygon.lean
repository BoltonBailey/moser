import Moser.Geometry.HalfSpaces

/-!
# Convex Polygons

This file defines convex polygons as ordered lists of rational vertices.
-/

/-- A convex polygon represented by its vertices in counterclockwise order.
We allow degenerate polygons of 0, 1, or 2 vertices,
but require that all vertices are distinct,
and in counterclockwise order for 3 or more vertices.
-/
structure ConvexPolygon where
  vertex_count : ℕ
  /-- The vertices of the polygon in counterclockwise order -/
  vertices : Fin vertex_count → RationalPoint
  /-- All vertices are distinct -/
  nodup : Function.Injective vertices
  /-- Counterclockwise -/
  vertices_extremeRationalPoints : ∀ i j k : Fin vertex_count,
    i < j → j < k →
      RationalPoint.ccw (vertices i) (vertices j) (vertices k) = true
deriving Repr, DecidableEq

/--
The vertex list of a convex polygon, in counterclockwise order.
-/
def ConvexPolygon.vertex_list (poly : ConvexPolygon) : List RationalPoint :=
  List.finRange poly.vertex_count |>.map poly.vertices


/-- Graham scan helper: process remaining points to build upper/lower hull -/
def grahamScanStep (stack : List RationalPoint) (p : RationalPoint) : List RationalPoint :=
  match stack with
  | [] => [p]
  | [q] => [p, q]
  | q :: r :: rest =>
    if RationalPoint.ccw r q p then p :: stack
    else grahamScanStep (r :: rest) p

/--
Compute the convex hull of a list of points using a Graham-scan-like algorithm.
Should return a list of vertices such that:

- All points in the returned list are in the input list (no new points).
- The returned list has no duplicates.
- The returned list is in counterclockwise order.
- All input points are in the convex hull defined by the returned vertices.
- The returned vertices are extreme points of the convex hull
  (no vertex is a convex combination of others).
-/
def convexHullRationalPoints (points : List RationalPoint) : List RationalPoint :=
  if points.length ≤ 1 then points
  else
    -- Sort by x-coordinate, then y-coordinate
    let sorted := points.mergeSort (fun p q => p 0 < q 0 || (p 0 == q 0 && p 1 ≤ q 1))
    -- Build lower hull (left to right)
    let lower := sorted.foldl grahamScanStep []
    -- Build upper hull (right to left)
    let upper := sorted.reverse.foldl grahamScanStep []
    -- Combine, removing duplicate endpoints
    match lower.reverse, upper.reverse with
    | [], u => u
    | l, [] => l
    | l, u => l ++ u.tail

lemma convexHullRationalPoints_nodup (points : List RationalPoint) :
    (convexHullRationalPoints points).Nodup := by
  sorry

-- lemma convexHullRationalPoints_extreme (points : List RationalPoint) :
--     (convexHullRationalPoints points).All (fun v =>
--       ¬(convexHullRationalPoints points).Any (fun w => w ≠ v && RationalPoint.isStrictlyLeftOf w v (convexHullRationalPoints points.head))) := by
--   sorry

/-- Construct a ConvexPolygon from a list of points by removing duplicates
    and keeping only extreme points of the convex hull. -/
def ConvexPolygon.ofList (vertices : List RationalPoint) : ConvexPolygon where
  vertex_count := (convexHullRationalPoints vertices).length
  vertices := fun i => (convexHullRationalPoints vertices).get ⟨i, by omega⟩
  nodup := by
    have : (convexHullRationalPoints vertices).Nodup := by
      exact convexHullRationalPoints_nodup vertices
    apply List.Nodup.injective_get this
  vertices_extremeRationalPoints := by
    sorry

/--
Returns a list of closed half-spaces corresponding to the edges of the convex polygon.
If there are fewer than 3 vertices, returns none.
-/
def ConvexPolygon.toHalfSpaces (poly : ConvexPolygon) : Option (List ClosedHalfSpace) :=
  if h : poly.vertex_count < 3 then none
  else
    let edges := List.finRange poly.vertex_count
    let halfSpaces := edges.map (fun i =>
      let p1 := poly.vertices i
      let p2 := poly.vertices (i + ⟨1, by omega⟩)
      RationalPoint.toWeaklyLeft p1 p2 (poly.nodup.ne (Fin.ext_iff.not.mpr (by
        simp only [Fin.val_add]
        have hi := i.isLt
        rcases Nat.lt_or_ge (i.val + 1) poly.vertex_count with h1 | h1
        · rw [Nat.mod_eq_of_lt h1]; omega
        · have : i.val + 1 = poly.vertex_count := by omega
          rw [this, Nat.mod_self]; omega))))
    some halfSpaces

/--
Given a collection of half-spaces, construct the convex polygon defined by their intersection.
This is determined by taking all intersections of the boundary lines of pairs of half-spaces,
and then filtering to those that satisfy all half-space constraints.
-/
def ConvexPolygon.ofHalfSpaces (halfSpaces : List ClosedHalfSpace) : Option ConvexPolygon :=
  let potentialVertices := halfSpaces.flatMap (fun h1 =>
    halfSpaces.filterMap (fun h2 => ClosedHalfSpace.lineIntersection h1 h2))
  let vertices := potentialVertices.filter (fun v => halfSpaces.all (fun h => h.contains v))
  some (ConvexPolygon.ofList vertices)

def ConvexPolygon.contains (poly : ConvexPolygon) (p : RationalPoint) : Bool :=
  match poly.toHalfSpaces with
  | none => false
  | some halfSpaces => halfSpaces.all (fun h => h.contains p)

def ConvexPolygon.isSubsetOf (p q : ConvexPolygon) : Bool :=
  p.vertex_list.all (fun v => q.contains v)

namespace ConvexPolygon

/-- Shrink a convex polygon by moving each edge inward
by at least `dist` (in the normal direction).
and at most `dist + tolerance` (to account for numerical issues).
-/
def shrink (poly : ConvexPolygon) (dist : ℚ) (tolerance : ℚ) (hdist : 0 < dist) (htol : 0 < tolerance) :
    Option ConvexPolygon :=
  let halfSpaces := poly.toHalfSpaces
  match halfSpaces with
  | none => none
  | some hs =>
    let movedHalfSpaces := hs.map (fun h => h.moveInward dist tolerance hdist htol)
    (ConvexPolygon.ofHalfSpaces movedHalfSpaces)

end ConvexPolygon
