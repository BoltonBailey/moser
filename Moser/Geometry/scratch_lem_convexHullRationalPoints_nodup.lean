import Moser.Geometry.HalfSpaces

/-!
# Convex Polygons

This file defines convex polygons as ordered lists of rational vertices.
-/


/--
A polygon represented by its vertices.

we require that all vertices are distinct, and that there are 3 or more vertices.

Operations that would return a degenerate polygon (fewer than 3 vertices) return none instead.

Note we do not extend mathlib's `Polygon`, because we want to bundle the vertex count.
-/
structure NondegenPolygon where
  /--
  The number of vertices in the polygon. -/
  vertex_count : ℕ
  /-- vertex_count must be positive -/
  vertex_count_pos : NeZero vertex_count
  /--
  Vertex count must be at least 3
  -/
  three_le_vertex_count : 3 ≤ vertex_count
  /-- The vertices of the polygon, in counterclockwise order -/
  vertices : Fin vertex_count → RationalPoint
  /-- All vertices are distinct -/
  nodup : Function.Injective vertices
deriving Repr, DecidableEq

attribute [nolint unusedArguments] instReprNondegenPolygon.repr

instance (poly : NondegenPolygon) : NeZero poly.vertex_count := poly.vertex_count_pos

/-- The open half-space strictly to the left of the directed edge from vertex `i` to vertex `i+1`. -/
def NondegenPolygon.getStrictlyLeftHalfspace (ng : NondegenPolygon) (i : Fin ng.vertex_count) :
    OpenHalfSpace :=
  let p1 := ng.vertices i
  let p2 := ng.vertices (i + 1)
  RationalPoint.toStrictlyLeft p1 p2 (by
    intro ne
    have := ng.nodup ne
    have three_le := ng.three_le_vertex_count
    simp_all)



/--
A convex polygon.

Convexity is enforced by the condition that for each edge i→i+1,
all other vertices lie strictly to the left of that edge.

The strictness enforces that there can be no collinear triples of vertices,
which in turn ensures that all vertices are extreme points of the convex hull.
-/
structure ConvexPolygon extends NondegenPolygon where
  /-- For all edges i→i+1, all other vertices lie on or to the left (closed half-space) -/
  vertices_extremeRationalPoints :
    ∀ i j : Fin vertex_count, j ≠ i → j ≠ i + 1 →
      (NondegenPolygon.getStrictlyLeftHalfspace
        ⟨vertex_count, vertex_count_pos, three_le_vertex_count, vertices, nodup⟩ i
      ).contains (vertices j) = true
deriving Repr, DecidableEq

attribute [nolint unusedArguments] instReprConvexPolygon.repr


  -- ∀ i j k : Fin vertex_count,
  --   i < j → j < k →
  --     RationalPoint.ccw (vertices i) (vertices j) (vertices k) = true


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

/-- Lexicographic order on rational points: by `x`-coordinate, breaking ties with `y`. -/
def RationalPoint.lexLE (p q : RationalPoint) : Bool :=
  decide (p 0 < q 0) || (decide (p 0 = q 0) && decide (p 1 ≤ q 1))

/-- Sort a list of rational points lexicographically by `(x, y)`, after first
    dropping duplicates. The dedup step makes the downstream Graham-scan
    invariants and uniqueness proofs go through cleanly. -/
def sortRationalPointsLex (points : List RationalPoint) : List RationalPoint :=
  points.dedup.mergeSort RationalPoint.lexLE

/--
Lower-hull pass of Andrew's monotone chain: fold `grahamScanStep` left over an
already-sorted list. Scanning left-to-right keeps only strict left turns, so the
result is the lower hull in **reverse** traversal order (the rightmost point is
at the head, the leftmost at the tail).
-/
def lowerHullScan (sorted : List RationalPoint) : List RationalPoint :=
  sorted.foldl grahamScanStep []

/--
Upper-hull pass of Andrew's monotone chain: scan the **reverse** of an
already-sorted list. The result is the upper hull in reverse traversal order
(the leftmost point is at the head, the rightmost at the tail).
-/
def upperHullScan (sorted : List RationalPoint) : List RationalPoint :=
  sorted.reverse.foldl grahamScanStep []

/--
Stitch the lower and upper hull scans into a single counterclockwise vertex list.

Each scan is reversed into traversal order, then `dropLast` removes the shared
endpoint where the lower and upper hulls meet, avoiding duplicates. For lists
with fewer than two distinct points the special cases short-circuit.

The upper part is filtered against the lower part to guarantee that the
concatenation has no duplicates, even in degenerate cases where the two hulls
might otherwise share an interior point.
-/
def convexHullFromSorted : List RationalPoint → List RationalPoint
  | [] => []
  | [p] => [p]
  | sorted =>
    let lower := (lowerHullScan sorted).reverse.dropLast
    let upper := (upperHullScan sorted).reverse.dropLast
    lower ++ upper.filter (fun p => decide (p ∉ lower))

/--
Compute the convex hull of a list of points using a Graham-scan-like algorithm.
Should return a list of vertices such that:

- All points in the returned list are in the input list (no new points).
- The returned list has no duplicates.
- The returned list starts with the lowest x-coordinate point
  (lowest y-coordinate to tiebreak)
  and then goes  in counterclockwise order.
- All input points are in the convex hull defined by the returned vertices.
- The returned vertices are extreme points of the convex hull
  (no vertex is a convex combination of others).

Implementation: lex-sort the points, then stitch the two monotone-chain scans
together via `convexHullFromSorted`. Consecutive duplicates in the sorted list
are absorbed by `grahamScanStep`, since `RationalPoint.ccw` is strict and
returns `false` whenever two of its arguments coincide.
-/
def convexHullRationalPoints (points : List RationalPoint) : List RationalPoint :=
  convexHullFromSorted (sortRationalPointsLex points)

lemma grahamScanStep_sublist (stack : List RationalPoint) (p : RationalPoint) :
    (grahamScanStep stack p).Sublist (p :: stack) := by
  match stack with
  | [] => simp [grahamScanStep]
  | [q] => simp [grahamScanStep]
  | q :: r :: rest =>
    unfold grahamScanStep
    split_ifs with h
    · exact List.Sublist.refl _
    · have ih := grahamScanStep_sublist (r :: rest) p
      -- ih : (grahamScanStep (r :: rest) p).Sublist (p :: r :: rest)
      -- Goal: (grahamScanStep (r :: rest) p).Sublist (p :: q :: r :: rest)
      refine ih.trans ?_
      exact (List.sublist_cons_self q (r :: rest)).cons_cons p
termination_by stack.length

lemma foldl_grahamScanStep_sublist (l acc : List RationalPoint) :
    (l.foldl grahamScanStep acc).Sublist (l.reverse ++ acc) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append]
    -- Goal: (xs.foldl grahamScanStep (grahamScanStep acc x)).Sublist
    --   (xs.reverse ++ (x :: acc))
    have step : (grahamScanStep acc x).Sublist (x :: acc) := grahamScanStep_sublist acc x
    have ih_inst := ih (grahamScanStep acc x)
    -- ih_inst : (xs.foldl grahamScanStep (grahamScanStep acc x)).Sublist
    --     (xs.reverse ++ grahamScanStep acc x)
    refine ih_inst.trans ?_
    exact List.Sublist.append_left step xs.reverse

lemma lowerHullScan_sublist (sorted : List RationalPoint) :
    (lowerHullScan sorted).Sublist sorted.reverse := by
  unfold lowerHullScan
  have := foldl_grahamScanStep_sublist sorted []
  simpa using this

lemma upperHullScan_sublist (sorted : List RationalPoint) :
    (upperHullScan sorted).Sublist sorted := by
  unfold upperHullScan
  have h := foldl_grahamScanStep_sublist sorted.reverse []
  rw [List.reverse_reverse] at h
  simpa using h

lemma sortRationalPointsLex_nodup (points : List RationalPoint) :
    (sortRationalPointsLex points).Nodup := by
  unfold sortRationalPointsLex
  have hperm : (points.dedup.mergeSort RationalPoint.lexLE).Perm points.dedup :=
    List.mergeSort_perm points.dedup RationalPoint.lexLE
  exact hperm.symm.nodup (List.nodup_dedup points)

lemma convexHullFromSorted_nodup {sorted : List RationalPoint} (h : sorted.Nodup) :
    (convexHullFromSorted sorted).Nodup := by
  match sorted, h with
  | [], _ => simp [convexHullFromSorted]
  | [p], _ => simp [convexHullFromSorted]
  | p :: q :: rest, h =>
    unfold convexHullFromSorted
    set L := p :: q :: rest with hL
    have hL_nodup : L.Nodup := h
    have hL_rev_nodup : L.reverse.Nodup := hL_nodup.reverse
    -- lower = (lowerHullScan L).reverse.dropLast
    have lower_sub_rev : (lowerHullScan L).Sublist L.reverse := lowerHullScan_sublist L
    have lower_rev_sub : (lowerHullScan L).reverse.Sublist L.reverse.reverse :=
      lower_sub_rev.reverse
    have lower_rev_sub' : (lowerHullScan L).reverse.Sublist L := by
      rw [List.reverse_reverse] at lower_rev_sub; exact lower_rev_sub
    have lower_dropLast_sub : (lowerHullScan L).reverse.dropLast.Sublist L :=
      (List.dropLast_sublist _).trans lower_rev_sub'
    have lower_nodup : ((lowerHullScan L).reverse.dropLast).Nodup :=
      lower_dropLast_sub.nodup hL_nodup
    -- upper = (upperHullScan L).reverse.dropLast
    have upper_sub : (upperHullScan L).Sublist L := upperHullScan_sublist L
    have upper_rev_sub : (upperHullScan L).reverse.Sublist L.reverse := upper_sub.reverse
    have upper_dropLast_sub : (upperHullScan L).reverse.dropLast.Sublist L.reverse :=
      (List.dropLast_sublist _).trans upper_rev_sub
    have upper_nodup : ((upperHullScan L).reverse.dropLast).Nodup :=
      upper_dropLast_sub.nodup hL_rev_nodup
    set lower := (lowerHullScan L).reverse.dropLast with hlower
    set upper := (upperHullScan L).reverse.dropLast with hupper
    have filt_nodup : (upper.filter (fun p => decide (p ∉ lower))).Nodup :=
      upper_nodup.filter _
    refine List.Nodup.append lower_nodup filt_nodup ?_
    intro x hx_lower hx_filt
    rw [List.mem_filter] at hx_filt
    obtain ⟨_, hx_not⟩ := hx_filt
    simp at hx_not
    exact hx_not hx_lower

lemma convexHullRationalPoints_nodup (points : List RationalPoint) :
    (convexHullRationalPoints points).Nodup := by
  unfold convexHullRationalPoints
  exact convexHullFromSorted_nodup (sortRationalPointsLex_nodup points)

-- lemma convexHullRationalPoints_extreme (points : List RationalPoint) :
--     (convexHullRationalPoints points).All (fun v =>
--       ¬(convexHullRationalPoints points).Any (fun w => w ≠ v && RationalPoint.isStrictlyLeftOf w v (convexHullRationalPoints points.head))) := by
--   sorry

/--
Construct a ConvexPolygon from a list of points by removing duplicates
    and keeping only extreme points of the convex hull.
    returns none if there are fewer than 3 extreme points. -/
def ConvexPolygon.ofList (vertices : List RationalPoint) : Option ConvexPolygon := sorry

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
  (ConvexPolygon.ofList vertices)

/-- Decide whether the point `p` lies in the convex polygon `poly`. -/
def ConvexPolygon.contains (poly : ConvexPolygon) (p : RationalPoint) : Bool :=
  match poly.toHalfSpaces with
  | none => false
  | some halfSpaces => halfSpaces.all (fun h => h.contains p)

/-- Decide whether every vertex of `p` lies in `q`, witnessing `p ⊆ q` for convex polygons. -/
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
