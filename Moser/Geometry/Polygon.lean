import Mathlib
import Moser.Geometry.Point

/-!
# Convex Polygons

This file defines convex polygons as ordered lists of rational vertices.
-/

namespace Moser

/-- A convex polygon represented by its vertices in counterclockwise order.
    Empty list = empty set, single point = point, two points = line segment,
    three or more = polygon -/
structure ConvexPolygon where
  /-- The vertices of the polygon in counterclockwise order -/
  vertices : List Point
  /-- All vertices are distinct -/
  nodup : vertices.Nodup
  /-- Each vertex is an extreme point of the convex hull -/
  vertices_extremePoints : ∀ v ∈ vertices,
    Point.toReal v ∈ (convexHull ℝ (Point.toReal '' vertices.toFinset)).extremePoints ℝ

/-- Check if a point is strictly to the left of the directed line from p1 to p2.
    Uses the cross product: positive means left, negative means right, zero means collinear. -/
def isLeftOf (p p1 p2 : Point) : Bool :=
  Point.crossProduct (p2 - p1) (p - p1) > 0

/-- Check if three points are in counterclockwise order -/
def ccw (p1 p2 p3 : Point) : Bool := isLeftOf p3 p1 p2

/-- Graham scan helper: process remaining points to build upper/lower hull -/
def grahamScanStep (stack : List Point) (p : Point) : List Point :=
  match stack with
  | [] => [p]
  | [q] => [p, q]
  | q :: r :: rest =>
    if ccw r q p then p :: stack
    else grahamScanStep (r :: rest) p

/-- Elements of grahamScanStep output are either p or from the stack -/
theorem grahamScanStep_subset (stack : List Point) (p : Point) :
    ∀ x ∈ grahamScanStep stack p, x = p ∨ x ∈ stack := by
  match stack with
  | [] =>
    intro x hx
    simp only [grahamScanStep, List.mem_singleton] at hx
    left; exact hx
  | [q] =>
    intro x hx
    simp only [grahamScanStep, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hp | hq
    · left; exact hp
    · right; simp only [List.mem_singleton]; exact hq
  | q :: r :: tail =>
    intro x hx
    simp only [grahamScanStep] at hx
    split_ifs at hx with h
    · simp only [List.mem_cons] at hx ⊢
      rcases hx with hp | hx'
      · left; exact hp
      · right; exact hx'
    · have ih := grahamScanStep_subset (r :: tail) p x hx
      rcases ih with hp | hx''
      · left; exact hp
      · right
        exact List.mem_cons_of_mem q hx''
termination_by stack.length

/-- Folding grahamScanStep over a list produces elements from that list -/
theorem foldl_grahamScanStep_subset (init : List Point) (points : List Point) :
    ∀ x ∈ (points.foldl grahamScanStep init), x ∈ init ∨ x ∈ points := by
  induction points generalizing init with
  | nil =>
    intro x hx
    simp only [List.foldl_nil] at hx
    left; exact hx
  | cons p rest ih =>
    intro x hx
    simp only [List.foldl_cons] at hx
    have ih' := ih (grahamScanStep init p) x hx
    rcases ih' with h | h
    · have := grahamScanStep_subset init p x h
      rcases this with rfl | h'
      · right; simp
      · left; exact h'
    · right; simp [h]

/-- Compute the convex hull of a list of points using a Graham-scan-like algorithm.
    Returns vertices in counterclockwise order. -/
def convexHullPoints (points : List Point) : List Point :=
  if points.length ≤ 1 then points
  else
    -- Sort by x-coordinate, then y-coordinate
    let sorted := points.mergeSort (fun p q => p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2))
    -- Build lower hull (left to right)
    let lower := sorted.foldl grahamScanStep []
    -- Build upper hull (right to left)
    let upper := sorted.reverse.foldl grahamScanStep []
    -- Combine, removing duplicate endpoints
    match lower.reverse, upper.reverse with
    | [], u => u
    | l, [] => l
    | l, u => l ++ u.tail

/-- The convex hull algorithm outputs are a subset of the input -/
theorem convexHullPoints_subset (points : List Point) :
    ∀ p ∈ convexHullPoints points, p ∈ points := by
  intro p hp
  unfold convexHullPoints at hp
  split_ifs at hp with h
  · exact hp
  · -- The algorithm only outputs points from the sorted list, which is a permutation of input
    simp only at hp
    generalize hS : points.mergeSort
      (fun p q => p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2)) = sorted at hp
    generalize hL : sorted.foldl grahamScanStep [] = lower at hp
    generalize hU : sorted.reverse.foldl grahamScanStep [] = upper at hp
    have hsorted : sorted.Perm points := hS ▸ List.mergeSort_perm _ _
    have hlower : ∀ x ∈ lower, x ∈ sorted := fun x hx => by
      rw [← hL] at hx
      have := foldl_grahamScanStep_subset [] sorted x hx
      simp only [List.not_mem_nil, false_or] at this
      exact this
    have hupper : ∀ x ∈ upper, x ∈ sorted := fun x hx => by
      rw [← hU] at hx
      have := foldl_grahamScanStep_subset [] sorted.reverse x hx
      simp only [List.not_mem_nil, false_or] at this
      rw [List.mem_reverse] at this
      exact this
    -- The result is from lower.reverse, upper.reverse, or their combination
    rcases hl : lower.reverse with _ | ⟨lh, lt⟩
    · simp only [hl] at hp
      have hp' : p ∈ upper := by rw [← List.mem_reverse]; exact hp
      exact hsorted.mem_iff.mp (hupper p hp')
    · rcases hu : upper.reverse with _ | ⟨uh, ut⟩
      · simp only [hl, hu] at hp
        have hp' : p ∈ lower := by rw [← List.mem_reverse, hl]; exact hp
        exact hsorted.mem_iff.mp (hlower p hp')
      · simp only [hl, hu, List.mem_append] at hp
        rcases hp with hpl | hpu
        · have hp' : p ∈ lower := by rw [← List.mem_reverse, hl]; exact hpl
          exact hsorted.mem_iff.mp (hlower p hp')
        · have htail : p ∈ upper.reverse := by rw [hu]; exact List.mem_of_mem_tail hpu
          have hp' : p ∈ upper := by rw [← List.mem_reverse]; exact htail
          exact hsorted.mem_iff.mp (hupper p hp')

/-- grahamScanStep produces a nodup list when stack is nodup and p is not in stack -/
theorem grahamScanStep_nodup (stack : List Point) (p : Point)
    (hstack : stack.Nodup) (hp : p ∉ stack) :
    (grahamScanStep stack p).Nodup := by
  match stack with
  | [] => simp [grahamScanStep]
  | [q] =>
    simp only [grahamScanStep, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true]
    intro heq
    exact hp (heq ▸ List.mem_singleton_self q)
  | q :: r :: tail =>
    simp only [grahamScanStep]
    split_ifs with h
    · rw [List.nodup_cons]
      exact ⟨hp, hstack⟩
    · apply grahamScanStep_nodup
      · exact (List.nodup_cons.mp hstack).2
      · intro hmem
        apply hp
        exact List.mem_cons_of_mem q hmem
termination_by stack.length

/-- Folding grahamScanStep preserves nodup when stack and points are disjoint and nodup -/
theorem foldl_grahamScanStep_nodup' (init : List Point) (points : List Point)
    (hinit : init.Nodup) (hpoints : points.Nodup)
    (hdisjoint : ∀ x ∈ init, x ∉ points) :
    (points.foldl grahamScanStep init).Nodup := by
  induction points generalizing init with
  | nil => simp [hinit]
  | cons p rest ih =>
    simp only [List.foldl_cons]
    have hrest : rest.Nodup := (List.nodup_cons.mp hpoints).2
    have hp_not_in_rest : p ∉ rest := (List.nodup_cons.mp hpoints).1
    have hp_not_in_init : p ∉ init := fun h => hdisjoint p h List.mem_cons_self
    have hstep_nodup : (grahamScanStep init p).Nodup :=
      grahamScanStep_nodup init p hinit hp_not_in_init
    apply ih (grahamScanStep init p) hstep_nodup hrest
    intro x hx hx_rest
    have := grahamScanStep_subset init p x hx
    rcases this with rfl | hx_init
    · exact hp_not_in_rest hx_rest
    · exact hdisjoint x hx_init (List.mem_cons_of_mem p hx_rest)

/-- Folding grahamScanStep preserves nodup when elements are distinct -/
theorem foldl_grahamScanStep_nodup (points : List Point) (hpoints : points.Nodup) :
    (points.foldl grahamScanStep []).Nodup := by
  apply foldl_grahamScanStep_nodup' [] points List.nodup_nil hpoints
  intro x hx
  simp at hx

/-- The convex hull algorithm produces a list with no duplicates when input has no duplicates -/
theorem convexHullPoints_nodup (points : List Point) (h : points.Nodup) :
    (convexHullPoints points).Nodup := by
  unfold convexHullPoints
  split_ifs with hlen
  · exact h
  · -- The sorted list is a permutation of points, hence nodup
    have hsorted_nodup : (points.mergeSort
        (fun p q => p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2))).Nodup := by
      have hperm := List.mergeSort_perm points
        (fun p q => p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2))
      exact hperm.nodup_iff.mpr h
    set sorted := points.mergeSort
        (fun p q => p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2)) with hs
    have hlower_nodup : (sorted.foldl grahamScanStep []).Nodup :=
      foldl_grahamScanStep_nodup sorted hsorted_nodup
    have hupper_nodup : (sorted.reverse.foldl grahamScanStep []).Nodup := by
      apply foldl_grahamScanStep_nodup
      exact List.nodup_reverse.mpr hsorted_nodup
    -- Simplify the have bindings away
    change (match (sorted.foldl grahamScanStep []).reverse,
               (sorted.reverse.foldl grahamScanStep []).reverse with
          | [], u => u
          | l, [] => l
          | l, u => l ++ u.tail).Nodup
    -- Now analyze the match by splitting on the structure of reversed hulls
    split
    next => -- lower.reverse = []
      exact List.nodup_reverse.mpr hupper_nodup
    next _ _ heq _ => -- lower.reverse non-empty, upper.reverse = []
      exact List.nodup_reverse.mpr hlower_nodup
    next => -- Both non-empty: need to show (l ++ u.tail).Nodup
      -- TODO: This requires showing lower.reverse and upper.reverse.tail are disjoint.
      -- The lower hull contains points going counterclockwise from leftmost to rightmost
      -- along the "bottom". The upper hull goes from rightmost to leftmost along the "top".
      -- By removing the head of upper.reverse (which is the rightmost point, shared with
      -- lower), we avoid that duplicate. However, proving the remaining points are disjoint
      -- requires geometric reasoning about the CCW ordering invariants of Graham scan.
      sorry

/-- Each point in convexHullPoints output is an extreme point of the convex hull -/
theorem convexHullPoints_extremePoints (points : List Point) (h : points.Nodup) :
    ∀ v ∈ convexHullPoints points,
      Point.toReal v ∈
        (convexHull ℝ (Point.toReal '' (convexHullPoints points).toFinset)).extremePoints ℝ := by
  intro v hv
  -- TODO: Prove that Graham scan only outputs extreme points.
  -- This requires showing that each output vertex cannot be written as a strict convex
  -- combination of other output vertices. The key insight is that the CCW test in
  -- grahamScanStep ensures we only keep "corner" points where the boundary turns left.
  -- Formally, use `mem_extremePoints_iff_forall_segment` and the geometric properties
  -- of the algorithm.
  sorry

/-- The convex hull of the output equals the convex hull of the input -/
theorem convexHullPoints_convexHull (points : List Point) :
    convexHull ℝ (Point.toReal '' (convexHullPoints points).toFinset) =
    convexHull ℝ (Point.toReal '' points.toFinset) := by
  -- TODO: Prove Graham scan correctness.
  -- The ⊆ direction follows from convexHullPoints_subset and monotonicity of convexHull.
  -- The ⊇ direction requires showing every input point is in the convex hull of the output.
  -- This follows from the fact that the algorithm only removes interior points, keeping
  -- all extreme points. Use `convexHull_mono` for ⊆ and prove that discarded points
  -- lie in the interior of the triangle formed by their neighbors on the hull.
  sorry

/-- Filter a list to keep only points that are on the convex hull boundary -/
def filterToExtremePoints (points : List Point) : List Point :=
  let hull := convexHullPoints points
  points.filter (fun p => hull.contains p)

/-- Filtering preserves Nodup -/
theorem filterToExtremePoints_nodup (points : List Point) (h : points.Nodup) :
    (filterToExtremePoints points).Nodup :=
  List.Nodup.filter _ h

/-- Construct a ConvexPolygon from a list of points by removing duplicates
    and keeping only extreme points of the convex hull. -/
def ConvexPolygon.ofList (vertices : List Point) : ConvexPolygon :=
  let deduped := vertices.dedup
  let extreme := filterToExtremePoints deduped
  let hull := convexHullPoints extreme
  have h_dedup_nodup : deduped.Nodup := List.nodup_dedup vertices
  have h_extreme_nodup : extreme.Nodup := filterToExtremePoints_nodup deduped h_dedup_nodup
  { vertices := hull
    nodup := convexHullPoints_nodup extreme h_extreme_nodup
    vertices_extremePoints := convexHullPoints_extremePoints extreme h_extreme_nodup
  }


namespace ConvexPolygon

/-- Convert a polygon to a set in ℝ² via convex hull -/
def toSet (poly : ConvexPolygon) : Set (ℝ × ℝ) :=
  convexHull ℝ (Set.range (fun i : Fin poly.vertices.length =>
    Point.toReal (poly.vertices.get ⟨i, by omega⟩)))

/-- Get the edges of the polygon as pairs of consecutive vertices -/
def edges (poly : ConvexPolygon) : List (Point × Point) :=
  match poly.vertices with
  | [] => []
  | [_] => []
  | h :: t => List.zipWith (fun p q => (p, q)) poly.vertices (t ++ [h])

/-- Compute the inward-facing unit normal for an edge (p1, p2) of a CCW polygon.
    The inward normal points to the right of the edge direction. -/
def edgeInwardNormal (p1 p2 : Point) : ℚ × ℚ :=
  let dx := p2.1 - p1.1
  let dy := p2.2 - p1.2
  let lenSq := dx * dx + dy * dy
  if lenSq = 0 then (0, 0)
  else (dy / lenSq, -dx / lenSq)  -- Normalized perpendicular (pointing inward for CCW)

/-- Move a point along a direction by a scalar factor -/
def movePoint (p : Point) (dir : ℚ × ℚ) (dist : ℚ) : Point :=
  (p.1 + dist * dir.1, p.2 + dist * dir.2)

/-- Compute intersection of two lines, each given by a point and direction.
    Returns None if lines are parallel. -/
def lineIntersection (p1 : Point) (d1 : ℚ × ℚ) (p2 : Point) (d2 : ℚ × ℚ) : Option Point :=
  let cross := d1.1 * d2.2 - d1.2 * d2.1
  if cross = 0 then none
  else
    let dx := p2.1 - p1.1
    let dy := p2.2 - p1.2
    let t := (dx * d2.2 - dy * d2.1) / cross
    some (p1.1 + t * d1.1, p1.2 + t * d1.2)

/-- Shrink a convex polygon by moving each edge inward by the given distance.
    Returns None if the polygon degenerates (edges intersect improperly).
    For a convex polygon with CCW vertices, positive distance shrinks inward. -/
def shrink (poly : ConvexPolygon) (dist : ℚ) : Option ConvexPolygon :=
  match poly.vertices with
  | [] => some poly
  | [_] => some poly  -- Single point, can't shrink
  | [_, _] => some poly  -- Line segment, can't shrink properly
  | _ :: _ :: _ :: _ =>
    -- Get edges as pairs with their directions and inward normals
    let edges := poly.edges
    -- Move each edge inward: compute moved edge line (point + direction)
    let movedEdges := edges.map fun (p1, p2) =>
      let normal := edgeInwardNormal p1 p2
      let newP1 := movePoint p1 normal dist
      let dir := (p2.1 - p1.1, p2.2 - p1.2)
      (newP1, dir)
    -- Compute new vertices as intersections of consecutive moved edges
    let n := movedEdges.length
    let newVerts := List.range n |>.filterMap fun i =>
      let e1 := movedEdges.getD i ((0, 0), (1, 0))
      let e2 := movedEdges.getD ((i + 1) % n) ((0, 0), (1, 0))
      lineIntersection e1.1 e1.2 e2.1 e2.2
    -- Check that we got all vertices
    if newVerts.length = n then
      some (ConvexPolygon.ofList newVerts)
    else
      none

/-- The area of a shrunk polygon is less than or equal to the original -/
theorem shrink_area_le (poly : ConvexPolygon) (dist : ℚ) (hdist : 0 < dist)
    (hpoly : poly.vertices.length ≥ 3) :
    ∀ shrunk, poly.shrink dist = some shrunk →
      MeasureTheory.volume shrunk.toSet ≤ MeasureTheory.volume poly.toSet := by
  -- TODO: Prove that shrinking a polygon decreases its area.
  -- The shrunk polygon is contained in the original (each edge moved inward),
  -- so this follows from monotonicity of Lebesgue measure: shrunk.toSet ⊆ poly.toSet
  -- implies volume shrunk.toSet ≤ volume poly.toSet.
  -- First prove the containment, then apply MeasureTheory.measure_mono.
  sorry

/-- Points in a shrunk polygon are at least `dist` away from the boundary of the original -/
theorem shrink_interior_dist (poly : ConvexPolygon) (dist : ℚ) (hdist : 0 < dist)
    (hpoly : poly.vertices.length ≥ 3) :
    ∀ shrunk, poly.shrink dist = some shrunk →
      ∀ p ∈ interior shrunk.toSet, ∃ q ∈ frontier poly.toSet,
        dist ≤ Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2) := by
  -- TODO: Prove distance property of the shrink operation.
  -- Each edge of the shrunk polygon is exactly `dist` away from the corresponding
  -- edge of the original polygon (moved along the inward normal by `dist`).
  -- Points in the interior of the shrunk polygon are further from the original
  -- boundary than points on the shrunk boundary.
  -- This requires showing that for each point p in interior(shrunk), the closest
  -- point on frontier(poly) is at distance ≥ dist.
  sorry

/-- Get the number of vertices -/
def numVertices (poly : ConvexPolygon) : ℕ := poly.vertices.length

/-- Check if all vertices satisfy a predicate -/
def allVertices (poly : ConvexPolygon) (p : Point → Bool) : Bool :=
  poly.vertices.all p

end ConvexPolygon

end Moser
