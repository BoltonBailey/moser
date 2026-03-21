import Mathlib

/-!
# Convex Polygons

This file defines convex polygons as ordered lists of rational vertices.
-/

/-- A point in the plane with rational coordinates -/
abbrev RationalPoint := (Fin 2) → ℚ

namespace RationalPoint

/-- Squared distance between two points (avoids square roots) -/
def distSq (p q : RationalPoint) : ℚ :=
  let dx := p 0 - q 0
  let dy := p 1 - q 1
  dx * dx + dy * dy

/-- Cross product of two 2D vectors (returns scalar) -/
def crossProduct (u v : RationalPoint) : ℚ := u 0 * v 1 - u 1 * v 0

/-- Dot product of two 2D vectors -/
def dotProduct (u v : RationalPoint) : ℚ := u 0 * v 0 + u 1 * v 1

/-- Euclidean length squared of a vector -/
def lengthSq (v : RationalPoint) : ℚ := v 0 * v 0 + v 1 * v 1


/-- Check if a point is strictly to the left of the directed line from p1 to p2.
    Uses the cross product: positive means left, negative means right, zero means collinear. -/
def isStrictlyLeftOf (p p1 p2 : RationalPoint) : Bool :=
  crossProduct (p2 - p1) (p - p1) > 0

/-- Check if three points are in counterclockwise order -/
def ccw (p1 p2 p3 : RationalPoint) : Bool := isStrictlyLeftOf p3 p1 p2

def rotate90Counterclockwise (p : RationalPoint) : RationalPoint :=
  ![ -p 1, p 0 ]

end RationalPoint

structure ClosedHalfSpace where
  basepoint : RationalPoint
  /-- The direction -/
  direction : RationalPoint

def ClosedHalfSpace.contains (h : ClosedHalfSpace) (p : RationalPoint) : Bool :=
  RationalPoint.dotProduct h.direction (p - h.basepoint) ≥ 0

def RationalPoint.toWeaklyLeft (p1 p2 : RationalPoint) : ClosedHalfSpace :=
  { basepoint := p1, direction := RationalPoint.rotate90Counterclockwise (p2 - p1) }

/--
Change the half-space by moving the basepoint inward by at least `dist` in the normal direction,
and at most `dist + tolerance` to account for numerical issues.
-/
def ClosedHalfSpace.moveInward (h : ClosedHalfSpace) (dist tolerance : ℚ) (tolerance_pos : 0 < tolerance) :
    ClosedHalfSpace :=
  sorry

structure OpenHalfSpace where
  basepoint : RationalPoint
  /-- The direction -/
  direction : RationalPoint

def OpenHalfSpace.contains (h : OpenHalfSpace) (p : RationalPoint) : Bool :=
  RationalPoint.dotProduct h.direction (p - h.basepoint) > 0

def RationalPoint.toStrictlyLeft (p1 p2 : RationalPoint) : OpenHalfSpace :=
  { basepoint := p1, direction := RationalPoint.rotate90Counterclockwise (p2 - p1) }



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

def ConvexPolygon.vertex_list (poly : ConvexPolygon) : List RationalPoint :=
  List.finRange poly.vertex_count |>.map poly.vertices

/--
Obtain a rational convex polygon from a list of rational points by computing the convex hull
and keeping only the extreme points.
-/
def ConvexPolygon.ofHull (pts : List RationalPoint) : ConvexPolygon where
  vertex_count := sorry
  vertices := sorry
  nodup := sorry
  vertices_extremeRationalPoints := sorry

/-- Graham scan helper: process remaining points to build upper/lower hull -/
def grahamScanStep (stack : List RationalPoint) (p : RationalPoint) : List RationalPoint :=
  match stack with
  | [] => [p]
  | [q] => [p, q]
  | q :: r :: rest =>
    if RationalPoint.ccw r q p then p :: stack
    else grahamScanStep (r :: rest) p

/-- Elements of grahamScanStep output are either p or from the stack -/
theorem grahamScanStep_subset (stack : List RationalPoint) (p : RationalPoint) :
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
theorem foldl_grahamScanStep_subset (init : List RationalPoint) (points : List RationalPoint) :
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

/-- The convex hull algorithm outputs are a subset of the input -/
theorem convexHullRationalPoints_subset (points : List RationalPoint) :
    ∀ p ∈ convexHullRationalPoints points, p ∈ points := by
  intro p hp
  sorry

/-- grahamScanStep produces a nodup list when stack is nodup and p is not in stack -/
theorem grahamScanStep_nodup (stack : List RationalPoint) (p : RationalPoint)
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

/-- Filter a list to keep only points that are on the convex hull boundary -/
def filterToExtremeRationalPoints (points : List RationalPoint) : List RationalPoint :=
  let hull := convexHullRationalPoints points
  points.filter (fun p => hull.contains p)

/-- Construct a ConvexPolygon from a list of points by removing duplicates
    and keeping only extreme points of the convex hull. -/
def ConvexPolygon.ofList (vertices : List RationalPoint) : ConvexPolygon where
  vertex_count := (filterToExtremeRationalPoints vertices).length
  vertices := fun i => (filterToExtremeRationalPoints vertices).get ⟨i, by omega⟩
  nodup := by
    sorry
  vertices_extremeRationalPoints := by
    sorry

/--
Returns a list of closed half-spaces corresponding to the edges of the convex polygon.
If there are fewer than 3 vertices,
returns none since we cannot define half-spaces for degenerate polygons.
-/
def ConvexPolygon.toHalfSpaces (poly : ConvexPolygon) : Option (List ClosedHalfSpace) :=
  if h : poly.vertex_count < 3 then none
  else
    let edges := List.finRange poly.vertex_count
    let halfSpaces := edges.map (fun i =>
      let p1 := poly.vertices i
      let p2 := poly.vertices (i + ⟨1, by omega⟩)
      RationalPoint.toWeaklyLeft p1 p2)
    some halfSpaces

def ConvexPolygon.contains (poly : ConvexPolygon) (p : RationalPoint) : Bool :=
  match poly.toHalfSpaces with
  | none => false
  | some halfSpaces => halfSpaces.all (fun h => h.contains p)

namespace ConvexPolygon

/-- Convert a polygon to a set in ℝ² via convex hull -/
def toSet (poly : ConvexPolygon) : Set (EuclideanSpace ℝ (Fin 2)) := sorry

/-- Shrink a convex polygon by moving each edge inward
by at least `dist` (in the normal direction).
and at most `dist + tolerance` (to account for numerical issues).
-/
def shrink (poly : ConvexPolygon) (dist : ℚ) (tolerance : ℚ) (tolerance_pos : 0 < tolerance) :
    ConvexPolygon :=
  sorry


end ConvexPolygon
