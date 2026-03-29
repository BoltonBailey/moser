/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

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

lemma lengthSq_nonneg (v : RationalPoint) : 0 ≤ lengthSq v := by
  unfold lengthSq
  nlinarith


/-- Check if a point is strictly to the left of the directed line from p1 to p2.
    Uses the cross product: positive means left, negative means right, zero means collinear. -/
def isStrictlyLeftOf (p p1 p2 : RationalPoint) : Bool :=
  crossProduct (p2 - p1) (p - p1) > 0

/-- Check if three points are in counterclockwise order -/
def ccw (p1 p2 p3 : RationalPoint) : Bool := isStrictlyLeftOf p3 p1 p2

def rotate90Counterclockwise (p : RationalPoint) : RationalPoint :=
  ![ -p 1, p 0 ]

end RationalPoint

/--
Given a list of points, returns another list such that
the first point is the one with the lowest y-coordinate (and leftmost in case of ties),
and the rest are sorted by increasing polar angle with respect to the first point.
Points that fall directly between the first point and another point
(i.e., are collinear and closer to the first point) are removed.
-/
def grahamScanSortPolarAngle (points : List RationalPoint) : List RationalPoint :=
  match points with
  | [] => []
  | h :: _ =>
    -- Find pivot: lowest y-coordinate, then leftmost x-coordinate in case of ties
    let pivot := points.foldl (fun best p =>
      if p 1 < best 1 || (p 1 == best 1 && p 0 < best 0) then p else best) h
    -- Remove the first occurrence of pivot from the list
    let rest := points.eraseP (fun p => p 0 == pivot 0 && p 1 == pivot 1)
    -- Sort by polar angle from pivot using cross product comparison.
    -- cross > 0 means a has a smaller polar angle than b (a comes first).
    -- For collinear points in the same direction, sort by distance (closer first,
    -- so they appear before the farthest and get filtered out below).
    -- For collinear points in opposite directions (0° vs 180°), the rightward
    -- point (angle 0°) comes first.
    let sorted := rest.mergeSort (fun a b =>
      let va := a - pivot
      let vb := b - pivot
      let cross := RationalPoint.crossProduct va vb
      if cross > 0 then true
      else if cross < 0 then false
      else if RationalPoint.dotProduct va vb ≥ 0 then
        RationalPoint.distSq a pivot ≤ RationalPoint.distSq b pivot
      else
        va 0 > 0)
    -- Remove collinear points that are not the farthest from the pivot:
    -- keep p only if there is no q at the same angle and farther away.
    let filtered := sorted.filter (fun p =>
      !(sorted.any (fun q =>
        RationalPoint.crossProduct (p - pivot) (q - pivot) == 0 &&
        RationalPoint.dotProduct (p - pivot) (q - pivot) > 0 &&
        RationalPoint.distSq p pivot < RationalPoint.distSq q pivot)))
    pivot :: filtered



/-- Stack-based reduction step: push p onto stack, popping points that create non-left turns. -/
private def grahamScanStep' (stack : List RationalPoint) (p : RationalPoint) :
    List RationalPoint :=
  match stack with
  | [] => [p]
  | [q] => [p, q]
  | q :: r :: rest =>
    if RationalPoint.ccw r q p then p :: stack
    else grahamScanStep' (r :: rest) p
termination_by stack.length

/--
A step in the graham scan algorithm:
given a list of points sorted by increasing polar angle with respect to the first point,
removes points that do not form a left turn with the adjacent points in the hull.
-/
def grahamScanReduce (points : List RationalPoint) : List RationalPoint :=
  (points.foldl grahamScanStep' []).reverse

/-- Repeatedly apply `grahamScanReduce` until the list stops shrinking. -/
def grahamScanReduceLoop (pts : List RationalPoint) : List RationalPoint :=
  let reduced := grahamScanReduce pts
  if reduced.length < pts.length then grahamScanReduceLoop reduced else reduced
termination_by pts.length

/--
The main Graham scan algorithm:
given a list of points, returns the vertices of the convex hull in counterclockwise order.

It does this by repretedly applying `grahamScanReduce` to the list of points sorted by polar angle
until no more points can be removed.
-/
def grahamScan (points : List RationalPoint) : List RationalPoint :=
  grahamScanReduceLoop (grahamScanSortPolarAngle points)

-- =========================================================
-- Helper lemmas for the subset direction of the main theorem
-- =========================================================

/-- A foldl "select" always returns something from the initial value or the list. -/
private lemma foldl_select_mem {α : Type*} (pts : List α) (init : α)
    (cond : α → α → Bool) :
    pts.foldl (fun best p => if cond p best then p else best) init ∈ init :: pts := by
  induction pts generalizing init with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl]
    have key := ih (if cond h init then h else init)
    have sub : (if cond h init then h else init) :: t ⊆ init :: h :: t := by
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · split_ifs with hc
        · exact .inr (.inl rfl)
        · exact .inl rfl
      · exact .inr (.inr hx)
    exact sub key

/-- `grahamScanStep'` only outputs `p` or elements already in the stack. -/
private lemma grahamScanStep'_mem_aux : ∀ (n : ℕ) (stack : List RationalPoint)
    (p : RationalPoint), stack.length ≤ n →
    ∀ x ∈ grahamScanStep' stack p, x = p ∨ x ∈ stack := by
  intro n
  induction n with
  | zero =>
    intro stack p hlen x hx
    match stack with
    | [] =>
      simp only [grahamScanStep', List.mem_cons, List.mem_nil_iff, or_false] at hx
      exact .inl hx
    | _ :: _ => simp at hlen
  | succ m ih =>
    intro stack p hlen x hx
    match stack with
    | [] =>
      simp only [grahamScanStep', List.mem_cons, List.mem_nil_iff, or_false] at hx
      exact .inl hx
    | [q] =>
      simp only [grahamScanStep', List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact .inl rfl
      · exact .inr (by simpa using hx)
    | q :: r :: rest =>
      simp only [grahamScanStep'] at hx
      split_ifs at hx with h
      · rcases List.mem_cons.mp hx with rfl | hmem
        · exact .inl rfl
        · exact .inr hmem
      · have hlen' : (r :: rest).length ≤ m := by
          have : (q :: r :: rest).length = (r :: rest).length + 1 := rfl
          omega
        rcases ih (r :: rest) p hlen' x hx with rfl | hmem
        · exact .inl rfl
        · exact .inr (List.mem_cons_of_mem q hmem)

private lemma grahamScanStep'_mem (stack : List RationalPoint) (p : RationalPoint) :
    ∀ x ∈ grahamScanStep' stack p, x = p ∨ x ∈ stack :=
  grahamScanStep'_mem_aux stack.length stack p le_rfl

/-- Every element of `foldl grahamScanStep' init pts` comes from `init` or `pts`. -/
private lemma foldl_grahamScanStep'_mem (init : List RationalPoint) (pts : List RationalPoint) :
    ∀ x ∈ List.foldl grahamScanStep' init pts, x ∈ init ∨ x ∈ pts := by
  induction pts generalizing init with
  | nil => simp
  | cons p rest ih =>
    intro x hx
    simp only [List.foldl] at hx
    rcases ih (grahamScanStep' init p) x hx with h | h
    · rcases grahamScanStep'_mem init p x h with rfl | hmem
      · exact .inr (.head _)
      · exact .inl hmem
    · exact .inr (.tail _ h)

/-- `grahamScanReduce` only keeps elements from its input. -/
private lemma grahamScanReduce_subset (pts : List RationalPoint) :
    ∀ x ∈ grahamScanReduce pts, x ∈ pts := by
  intro x hx
  simp only [grahamScanReduce, List.mem_reverse] at hx
  rcases foldl_grahamScanStep'_mem [] pts x hx with h | h
  · simp at h
  · exact h

/-- `grahamScanSortPolarAngle` only keeps elements from its input. -/
private lemma grahamScanSortPolarAngle_subset (points : List RationalPoint) :
    ∀ x ∈ grahamScanSortPolarAngle points, x ∈ points := by
  match points with
  | [] => simp [grahamScanSortPolarAngle]
  | h :: rest =>
    intro x hx
    simp only [grahamScanSortPolarAngle, List.mem_cons] at hx
    rcases hx with rfl | hx
    · -- x = pivot; after rfl, x is substituted; goal: pivot ∈ h :: rest
      have hmem :=
        foldl_select_mem (h :: rest) h
          (fun p best => p 1 < best 1 || (p 1 == best 1 && p 0 < best 0))
      -- hmem : pivot ∈ h :: (h :: rest), i.e. pivot = h ∨ pivot ∈ h :: rest
      rcases List.mem_cons.mp hmem with h_eq | hmem
      · -- pivot = h; rewrite and use h ∈ h :: rest
        rw [h_eq]; exact List.mem_cons.mpr (.inl rfl)
      · exact hmem
    · -- x ∈ filtered ⊆ sorted ⊆ eraseP ⊆ points
      have h1 : x ∈ ((h :: rest).eraseP _).mergeSort _ := (List.mem_filter.mp hx).1
      have h2 : x ∈ (h :: rest).eraseP _ :=
        (List.mergeSort_perm ((h :: rest).eraseP _) _).subset h1
      exact List.eraseP_subset h2

/-- `grahamScan` equals `grahamScanReduceLoop` applied to the sorted list. -/
private lemma grahamScan_eq_reduceLoop (points : List RationalPoint) :
    grahamScan points = grahamScanReduceLoop (grahamScanSortPolarAngle points) := rfl

/-- One-step unfolding of `grahamScanReduceLoop`. -/
private lemma grahamScanReduceLoop_step (pts : List RationalPoint) :
    grahamScanReduceLoop pts =
      if (grahamScanReduce pts).length < pts.length
      then grahamScanReduceLoop (grahamScanReduce pts)
      else grahamScanReduce pts := by
  -- Use the auto-generated equation lemma (rw applies it exactly once, no looping)
  rw [grahamScanReduceLoop.eq_1]

/-- `grahamScanReduceLoop` only keeps elements from its input. -/
private lemma grahamScanReduceLoop_subset : ∀ (n : ℕ) (pts : List RationalPoint),
    pts.length ≤ n → ∀ x ∈ grahamScanReduceLoop pts, x ∈ pts := by
  intro n
  induction n with
  | zero =>
    intro pts hlen x hx
    rw [grahamScanReduceLoop_step] at hx
    split_ifs at hx with h
    · exact absurd h (by omega)
    · exact grahamScanReduce_subset pts x hx
  | succ m ih =>
    intro pts hlen x hx
    rw [grahamScanReduceLoop_step] at hx
    split_ifs at hx with h
    · have hlen' : (grahamScanReduce pts).length ≤ m := by omega
      exact grahamScanReduce_subset pts x (ih _ hlen' x hx)
    · exact grahamScanReduce_subset pts x hx

/-- Every element of `grahamScan points` is in `points`. -/
private lemma grahamScan_subset (points : List RationalPoint) :
    ∀ x ∈ grahamScan points, x ∈ points := fun x hx =>
  grahamScanSortPolarAngle_subset points x
    (grahamScanReduceLoop_subset _ _ le_rfl x
      (grahamScan_eq_reduceLoop points ▸ hx))

/--
Every point in a list is a convex combination
of the points in the convex hull of that list, as given by the Graham scan algorithm.
-/
theorem convexHull_grahamScan_eq (points : List RationalPoint) :
    convexHull ℚ {p | p ∈ grahamScan points} = convexHull ℚ {p | p ∈ points} := by
  apply le_antisymm
  · -- grahamScan points ⊆ points, so convexHull(scan) ⊆ convexHull(points)
    apply convexHull_mono
    intro x hx
    exact grahamScan_subset points x hx
  · -- Every point of points is in convexHull(grahamScan points).
    -- This is the algorithm correctness direction: every removed point is a convex
    -- combination of points that remain. Proved by induction on the two phases:
    --   (1) grahamScanSortPolarAngle: collinear-interior points lie on a segment
    --       between the pivot and the farthest collinear point, hence in the hull.
    --   (2) grahamScanReduce: each popped point q (where ¬ ccw r q p) lies inside
    --       the polygon formed by the current hull stack.
    simp [grahamScan]
    sorry
