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

/--
The main Graham scan algorithm:
given a list of points, returns the vertices of the convex hull in counterclockwise order.

It does this by repretedly applying `grahamScanReduce` to the list of points sorted by polar angle
until no more points can be removed.
-/
def grahamScan (points : List RationalPoint) : List RationalPoint :=
  let sorted := grahamScanSortPolarAngle points
  let rec reduceLoop (pts : List RationalPoint) : List RationalPoint :=
    let reduced := grahamScanReduce pts
    if reduced.length < pts.length then reduceLoop reduced else reduced
  termination_by pts.length
  reduceLoop sorted

/--
Every point in a list is a convex combination
of the points in the convex hull of that list, as given by the Graham scan algorithm.
-/
theorem convexHull_grahamScan_eq (points : List RationalPoint) :
    convexHull ℚ {p | p ∈ grahamScan points} = convexHull ℚ {p | p ∈ points} := by
  ext p
  sorry
