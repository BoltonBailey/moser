module

public import Mathlib

@[expose] public section

/-!
# Planar Points

This file defines points in the plane over a generic ordered field `K`,
and basic geometric operations on them.
-/

/-- A point in the plane with coordinates in an ordered field `K`. -/
abbrev Point (K : Type*) := (Fin 2) → K

variable {K : Type*}

namespace Point

section CommRing

variable [CommRing K]

/-- Squared distance between two points (avoids square roots) -/
def distSq (p q : Point K) : K :=
  let dx := p 0 - q 0
  let dy := p 1 - q 1
  dx * dx + dy * dy

/-- Cross product of two 2D vectors (returns scalar) -/
def crossProduct (u v : Point K) : K := u 0 * v 1 - u 1 * v 0

/-- Dot product of two 2D vectors -/
def dotProduct (u v : Point K) : K := u 0 * v 0 + u 1 * v 1

/-- Euclidean length squared of a vector -/
def lengthSq (v : Point K) : K := v 0 * v 0 + v 1 * v 1

/-- Rotate a point by 90° counterclockwise about the origin. -/
def rotate90Counterclockwise (p : Point K) : Point K :=
  ![ -p 1, p 0 ]

lemma lengthSq_rotate90Counterclockwise (v : Point K) :
    lengthSq (rotate90Counterclockwise v) = lengthSq v := by
  simp [lengthSq, rotate90Counterclockwise, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end CommRing

section Ordered

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma lengthSq_nonneg (v : Point K) : 0 ≤ lengthSq v := by
  unfold lengthSq
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

/-- Check if a point is strictly to the left of the directed line from p1 to p2.
    Uses the cross product: positive means left, negative means right, zero means collinear. -/
def isStrictlyLeftOf (p p1 p2 : Point K) : Bool :=
  crossProduct (p2 - p1) (p - p1) > 0

/-- Check if three points are in counterclockwise order -/
def ccw (p1 p2 p3 : Point K) : Bool := isStrictlyLeftOf p3 p1 p2

lemma lengthSq_pos_of_ne (v : Point K) (hv : v ≠ 0) : 0 < lengthSq v := by
  simp only [lengthSq]
  by_contra h
  push Not at h
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  exact hv (funext (fun i => by fin_cases i <;> simp_all))

end Ordered

end Point

end
