import Mathlib

/-!
# Rational Points

This file defines rational points in the plane and basic geometric operations on them.
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

lemma lengthSq_rotate90Counterclockwise (v : RationalPoint) :
    lengthSq (rotate90Counterclockwise v) = lengthSq v := by
  simp [lengthSq, rotate90Counterclockwise, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma lengthSq_pos_of_ne (v : RationalPoint) (hv : v ≠ 0) : 0 < lengthSq v := by
  simp only [lengthSq]
  by_contra h
  push_neg at h
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  exact hv (funext (fun i => by fin_cases i <;> simp_all))

end RationalPoint
