import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic

/-!
# Points in the Plane

This file defines points as rational coordinate pairs and basic operations.
-/

namespace Moser

/-- A point in the plane with rational coordinates -/
abbrev Point := ℚ × ℚ

namespace Point

/-- Convert a rational point to a real point -/
def toReal (p : Point) : ℝ × ℝ := (↑p.1, ↑p.2)

/-- Squared distance between two points (avoids square roots) -/
def distSq (p q : Point) : ℚ :=
  let dx := p.1 - q.1
  let dy := p.2 - q.2
  dx * dx + dy * dy

/-- Subtract two points (vector from q to p) -/
def sub (p q : Point) : Point := (p.1 - q.1, p.2 - q.2)

instance : HSub Point Point Point where
  hSub := sub

/-- Add a point and a vector -/
def add (p q : Point) : Point := (p.1 + q.1, p.2 + q.2)

instance : HAdd Point Point Point where
  hAdd := add

/-- Cross product of two 2D vectors (returns scalar) -/
def crossProduct (u v : Point) : ℚ := u.1 * v.2 - u.2 * v.1

/-- Dot product of two 2D vectors -/
def dotProduct (u v : Point) : ℚ := u.1 * v.1 + u.2 * v.2

/-- Euclidean length squared of a vector -/
def lengthSq (v : Point) : ℚ := v.1 * v.1 + v.2 * v.2

end Point

end Moser
