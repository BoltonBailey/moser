import Mathlib
import Moser.Constants
import Moser.DirectIsometry.Basic

/-!
# Isometry Discretization

This file discretizes the space of direct planar isometries for computational purposes.

We might assume that the isometries act on worms containing the origin.
-/

namespace Moser

open Rat

/-- Rational approximation of π (355/113 is accurate to 6 decimal places) -/
def piApprox : ℚ := 355 / 113

/-- Rational approximation of sin using Taylor series (for small angles) -/
def sinApprox (angle : ℚ) : ℚ :=
  -- sin(x) ≈ x - x³/6 + x⁵/120 - x⁷/5040
  let x := angle
  let x2 := x * x
  let x3 := x2 * x
  let x5 := x3 * x2
  let x7 := x5 * x2
  x - x3 / 6 + x5 / 120 - x7 / 5040

/-- Rational approximation of cos using Taylor series (for small angles) -/
def cosApprox (angle : ℚ) : ℚ :=
  -- cos(x) ≈ 1 - x²/2 + x⁴/24 - x⁶/720
  let x := angle
  let x2 := x * x
  let x4 := x2 * x2
  let x6 := x4 * x2
  1 - x2 / 2 + x4 / 24 - x6 / 720

/-- Generate a grid of rational numbers in a range with given step size -/
def rationalGrid (min max step : ℚ) : List ℚ :=
  let n := Int.toNat ((max - min) / step).ceil
  List.range n |>.map (fun i => min + step * i)

/-- Helper: generate angle pairs without deduplication -/
def angleGridAux (n : ℕ) : List (ℚ × ℚ) :=
  let indices := List.range (n + 1)
  let j := n
  indices.flatMap fun i =>
    let a : ℚ := i
    let b : ℚ := j
    let a2 := a * a
    let b2 := b * b
    let norm := a2 + b2
    if norm == 0 then
      []
    else
      let c := (a2 - b2) / norm
      let s := (2 * a * b) / norm
      [(c, s), (-c, s), (c, -s), (-c, -s)]

/--
Generate rational points on the unit circle,
so that the maximum difference in angle between adjacent points is no more than `max_angle_change`.

Note: Implementation using the complex squaring trick.
For (a, b) we compute (a + bi)² = (a² - b²) + 2abi, then normalize to get:
- cos = (a² - b²) / (a² + b²)
- sin = 2ab / (a² + b²)
This gives exact rational (cos, sin) pairs satisfying cos² + sin² = 1.

TODO: Optimize by removing points that are too close together to be unnecessary per the spec.
-/
def angleGrid (max_angle_change : ℚ) : List (ℚ × ℚ) :=
  (angleGridAux (max 1 (Int.toNat (4 / max_angle_change).ceil))).dedup

/-- The core algebraic identity: for any a, b with a² + b² ≠ 0, the normalized
squared complex number lies on the unit circle. -/
theorem unit_circle_from_complex_square (a b : ℚ) (h : a * a + b * b ≠ 0) :
    let c := (a * a - b * b) / (a * a + b * b)
    let s := (2 * a * b) / (a * a + b * b)
    c * c + s * s = 1 := by
  simp only
  have h' : a ^ 2 + b ^ 2 ≠ 0 := by convert h using 2 <;> ring
  field_simp
  ring

/-- All elements of angleGridAux satisfy the unit circle equation. -/
theorem angleGridAux_spec (n : ℕ) (p : ℚ × ℚ) (hp : p ∈ angleGridAux n) :
    p.1 * p.1 + p.2 * p.2 = 1 := by
  simp only [angleGridAux, List.mem_flatMap] at hp
  grind

/-- All elements of angleGrid satisfy the unit circle equation. -/
theorem angleGrid_spec (step : ℚ) (p : ℚ × ℚ) (hp : p ∈ angleGrid step) :
    p.1 * p.1 + p.2 * p.2 = 1 := by
  simp only [angleGrid] at hp
  exact angleGridAux_spec _ p (List.dedup_subset _ hp)

-- /--
-- Angle grid covers the unit circle with maximum angle change no more than `max_angle_change`.
-- -/
-- theorem angleGrid_spec_coverage (max_angle_change : ℚ)

#eval angleGrid (1 / 2)
#eval (angleGrid (1 / 10)).length
#eval (angleGrid (1 / 30)).length


/--
Discretize the space of planar isometries with given granularity
TODO fold into the worm manipulations and optimize more finely.
-/
def discretizeIsometries (epsilon : ℚ) : List DirectIsometry :=
  let angleStep := epsilon / 3
  let transStep := epsilon / 3
  -- Adjust angle step based on distance cutoff to ensure coverage
  -- even for faraway point for which rotation matters more
  let angles := angleGrid (angleStep / distanceCutoff)
  let gridCoordinates := rationalGrid (-distanceCutoff) distanceCutoff transStep
  let translations := (gridCoordinates.flatMap fun x =>
    gridCoordinates.map fun y => ![x, y]).filter (LocationRange.contains)
  angles.attach.flatMap fun ⟨angle, h⟩ =>
    translations.map fun t =>
        { cos := angle.1
          sin := angle.2
          translation := t
          isValid := by
            apply angleGrid_spec _ (angle.1, angle.2) h
          }

/-- Discretize with a default epsilon -/
def defaultDiscretization : List DirectIsometry :=
  discretizeIsometries (1 / 10)

#print sorries defaultDiscretization

#eval (defaultDiscretization).length -- about 4.4 million

end Moser
