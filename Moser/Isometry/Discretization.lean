import Mathlib
import Moser.Isometry.Planar
import Moser.Constants

/-!
# Isometry Discretization

This file discretizes the space of planar isometries for computational purposes.
-/

namespace Moser

open Rat

/-- Rational approximation of π (355/113 is accurate to 6 decimal places) -/
def piApprox : ℚ := 355 / 113

/-- Rational approximation of sin using Taylor series (for small angles) -/
def sinApprox (angle : ℚ) : ℚ :=
  -- sin(x) ≈ x - x³/6 + x⁵/120
  let x := angle
  let x2 := x * x
  let x3 := x2 * x
  let x5 := x3 * x2
  x - x3 / 6 + x5 / 120

/-- Rational approximation of cos using Taylor series (for small angles) -/
def cosApprox (angle : ℚ) : ℚ :=
  -- cos(x) ≈ 1 - x²/2 + x⁴/24
  let x := angle
  let x2 := x * x
  let x4 := x2 * x2
  1 - x2 / 2 + x4 / 24

/-- Generate a grid of rational numbers in a range with given step size -/
def rationalGrid (min max step : ℚ) : List ℚ :=
  let n := Int.toNat ((max - min) / step).ceil
  List.range n |>.map (fun i => min + step * i)

/-- Helper: generate angle pairs without deduplication -/
def angleGridAux (n : ℕ) : List (ℚ × ℚ) :=
  let indices := List.range (n + 1)
  indices.flatMap fun i =>
    indices.flatMap fun j =>
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
Generate rational points on the unit circle using the complex squaring trick.
For (a, b) we compute (a + bi)² = (a² - b²) + 2abi, then normalize to get:
- cos = (a² - b²) / (a² + b²)
- sin = 2ab / (a² + b²)
This gives exact rational (cos, sin) pairs satisfying cos² + sin² = 1.
-/
def angleGrid (step : ℚ) : List (ℚ × ℚ) :=
  (angleGridAux (max 1 (Int.toNat (2 / step).floor))).dedup

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
  obtain ⟨i, _, j, _, helem⟩ := hp
  split_ifs at helem with hnorm
  · simp at helem
  · have hnz : i * i + j * j ≠ 0 := by
      simp only [beq_iff_eq] at hnorm
      exact hnorm
    have hbase := unit_circle_from_complex_square i j hnz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at helem
    rcases helem with rfl | rfl | rfl | rfl <;>
      simp only [neg_mul_neg, hbase]

/-- All elements of angleGrid satisfy the unit circle equation. -/
theorem angleGrid_spec (step : ℚ) (p : ℚ × ℚ) (hp : p ∈ angleGrid step) :
    p.1 * p.1 + p.2 * p.2 = 1 := by
  simp only [angleGrid] at hp
  exact angleGridAux_spec _ p (List.dedup_subset _ hp)

#eval angleGrid (1 / 2)
#eval (angleGrid (1 / 10)).length

/-- Discretize the space of planar isometries with given granularity -/
def discretizeIsometries (epsilon : ℚ) : List PlanarIsometry :=
  let angleStep := epsilon / 3
  let transStep := epsilon / 3
  let angles := angleGrid angleStep
  let translations := rationalGrid (-distanceCutoff) distanceCutoff transStep
  angles.attach.flatMap fun ⟨angle, h⟩ =>
    translations.flatMap fun tx =>
      translations.map fun ty =>
        { cos := angle.1
          sin := angle.2
          translation := (tx, ty)
          isValid := angleGrid_spec angleStep angle h
          }

/-- Discretize with a default epsilon -/
def defaultDiscretization : List PlanarIsometry :=
  discretizeIsometries (1 / 10)

#eval (defaultDiscretization).length -- about 32 million

end Moser
