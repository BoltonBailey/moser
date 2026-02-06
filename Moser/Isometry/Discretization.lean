import Moser.Isometry.Planar
import Moser.Constants
import Mathlib.Data.Rat.Basic

/-!
# Isometry Discretization

This file discretizes the space of planar isometries for computational purposes.
-/

namespace Moser

/-- Rational approximation of π (355/113 is accurate to 6 decimal places) -/
def piApprox : ℚ := 355 / 113

/-- Rational approximation of sin using Taylor series (for small angles) -/
def sinApprox (angle : ℚ) : ℚ :=
  -- sin(x) ≈ x - x³/6 + x⁵/120
  let x := angle
  let x2 := x * x
  let x3 := x2 * x
  let x5 := x3 * x2
  x - x3/6 + x5/120

/-- Rational approximation of cos using Taylor series (for small angles) -/
def cosApprox (angle : ℚ) : ℚ :=
  -- cos(x) ≈ 1 - x²/2 + x⁴/24
  let x := angle
  let x2 := x * x
  let x4 := x2 * x2
  1 - x2/2 + x4/24

/-- Generate a grid of rational numbers in a range with given step size -/
def rationalGrid (min max step : ℚ) : List ℚ :=
  let n := Int.toNat ((max - min) / step).ceil
  List.range n |>.map (fun i => min + step * i)

/-- Discretize the space of planar isometries with given granularity -/
def discretizeIsometries (epsilon : ℚ) : List PlanarIsometry :=
  let angleStep := epsilon / 3
  let transStep := epsilon / 3
  let angles := rationalGrid 0 (2 * piApprox) angleStep
  let translations := rationalGrid (-distanceCutoff) distanceCutoff transStep

  angles.bind fun angle =>
    translations.bind fun tx =>
      translations.map fun ty =>
        { cos := cosApprox angle
          sin := sinApprox angle
          translation := (tx, ty) }

/-- Discretize with a default epsilon -/
def defaultDiscretization : List PlanarIsometry :=
  discretizeIsometries (1 / 10)

end Moser
