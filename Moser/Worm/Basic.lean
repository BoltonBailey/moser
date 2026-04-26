import Mathlib
import Moser.Geometry.Polygon

/-!
# Worms

This file defines worms as piecewise linear paths of unit length.
-/

namespace Moser

/-- Approximate sqrt(s) using Newton's method (Babylonian method).
    Given s ≥ 0 and epsilon > 0, returns a rational r such that |r - sqrt(s)| < epsilon -/
def sqrtApprox (s : ℚ) (epsilon : ℚ) (fuel : ℕ := 100) : ℚ :=
  if s ≤ 0 then 0
  else
    -- Newton iteration: x_{n+1} = (x_n + s/x_n) / 2
    let rec
      /-- One step of the Newton iteration on `x`, recursing up to `n` more times. -/
      newton (x : ℚ) (n : ℕ) : ℚ :=
        if n = 0 then x
        else
          let x' := (x + s / x) / 2
          -- Stop if we're close enough: |x'^2 - s| < epsilon * x' approximately
          if |x' * x' - s| < epsilon * epsilon then x'
          else newton x' (n - 1)
    -- Initial guess: max(1, s) is a reasonable starting point
    newton (max 1 s) fuel

/-- Approximate the Euclidean distance between two points to within epsilon.
    Returns a rational d such that |d - dist(p,q)| < epsilon -/
def distanceApprox (p q : RationalPoint) (epsilon : ℚ) : ℚ :=
  sqrtApprox (RationalPoint.distSq p q) epsilon

/-- Compute an approximate total length of a path given by vertices -/
def totalLengthApprox (vertices : List RationalPoint) (epsilon : ℚ) : ℚ :=
  if vertices.length < 2 then 0
  else
    let pairs := List.zip vertices vertices.tail
    -- Use epsilon / n for each segment to get total error < epsilon
    let segmentEpsilon := epsilon / pairs.length
    pairs.foldl (fun acc (p, q) => acc + distanceApprox p q segmentEpsilon) 0

/-- A worm is a piecewise linear path (at least 2 vertices) -/
structure Worm where
  /-- The vertices defining the path -/
  vertices : List RationalPoint
  /-- The path has at least 2 vertices -/
  nonempty : vertices.length ≥ 2

namespace Worm

/-- Scale a point by a rational factor -/
def scaleRationalPoint (s : ℚ) (p : RationalPoint) : RationalPoint := ![s * p 0, s * p 1]

/-- Scale all vertices of a worm by a factor -/
def scale (w : Worm) (s : ℚ) : Worm :=
  { vertices := w.vertices.map (scaleRationalPoint s)
    nonempty := by simp only [List.length_map, ge_iff_le]; exact w.nonempty }

/-- Get the approximate total length of the worm -/
def lengthApprox (w : Worm) (epsilon : ℚ) : ℚ :=
  totalLengthApprox w.vertices epsilon

/-- Scale a worm to have approximately unit length.
    Returns the scaled worm. The scaling factor is 1/length. -/
def scaleToUnit (w : Worm) (epsilon : ℚ) : Worm :=
  let len := w.lengthApprox epsilon
  if len ≤ 0 then w  -- Degenerate case: all points coincide
  else w.scale (1 / len)


/-- Convert worm vertices to a convex polygon -/
def toConvexPolygon (w : Worm) : ConvexPolygon := sorry

/-- Get the convex hull as a ConvexPolygon -/
def convexHullPolygon (w : Worm) : ConvexPolygon :=
  w.toConvexPolygon

end Worm

/-- A unit worm is a worm with total length approximately 1 -/
structure UnitWorm where
  /-- The underlying worm -/
  worm : Worm
  /-- The total length is approximately 1 (converges to 1 as epsilon → 0) -/
  unitLength : ∀ epsilon : ℚ, epsilon > 0 → |worm.lengthApprox epsilon - 1| < epsilon

namespace UnitWorm

/-- Get the vertices of a unit worm -/
def vertices (w : UnitWorm) : List RationalPoint := w.worm.vertices

/-- Convert to a convex polygon -/
def toConvexPolygon (w : UnitWorm) : ConvexPolygon := w.worm.toConvexPolygon

end UnitWorm

/-- Convert a worm to a unit worm by scaling to unit length.
    The epsilon parameter controls the precision of the length computation. -/
def Worm.toUnitWorm (w : Worm) (epsilon : ℚ) : UnitWorm := sorry

end Moser
