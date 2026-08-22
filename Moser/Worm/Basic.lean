module

public import Mathlib
public import Moser.Geometry.Polygon

public section

/-!
# Worms

This file defines worms as piecewise linear paths of unit length.

Worms live over `ℚ` because the length approximation `sqrtApprox` (Newton
iteration) is intrinsically rational; for an upgrade to algebraic numbers the
length should be computed exactly and the approximation machinery dropped.
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
def distanceApprox (p q : Point ℚ) (epsilon : ℚ) : ℚ :=
  sqrtApprox (Point.distSq p q) epsilon

/-- Compute an approximate total length of a path given by vertices -/
def totalLengthApprox (vertices : List (Point ℚ)) (epsilon : ℚ) : ℚ :=
  if vertices.length < 2 then 0
  else
    let pairs := List.zip vertices vertices.tail
    -- Use epsilon / n for each segment to get total error < epsilon
    let segmentEpsilon := epsilon / pairs.length
    pairs.foldl (fun acc (p, q) => acc + distanceApprox p q segmentEpsilon) 0

/-- A worm is a piecewise linear path (at least 2 vertices) -/
structure Worm where
  /-- The vertices defining the path -/
  vertices : List (Point ℚ)
  /-- The path has at least 2 vertices -/
  nonempty : vertices.length ≥ 2

namespace Worm

/-- Scale a point by a rational factor -/
def scalePoint (s : ℚ) (p : Point ℚ) : Point ℚ := ![s * p 0, s * p 1]

/-- Scale all vertices of a worm by a factor -/
def scale (w : Worm) (s : ℚ) : Worm :=
  { vertices := w.vertices.map (scalePoint s)
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


/-- The convex hull of the worm's vertices, as a convex polygon.

Returns `none` exactly when the hull is degenerate (fewer than three extreme
points), i.e. when all the vertices are collinear; `ConvexPolygon` requires at
least three vertices in strictly convex position, so there is nothing to
return in that case. -/
def toConvexPolygon (w : Worm) : Option (ConvexPolygon ℚ) :=
  ConvexPolygon.ofList w.vertices

/-- Get the convex hull as a `ConvexPolygon`, when it is nondegenerate. -/
def convexHullPolygon (w : Worm) : Option (ConvexPolygon ℚ) :=
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
def vertices (w : UnitWorm) : List (Point ℚ) := w.worm.vertices

/-- Convert to a convex polygon, when the hull is nondegenerate. -/
def toConvexPolygon (w : UnitWorm) : Option (ConvexPolygon ℚ) := w.worm.toConvexPolygon

end UnitWorm

/-!
## Remark: rescaling to unit length

There is deliberately no `Worm.toUnitWorm : Worm → ℚ → UnitWorm`. Rescaling a
worm by `1 / lengthApprox ε` (`Worm.scaleToUnit`) produces a worm whose *exact*
length is close to `1`, but `UnitWorm.unitLength` demands
`|lengthApprox ε - 1| < ε` for **every** `ε > 0`, and that cannot be
established here:

* a piecewise-linear path with rational vertices has length
  `∑ √(Δx² + Δy²)`, which is irrational except in degenerate cases, so no
  rational rescaling makes the exact length equal to `1`;
* `lengthApprox` is a Newton iteration run with fixed `fuel` and the stopping
  test `|x'² - s| < ε²`, which does not by itself certify `|x' - √s| < ε`.

Upgrading `Point` to algebraic numbers (so that lengths are computed exactly)
is the intended fix; until then `UnitWorm` should be built by supplying the
`unitLength` proof by hand.
-/

end Moser

end
