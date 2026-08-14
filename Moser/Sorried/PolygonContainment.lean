module

public import Mathlib
public import Moser.Geometry.Polygon
public import Moser.DirectIsometry.Basic

public section

/-!
# Containment of a polygon under rigid motions (STUB)

Decides whether a convex container polygon contains some rotation + translation
(direct/orientation-preserving isometry) of another convex polygon.

## TODO

- Implement this. [This paper](https://www.cs.princeton.edu/%7Echazelle/pubs/PolygContainmentProb.pdf) seems to describe an efficient algorithm for this.

-/

namespace ConvexPolygon

open scoped Convex

/-- The real planar region of a convex polygon: the convex hull of its vertices,
cast from `ℚ` into `ℝ²`. Used only to *state* the specification. -/
noncomputable def realCarrier (poly : ConvexPolygon ℚ) : Set (Fin 2 → ℝ) :=
  convexHull ℝ (Set.range fun i => fun j => ((poly.vertices i j : ℚ) : ℝ))

/-- A real orientation-preserving rotation by angle `θ` about the origin. -/
noncomputable def realRotate (θ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![Real.cos θ * x 0 - Real.sin θ * x 1, Real.sin θ * x 0 + Real.cos θ * x 1]

/--
Decide whether `container` contains some rotation + translation of `worm`.

UNIMPLEMENTED — see the module docstring for why this is hard over `ℚ`.
-/
def containsCopyOf (container worm : ConvexPolygon ℚ) : Bool := sorry

/--
Specification for `containsCopyOf`: it returns `true` exactly when there is a real
direct isometry (rotation by some `θ`, then translation by some `t`) carrying the
worm's region inside the container's region.

UNIMPLEMENTED.
-/
theorem containsCopyOf_iff (container worm : ConvexPolygon ℚ) :
    container.containsCopyOf worm = true ↔
      ∃ (θ : ℝ) (t : Fin 2 → ℝ),
        (fun x => realRotate θ x + t) '' worm.realCarrier ⊆ container.realCarrier := by
  sorry

end ConvexPolygon

end
