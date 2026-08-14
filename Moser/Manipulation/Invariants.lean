import Mathlib
import Moser.Constants
import Moser.Geometry.PolygonArea


/-!
# Working Set Invariants

This file defines the WorkingSet type with its three invariants.
-/

namespace Moser

/-- The working set of polygons maintained during the algorithm.

The three invariants the algorithm maintains:

* Invariant 1: all polygons are convex (guaranteed by the type).
* Invariant 2 (`Moser.WorkingSet.ContainsInitialWorm`, in `Moser.LowerBound`):
  every polygon contains the unshifted `InitialWorm`.
* Invariant 3 (`Moser.WorkingSet.Sound`, in `Moser.LowerBound`): every pinned
  convex worm cover of area at most `areaThreshold` contains the real region of
  some polygon of the working set.

Invariants 2 and 3 are stated as predicates in `Moser.LowerBound` (rather than as
fields here) so that the operations in `Moser.Manipulation.Operations` remain
plain computable functions; the preservation lemmas live alongside the
predicates. -/
structure WorkingSet where
  /-- The set of candidate polygons -/
  polygons : List (ConvexPolygon ℚ)

namespace WorkingSet


/-- Create initial working set with just the InitialWorm -/
def initial : WorkingSet :=
  { polygons := [InitialWorm] }

/-- Check if the working set is empty -/
def isEmpty (s : WorkingSet) : Bool :=
  s.polygons.isEmpty

/-- Get the polygon with minimum area -/
def minAreaPolygon (s : WorkingSet) : Option (ConvexPolygon ℚ) :=
  s.polygons.foldl
    (fun best p =>
      match best with
      | none => some p
      | some b => if p.area < b.area then some p else some b)
    none

/-- Get the minimum area in the working set -/
def minArea (s : WorkingSet) : ℚ :=
  match s.minAreaPolygon with
  | none => 0
  | some p => p.area

/-- Count the number of polygons -/
def size (s : WorkingSet) : ℕ :=
  s.polygons.length

end WorkingSet

end Moser
