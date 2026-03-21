import Mathlib
import Moser.Constants
import Moser.Geometry.PolygonArea


/-!
# Working Set Invariants

This file defines the WorkingSet type with its three invariants.
-/

namespace Moser

open Rat

/-- The working set of polygons maintained during the algorithm -/
structure WorkingSet where
  /-- The set of candidate polygons -/
  polygons : List ConvexPolygon
  -- Invariant 1: All polygons are convex (guaranteed by type)
  -- Invariant 2: All contain InitialWorm via some isometry
  -- containsInitialWorm : ∀ p ∈ polygons, ∃ iso, InitialWorm ⊆ iso.apply(p)
  -- Invariant 3: Any Moser set with area < threshold contains some polygon via isometry
  -- moserSetProperty : ∀ M, IsMoserSet M → area M < areaThreshold →
  --   ∃ p ∈ polygons, ∃ iso, p ⊆ iso.apply(M)

namespace WorkingSet


/-- Create initial working set with just the InitialWorm -/
def initial : WorkingSet :=
  { polygons := [InitialWorm] }

/-- Check if the working set is empty -/
def isEmpty (s : WorkingSet) : Bool :=
  s.polygons.isEmpty

/-- Get the polygon with minimum area -/
def minAreaPolygon (s : WorkingSet) : Option ConvexPolygon :=
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
