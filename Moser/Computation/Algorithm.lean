import Moser.MoserSet.Operations
import Moser.Worm.Enumeration

/-!
# Main Moser Computation Algorithm

This file implements the main iterative algorithm for improving Moser set bounds.
-/

namespace Moser

/-- Find a worm that increases the minimum area when added -/
def findWormIncreasingArea (p : ConvexPolygon) (epsilon : ℚ) : Option (ConvexPolygon × ℚ) :=
  let candidates := defaultWormEnumeration
  let currentArea := p.area

  candidates.foldl
    (fun best worm =>
      -- Simulate adding this worm
      let testSet : WorkingSet := { polygons := [p] }
      let afterAdding := testSet.addWormAndCleanup worm epsilon
      let newMinArea := afterAdding.minArea

      match best with
      | none =>
          if newMinArea > currentArea then some (worm, newMinArea)
          else none
      | some (bestWorm, bestArea) =>
          if newMinArea > bestArea then some (worm, newMinArea)
          else some (bestWorm, bestArea))
    none

/-- Single iteration of the Moser computation -/
def moserIteration (s : WorkingSet) (epsilon : ℚ) : Option WorkingSet :=
  if s.isEmpty then
    none  -- Success! No more polygons to check
  else
    match s.minAreaPolygon with
    | none => none
    | some p =>
        match findWormIncreasingArea p epsilon with
        | none => some s  -- No improvement found, return unchanged
        | some (worm, _newArea) =>
            some (s.addWormAndCleanup worm epsilon)

/-- Run the Moser computation for up to maxIterations -/
partial def moserComputation (maxIterations : ℕ) (epsilon : ℚ := 1/10) : Bool × WorkingSet × ℕ :=
  let initial := WorkingSet.initial
  go initial 0
where
  go (s : WorkingSet) (iter : ℕ) : Bool × WorkingSet × ℕ :=
    if iter ≥ maxIterations then
      (false, s, iter)  -- Timeout
    else if s.isEmpty then
      (true, s, iter)   -- Success!
    else
      match moserIteration s epsilon with
      | none => (true, s, iter)  -- Success!
      | some s' =>
          if s'.size == s.size && s'.minArea == s.minArea then
            (false, s', iter)  -- Stuck, no progress
          else
            go s' (iter + 1)

/-- Run computation with detailed output -/
def runMoserComputation (maxIterations : ℕ := 100) : IO Unit := do
  IO.println s!"Starting Moser computation with max {maxIterations} iterations..."
  let (success, finalSet, iters) := moserComputation maxIterations
  IO.println s!"Completed after {iters} iterations"
  IO.println s!"Success: {success}"
  IO.println s!"Final set size: {finalSet.size}"
  IO.println s!"Final min area: {finalSet.minArea}"

end Moser
