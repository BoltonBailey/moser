import Mathlib
import Moser.Manipulation.Invariants
import Moser.Worm.Basic
import Moser.DirectIsometry.Discretization

/-!
# Moser Set Operations

-/

namespace Moser

open Rat Option

namespace WorkingSet

/-- Operation 1: Remove polygons with area exceeding the threshold -/
def bigSetRemoval (s : WorkingSet) : WorkingSet :=
  { polygons := s.polygons.filter (fun p => p.area ≤ areaThreshold) }

/-- Operation 2: Remove polygons which are supersets of others -/
def supersetRemoval (s : WorkingSet) : WorkingSet :=
  { polygons := s.polygons.filter fun p =>
      ¬s.polygons.any fun q => q ≠ p && q.isSubsetOf p }

/-- Operation 4: Add a worm to the working set -/
def wormAdding (wormHull : ConvexPolygon) (epsilon : ℚ) (eps_pos : 0 < epsilon) (s : WorkingSet) : WorkingSet :=
  let isometries := discretizeIsometries epsilon
  let transformedWorms : List ConvexPolygon := isometries.filterMap (fun iso =>
    Option.map iso.applyPolygon (wormHull.shrink epsilon (epsilon / 10) (by grind) (by grind)) )
  let newPolygons := s.polygons.flatMap fun p =>
    transformedWorms.filterMap fun transformedWorm =>
      -- Compute union by taking vertices from both polygons
      -- For simplicity, use convex hull of combined vertices
      let combinedVertices := p.vertex_list ++ transformedWorm.vertex_list
      some (ConvexPolygon.ofList combinedVertices)
  { polygons := newPolygons }

/-- Apply all cleanup operations: bigSetRemoval -/
def cleanup (s : WorkingSet) : WorkingSet :=
  s |> bigSetRemoval |> supersetRemoval

/-- Add worm and cleanup -/
def addWormAndCleanup (wormHull : ConvexPolygon) (epsilon : ℚ) (eps_pos : 0 < epsilon) (s : WorkingSet) : WorkingSet :=
  (s.wormAdding wormHull epsilon eps_pos).cleanup

def InitialWorkingSet : WorkingSet := {
  polygons := [InitialWorm]
}

#print sorries addWormAndCleanup

-- #eval (InitialWorkingSet.addWormAndCleanup RightTriangleOntThirdWorm (.divInt 1 100) (by rfl)).polygons.length

end WorkingSet
--
end Moser
