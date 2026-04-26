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

/--
given a convex polygon `p` and a worm hull `w` and a positive rational `ε`, return a List of convex polygons obtained by discretizing the space of direct isometries and applying them to a shrunk version of `w`, then taking the convex hull of p with the result.
-/
def wormReplacement (p : ConvexPolygon) (w : ConvexPolygon) (epsilon : ℚ) (eps_pos : 0 < epsilon) : List ConvexPolygon :=
  let isometries := discretizeIsometries epsilon
  let transformedWorms : List ConvexPolygon := isometries.filterMap (fun iso =>
    Option.map iso.applyPolygon (w.shrink epsilon (epsilon / 10) (by grind) (by grind)) )
  transformedWorms.filterMap fun transformedWorm =>
    -- Compute union by taking vertices from both polygons
    -- For simplicity, use convex hull of combined vertices
    let combinedVertices := p.vertex_list ++ transformedWorm.vertex_list
    (ConvexPolygon.ofList combinedVertices)

/-- Operation 4: Add a worm to the working set -/
def wormAdding (wormHull : ConvexPolygon) (epsilon : ℚ) (eps_pos : 0 < epsilon) (s : WorkingSet) : WorkingSet :=
  { polygons := s.polygons.flatMap (fun p => wormReplacement p wormHull epsilon eps_pos) }

/-- Apply all cleanup operations: bigSetRemoval -/
def cleanup (s : WorkingSet) : WorkingSet :=
  s |> bigSetRemoval |> supersetRemoval

/-- Add worm and cleanup -/
def addWormAndCleanup (wormHull : ConvexPolygon) (epsilon : ℚ) (eps_pos : 0 < epsilon) (s : WorkingSet) : WorkingSet :=
  (s.wormAdding wormHull epsilon eps_pos).cleanup

/-- The initial working set: a single polygon, the `InitialWorm`. -/
def InitialWorkingSet : WorkingSet := {
  polygons := [InitialWorm]
}

#print sorries addWormAndCleanup

-- #eval wormReplacement InitialWorm RightTriangleOneThirdWorm (1 / 3) (by grind)

-- #eval (InitialWorkingSet.addWormAndCleanup RightTriangleOneThirdWorm (.divInt 1 10) (by rfl)).polygons.length

end WorkingSet
--
end Moser
