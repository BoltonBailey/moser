module

public import Mathlib
public import Moser.Manipulation.Invariants
import Moser.Worm.Basic
public import Moser.DirectIsometry.Discretization

@[expose] public section

/-!
# Moser Set Operations

-/

namespace Moser

open Option

namespace WorkingSet

/-- Operation 1: Remove polygons with area exceeding the threshold -/
def bigSetRemoval (s : WorkingSet) : WorkingSet :=
  { polygons := s.polygons.filter (fun p => p.area ≤ areaThreshold) }

/-- One step of `supersetRemoval`: adjoin the polygon `p` to the accumulator
`kept` of retained polygons. If some retained polygon is contained in `p`, then
`p` is redundant and is dropped; otherwise `p` is retained, and any previously
retained polygons containing `p` (now redundant) are dropped. -/
def supersetRemovalStep (kept : List (ConvexPolygon ℚ)) (p : ConvexPolygon ℚ) :
    List (ConvexPolygon ℚ) :=
  if kept.any fun q => q.isSubsetOf p then kept
  else kept.filter (fun q => !p.isSubsetOf q) ++ [p]

/-- Operation 2: Remove polygons which are supersets of others, processed
sequentially by `supersetRemovalStep`.

The sequential form (rather than the symmetric filter "drop `p` whenever some
other `q ⊆ p` is in the list") matters for soundness:
`ConvexPolygon.isSubsetOf` is not antisymmetric — two distinct polygons, e.g.
with cyclically rotated vertex lists, can each contain the other — and the
symmetric filter would delete *both* members of such a pair, potentially
removing the last witness required by the soundness invariant
(`Moser.WorkingSet.Sound.supersetRemoval` in `Moser.LowerBound`). The
sequential form always keeps a representative. -/
def supersetRemoval (s : WorkingSet) : WorkingSet :=
  { polygons := s.polygons.foldl supersetRemovalStep [] }

/--
given a convex polygon `p` and a worm hull `w` and a positive rational `ε`,
return a List of convex polygons obtained by discretizing the space of direct
isometries and applying them to a shrunk version of `w`, then taking the
convex hull of p with the result.

TODO change the isometry discretization to only include isometries in the
allowed set of `p`, rather than the initialworm
-/
def wormReplacement (p : ConvexPolygon ℚ) (w : ConvexPolygon ℚ) (epsilon : ℚ)
    (eps_pos : 0 < epsilon) : List (ConvexPolygon ℚ) :=
  let isometries := discretizeIsometries epsilon
  let transformedWorms : List (ConvexPolygon ℚ) := isometries.filterMap (fun iso =>
    Option.map iso.applyPolygon
      (w.shrink epsilon (epsilon / 10) (by grind) (by grind)) )
  transformedWorms.filterMap fun transformedWorm =>
    -- Compute union by taking vertices from both polygons
    -- For simplicity, use convex hull of combined vertices
    let combinedVertices := p.vertex_list ++ transformedWorm.vertex_list
    (ConvexPolygon.ofList combinedVertices)

/-- Operation 4: Add a worm to the working set -/
def wormAdding (wormHull : ConvexPolygon ℚ) (epsilon : ℚ) (eps_pos : 0 < epsilon)
    (s : WorkingSet) : WorkingSet :=
  { polygons := s.polygons.flatMap (fun p => wormReplacement p wormHull epsilon eps_pos) }

/-- Apply all cleanup operations: bigSetRemoval -/
def cleanup (s : WorkingSet) : WorkingSet :=
  s |> bigSetRemoval |> supersetRemoval

/-- Add worm and cleanup -/
def addWormAndCleanup (wormHull : ConvexPolygon ℚ) (epsilon : ℚ) (eps_pos : 0 < epsilon)
    (s : WorkingSet) : WorkingSet :=
  (s.wormAdding wormHull epsilon eps_pos).cleanup

/-- The initial working set: a single polygon, the `InitialWorm`. -/
def InitialWorkingSet : WorkingSet := {
  polygons := [InitialWorm]
}

#print sorries addWormAndCleanup

-- #eval wormReplacement InitialWorm RightTriangleOneThirdWorm (1 / 3) (by grind)

-- #eval (InitialWorkingSet.addWormAndCleanup RightTriangleOneThirdWorm
--   (.divInt 1 10) (by rfl)).polygons.length

end WorkingSet
--
end Moser

end
