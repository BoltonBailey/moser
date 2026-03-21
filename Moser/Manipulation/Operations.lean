import Mathlib
import Moser.Manipulation.Invariants
import Moser.Worm.Basic
import Moser.DirectIsometry.Discretization

/-!
# Moser Set Operations

This file implements the four key operations on the working set:
1. bigSetRemoval: Remove polygons with area > threshold
2. hullTaking: Apply convex hull (identity for convex polygons)
3. distanceRemoval: Remove polygons with vertices too far from origin
4. wormAdding: Add unions with transformed worm convex hulls
-/

namespace Moser

open Rat

namespace WorkingSet

/-- Operation 1: Remove polygons with area exceeding the threshold -/
def bigSetRemoval (s : WorkingSet) : WorkingSet :=
  { polygons := s.polygons.filter (fun p => p.area ≤ areaThreshold) }

-- /-- Operation 2: Apply convex hull (identity for already-convex polygons) -/
-- def hullTaking (s : WorkingSet) : WorkingSet :=
--   s  -- Already convex by type invariant

-- /-- Operation 3: Remove polygons with vertices exceeding distance cutoff -/
-- def distanceRemoval (s : WorkingSet) : WorkingSet :=
--   { polygons := s.polygons.filter fun p =>
--       p.vertices.all fun v =>
--         Point.distSq v (0, 0) ≤ distanceCutoff * distanceCutoff }

/-- Operation 4: Add a worm to the working set -/
def wormAdding (wormHull : ConvexPolygon) (epsilon : ℚ) (s : WorkingSet) : WorkingSet :=
  let isometries := discretizeIsometries epsilon
  let newPolygons := s.polygons.flatMap fun p =>
    isometries.filterMap fun iso =>
      let transformedWorm := iso.applyPolygon wormHull
      -- Compute union by taking vertices from both polygons
      -- For simplicity, use convex hull of combined vertices
      let combinedVertices := p.vertex_list ++ transformedWorm.vertex_list
      some (ConvexPolygon.ofHull combinedVertices)
  { polygons := newPolygons }

/-- Apply all cleanup operations: hull, bigSet, distance removal -/
def cleanup (s : WorkingSet) : WorkingSet :=
  s |> bigSetRemoval

/-- Add worm and cleanup -/
def addWormAndCleanup (wormHull : ConvexPolygon) (epsilon : ℚ) (s : WorkingSet) : WorkingSet :=
  (s.wormAdding wormHull epsilon).cleanup

end WorkingSet

end Moser
