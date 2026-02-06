import Moser.Worm.Enumeration
import Moser.Geometry.Containment

/-!
# Minimal Worm Finding

This file implements algorithms to find minimal worms not contained in a polygon.
-/

namespace Moser

/-- A partial path in the TSP dynamic programming -/
structure PartialPath where
  /-- Vertices visited so far -/
  visited : List Point
  /-- Current total length -/
  length : ℚ
  /-- Set of unvisited vertices -/
  remaining : List Point

/-- Find a minimal worm (via TSP) that doesn't fit in the polygon -/
def minimalWormNotContained (poly : ConvexPolygon) : Option ConvexPolygon :=
  -- Simplified version: just check enumerated worms
  -- TODO: Implement full DP-based TSP for finding minimal worm
  let candidates := defaultWormEnumeration
  candidates.find? fun w =>
    !poly.containsPolygon w

/-- Find any worm that isn't contained in the polygon after applying isometries -/
def findWormNotFitting (poly : ConvexPolygon) (isometries : List PlanarIsometry) : Option ConvexPolygon :=
  let candidates := defaultWormEnumeration
  candidates.find? fun w =>
    isometries.all fun iso =>
      let transformedWorm := iso.applyPolygon w
      !poly.containsPolygon transformedWorm

end Moser
