import Moser.Basic

/-!
# Computational Approach to Moser's Worm Problem

This is the main entry point for the computational framework described in
https://thequantummilkman.substack.com/p/a-computational-approach-to-mosers

The goal is to improve lower bounds on Moser sets by iteratively:
1. Starting with an initial square
2. Finding worms that force the set to grow
3. Applying operations to maintain invariants
4. Repeating until no valid Moser set remains below the area threshold

## Quick Start

Run the main computation:
```lean
#eval Moser.runMoserComputation 100
```

## Structure

- `Moser.Constants`: Area threshold, distance cutoff, initial square
- `Moser.Geometry`: Points, polygons, areas, containment, intersection
- `Moser.Worm`: Worm definitions and enumeration
- `Moser.MoserSet`: Moser set definition, invariants, operations
- `Moser.Isometry`: Planar isometries and discretization
- `Moser.Computation`: Main algorithm and verification

## Example Computations
-/

namespace Moser

-- Test that the initial square has area 1/9
#eval
  let square : ConvexPolygon := {
    vertices := Constants.InitialSquare
    nonempty := by decide
  }
  s!"Initial square area: {square.area} (expected 1/9 = {1/9 : ℚ})"

-- Test point containment
#eval
  let square : ConvexPolygon := {
    vertices := Constants.InitialSquare
    nonempty := by decide
  }
  s!"Origin in square: {pointInConvexPolygon (0, 0) square}"

-- Test working set operations
#eval
  let initial := WorkingSet.initial
  s!"Initial working set size: {initial.size}"

#eval
  let initial := WorkingSet.initial
  s!"Initial min area: {initial.minArea}"

-- Test big set removal
#eval
  let initial := WorkingSet.initial
  let afterRemoval := initial.bigSetRemoval
  s!"After big set removal: {afterRemoval.size} polygons"

-- Run a small computation
-- #eval runMoserComputation 10

end Moser
