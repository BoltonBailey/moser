import Mathlib.Data.Rat.Basic

/-!
# Constants for Moser's Worm Problem

This file defines the key constants used in the computational approach:
- `areaThreshold`: Maximum area for candidate Moser sets
- `distanceCutoff`: Maximum distance from origin for polygon vertices
- `InitialSquare`: Starting polygon (1/3 × 1/3 square centered at origin)
-/

namespace Moser

/-- Area threshold for candidate Moser sets (0.232240) -/
def areaThreshold : ℚ := 232240 / 1000000

/-- Distance cutoff for polygon vertices from origin (1.39344) -/
def distanceCutoff : ℚ := 1393440 / 1000000

/-- Initial square with side length 1/3 centered at origin -/
def InitialSquare : List (ℚ × ℚ) :=
  [(-1/6, -1/6), (1/6, -1/6), (1/6, 1/6), (-1/6, 1/6)]

end Moser
