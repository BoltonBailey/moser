import Moser.Computation.Algorithm

/-!
# Computational Verification

This file provides decidable instances for computational predicates.
-/

namespace Moser

-- Decidability instances for basic operations

instance : Decidable (p.1 = q.1 ∧ p.2 = q.2) := by
  exact instDecidableAnd

instance pointInPolyDecidable (p : Point) (poly : ConvexPolygon) :
    Decidable (pointInConvexPolygon p poly = true) := by
  exact instDecidableEqBool _ _

instance areaThresholdDecidable (poly : ConvexPolygon) :
    Decidable (poly.area ≤ areaThreshold) := by
  exact Rat.decidableLE _ _

instance distanceCheckDecidable (p : Point) (cutoff : ℚ) :
    Decidable (Point.distSq p (0, 0) ≤ cutoff * cutoff) := by
  exact Rat.decidableLE _ _

-- Example verification tests

/-- Test: Initial square has correct area -/
def testInitialSquareArea : Bool :=
  let square : ConvexPolygon := {
    vertices := Constants.InitialSquare
    nonempty := by decide
  }
  square.area == 1 / 9

/-- Test: Point at origin is inside initial square -/
def testPointInSquare : Bool :=
  let square : ConvexPolygon := {
    vertices := Constants.InitialSquare
    nonempty := by decide
  }
  pointInConvexPolygon (0, 0) square

/-- Test: bigSetRemoval keeps initial square -/
def testBigSetRemoval : Bool :=
  let initial := WorkingSet.initial
  let after := initial.bigSetRemoval
  !after.isEmpty

end Moser
