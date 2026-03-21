import Mathlib
import Moser.Geometry.Polygon

/-!
# Planar Isometries

This file defines planar isometries (rotations + translations) with rational approximations.
-/

namespace Moser

open Rat

/-- A planar isometry represented by rotation angle (via sin/cos) then a translation -/
structure DirectIsometry where
  /-- Cosine of rotation angle (rational approximation) -/
  cos : ℚ
  /-- Sine of rotation angle (rational approximation) -/
  sin : ℚ
  /-- Translation vector -/
  translation : RationalPoint
  /-- sin cos -/
  isValid : cos * cos + sin * sin = 1

namespace DirectIsometry

/-- The identity isometry -/
def id : DirectIsometry := ⟨1, 0, 0, by grind⟩

/-- Apply the isometry to a point -/
def apply (iso : DirectIsometry) (p : RationalPoint) : RationalPoint :=
  let rotated := ![iso.cos * p 0 - iso.sin * p 1, iso.sin * p 0 + iso.cos * p 1]
  rotated + iso.translation

-- TODO funlike instance

/-- Apply the isometry to a polygon -/
def applyPolygon (iso : DirectIsometry) (poly : ConvexPolygon) : ConvexPolygon where
  vertex_count := poly.vertex_count
  vertices := fun i => iso.apply (poly.vertices i)
  nodup := sorry
  vertices_extremeRationalPoints := sorry

/-- Compose two isometries -/
def compose (iso1 iso2 : DirectIsometry) : DirectIsometry :=
  { cos := iso1.cos * iso2.cos - iso1.sin * iso2.sin
    sin := iso1.sin * iso2.cos + iso1.cos * iso2.sin
    translation := iso1.apply iso2.translation
    isValid := by
      have h1 : iso1.cos * iso1.cos + iso1.sin * iso1.sin = 1 := iso1.isValid
      have h2 : iso2.cos * iso2.cos + iso2.sin * iso2.sin = 1 := iso2.isValid
      grind }

end DirectIsometry

end Moser
