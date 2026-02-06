import Moser.Geometry.Polygon
import Mathlib.Data.Complex.Basic

/-!
# Planar Isometries

This file defines planar isometries (rotations + translations) with rational approximations.
-/

namespace Moser

/-- A planar isometry represented by rotation angle (via sin/cos) and translation -/
structure PlanarIsometry where
  /-- Cosine of rotation angle (rational approximation) -/
  cos : ℚ
  /-- Sine of rotation angle (rational approximation) -/
  sin : ℚ
  /-- Translation vector -/
  translation : Point
  -- TODO: Add constraint that cos² + sin² ≈ 1

namespace PlanarIsometry

/-- The identity isometry -/
def id : PlanarIsometry := ⟨1, 0, (0, 0)⟩

/-- Apply the isometry to a point -/
def apply (iso : PlanarIsometry) (p : Point) : Point :=
  let rotated := (iso.cos * p.1 - iso.sin * p.2, iso.sin * p.1 + iso.cos * p.2)
  rotated + iso.translation

/-- Apply the isometry to a polygon -/
def applyPolygon (iso : PlanarIsometry) (poly : ConvexPolygon) : ConvexPolygon :=
  { vertices := poly.vertices.map (iso.apply ·)
    nonempty := by simp [List.length_map]; exact poly.nonempty }

/-- Compose two isometries -/
def compose (iso1 iso2 : PlanarIsometry) : PlanarIsometry :=
  { cos := iso1.cos * iso2.cos - iso1.sin * iso2.sin
    sin := iso1.sin * iso2.cos + iso1.cos * iso2.sin
    translation := iso1.apply iso2.translation }

end PlanarIsometry

end Moser
