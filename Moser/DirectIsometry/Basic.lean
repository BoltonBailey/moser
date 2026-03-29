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

def apply_injective (iso : DirectIsometry) : Function.Injective (iso.apply) := by
  intro x y h
  simp only [apply, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_add,
    Matrix.empty_add_empty, Matrix.vecCons_inj, add_left_inj, and_true] at h
  obtain ⟨h1, h2⟩ := h
  -- h1 : iso.cos * x 0 - iso.sin * x 1 = iso.cos * y 0 - iso.sin * y 1
  -- h2 : iso.sin * x 0 + iso.cos * x 1 = iso.sin * y 0 + iso.cos * y 1
  have hx0 : iso.cos * (x 0 - y 0) - iso.sin * (x 1 - y 1) = 0 := by linarith
  have hx1 : iso.sin * (x 0 - y 0) + iso.cos * (x 1 - y 1) = 0 := by linarith
  have key0 : (iso.cos * iso.cos + iso.sin * iso.sin) * (x 0 - y 0) = 0 := by
    linear_combination iso.cos * hx0 + iso.sin * hx1
  have key1 : (iso.cos * iso.cos + iso.sin * iso.sin) * (x 1 - y 1) = 0 := by
    linear_combination -iso.sin * hx0 + iso.cos * hx1
  rw [iso.isValid, one_mul] at key0 key1
  have eq0 : x 0 = y 0 := by linarith
  have eq1 : x 1 = y 1 := by linarith
  funext i; fin_cases i
  · exact eq0
  · exact eq1

def apply_surjective (iso : DirectIsometry) : Function.Surjective (iso.apply) := by
  intro q
  refine ⟨![iso.cos * (q 0 - iso.translation 0) + iso.sin * (q 1 - iso.translation 1),
             -iso.sin * (q 0 - iso.translation 0) + iso.cos * (q 1 - iso.translation 1)], ?_⟩
  have hv := iso.isValid
  have h0 : iso.apply ![iso.cos * (q 0 - iso.translation 0) + iso.sin * (q 1 - iso.translation 1),
      -iso.sin * (q 0 - iso.translation 0) + iso.cos * (q 1 - iso.translation 1)] 0 = q 0 := by
    simp only [apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply]
    linear_combination (q 0 - iso.translation 0) * hv
  have h1 : iso.apply ![iso.cos * (q 0 - iso.translation 0) + iso.sin * (q 1 - iso.translation 1),
      -iso.sin * (q 0 - iso.translation 0) + iso.cos * (q 1 - iso.translation 1)] 1 = q 1 := by
    simp only [apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply]
    linear_combination (q 1 - iso.translation 1) * hv
  funext i; fin_cases i
  · exact h0
  · exact h1

instance : FunLike DirectIsometry RationalPoint (RationalPoint) where
  coe := apply
  coe_injective' := by
    intro i₁ i₂ h
    -- Apply to 0 to extract translation equality component-wise
    have h00 : i₁.apply (0 : RationalPoint) 0 = i₂.apply (0 : RationalPoint) 0 :=
      congr_fun (congr_fun h 0) 0
    have h01 : i₁.apply (0 : RationalPoint) 1 = i₂.apply (0 : RationalPoint) 1 :=
      congr_fun (congr_fun h 0) 1
    simp only [apply, Pi.zero_apply, mul_zero, sub_self, zero_add, add_zero, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply] at h00 h01
    -- Apply to ![1, 0] to extract cos and sin
    have hcos_eq : i₁.apply (![1, 0] : RationalPoint) 0 = i₂.apply (![1, 0] : RationalPoint) 0 :=
      congr_fun (congr_fun h ![1, 0]) 0
    have hsin_eq : i₁.apply (![1, 0] : RationalPoint) 1 = i₂.apply (![1, 0] : RationalPoint) 1 :=
      congr_fun (congr_fun h ![1, 0]) 1
    simp only [apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_one, mul_zero, sub_zero, add_zero, Pi.add_apply] at hcos_eq hsin_eq
    have htrans : i₁.translation = i₂.translation := by
      funext i; fin_cases i
      · exact h00
      · exact h01
    have hcos : i₁.cos = i₂.cos := by linarith
    have hsin : i₁.sin = i₂.sin := by linarith
    obtain ⟨c1, s1, t1, v1⟩ := i₁
    obtain ⟨c2, s2, t2, v2⟩ := i₂
    simp only at hcos hsin htrans
    subst hcos; subst hsin; subst htrans
    exact congrArg (DirectIsometry.mk c1 s1 t1) (proof_irrel v1 v2)

-- TODO funlike instance

/-- Apply the isometry to a polygon -/
def applyPolygon (iso : DirectIsometry) (poly : ConvexPolygon) : ConvexPolygon where
  vertex_count := poly.vertex_count
  vertex_count_pos := poly.vertex_count_pos
  three_le_vertex_count := poly.three_le_vertex_count
  vertices := fun i => iso.apply (poly.vertices i)
  nodup := iso.apply_injective.comp poly.nodup
  vertices_extremeRationalPoints := by
    intro i j hji hji1
    have h := poly.vertices_extremeRationalPoints i j hji hji1
    simp only [NondegenPolygon.getStrictlyLeftHalfspace, RationalPoint.toStrictlyLeft,
      OpenHalfSpace.contains, decide_eq_true_eq] at h ⊢
    -- Rotations preserve dotProduct (rotate90CCW ·) · = crossProduct · ·, and
    -- det of rotation matrix = cos²+sin² = 1 preserves cross products
    have heq : RationalPoint.dotProduct
          (RationalPoint.rotate90Counterclockwise
            (iso.apply (poly.vertices (i + 1)) - iso.apply (poly.vertices i)))
          (iso.apply (poly.vertices j) - iso.apply (poly.vertices i)) =
        RationalPoint.dotProduct
          (RationalPoint.rotate90Counterclockwise
            (poly.vertices (i + 1) - poly.vertices i))
          (poly.vertices j - poly.vertices i) := by
      simp only [RationalPoint.dotProduct, RationalPoint.rotate90Counterclockwise, apply,
        Pi.sub_apply, Pi.add_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination
        ((poly.vertices (i + 1) 0 - poly.vertices i 0) * (poly.vertices j 1 - poly.vertices i 1) -
         (poly.vertices (i + 1) 1 - poly.vertices i 1) * (poly.vertices j 0 - poly.vertices i 0)) *
        iso.isValid
    linarith

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
