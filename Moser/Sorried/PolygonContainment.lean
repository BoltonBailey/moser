module

public import Mathlib
public import Moser.Geometry.Polygon
public import Moser.DirectIsometry.Basic

public section

/-!
# Containment of a polygon under rigid motions

`ContainsCopyOf container worm` says that some direct (orientation-preserving)
isometry of the plane carries the region of `worm` inside the region of
`container`. This is the relation the working-set search needs to decide.

This file develops the relation itself — it is a preorder, and it is monotone in
the container — together with the rotation algebra it rests on.

## TODO

A *decision procedure* `ConvexPolygon → ConvexPolygon → Bool` for this relation,
correct with respect to `ContainsCopyOf`, is future work: the quantification is
over real rotation angles, so a rational decision procedure has to work with the
algebraic conditions on `cos θ`, `sin θ` rather than search a grid.
[This paper](https://www.cs.princeton.edu/%7Echazelle/pubs/PolygContainmentProb.pdf)
describes an efficient algorithm. Until then, `Moser.DirectIsometry.Discretization`
supplies the (finite, approximate) placements the search actually uses.
-/

namespace ConvexPolygon

open scoped Convex

/-- The real planar region of a convex polygon: the convex hull of its vertices,
cast from `ℚ` into `ℝ²`. -/
noncomputable def realCarrier (poly : ConvexPolygon ℚ) : Set (Fin 2 → ℝ) :=
  convexHull ℝ (Set.range fun i => fun j => ((poly.vertices i j : ℚ) : ℝ))

/-- A real orientation-preserving rotation by angle `θ` about the origin. -/
noncomputable def realRotate (θ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![Real.cos θ * x 0 - Real.sin θ * x 1, Real.sin θ * x 0 + Real.cos θ * x 1]

@[simp] lemma realRotate_apply_zero (θ : ℝ) (x : Fin 2 → ℝ) :
    realRotate θ x 0 = Real.cos θ * x 0 - Real.sin θ * x 1 := by simp [realRotate]

@[simp] lemma realRotate_apply_one (θ : ℝ) (x : Fin 2 → ℝ) :
    realRotate θ x 1 = Real.sin θ * x 0 + Real.cos θ * x 1 := by simp [realRotate]

@[simp] lemma realRotate_zero (x : Fin 2 → ℝ) : realRotate 0 x = x := by
  funext i; fin_cases i <;> simp

/-- Rotations are additive maps. -/
lemma realRotate_add_vec (θ : ℝ) (x y : Fin 2 → ℝ) :
    realRotate θ (x + y) = realRotate θ x + realRotate θ y := by
  funext i; fin_cases i <;> simp [Pi.add_apply] <;> ring

/-- Composing rotations adds the angles. -/
lemma realRotate_realRotate (θ₁ θ₂ : ℝ) (x : Fin 2 → ℝ) :
    realRotate θ₁ (realRotate θ₂ x) = realRotate (θ₁ + θ₂) x := by
  funext i
  fin_cases i <;> simp [Real.cos_add, Real.sin_add] <;> ring

/--
`ContainsCopyOf container worm` : some rotation followed by some translation
carries the worm's region inside the container's region.
-/
def ContainsCopyOf (container worm : ConvexPolygon ℚ) : Prop :=
  ∃ (θ : ℝ) (t : Fin 2 → ℝ),
    (fun x => realRotate θ x + t) '' worm.realCarrier ⊆ container.realCarrier

lemma ContainsCopyOf.refl (poly : ConvexPolygon ℚ) : ContainsCopyOf poly poly := by
  refine ⟨0, 0, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  simpa using hx

lemma ContainsCopyOf.trans {a b c : ConvexPolygon ℚ}
    (hab : ContainsCopyOf a b) (hbc : ContainsCopyOf b c) : ContainsCopyOf a c := by
  obtain ⟨θ₁, t₁, h₁⟩ := hab
  obtain ⟨θ₂, t₂, h₂⟩ := hbc
  refine ⟨θ₁ + θ₂, realRotate θ₁ t₂ + t₁, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hstep : realRotate (θ₁ + θ₂) x + (realRotate θ₁ t₂ + t₁)
      = realRotate θ₁ (realRotate θ₂ x + t₂) + t₁ := by
    rw [realRotate_add_vec, realRotate_realRotate]
    abel
  show realRotate (θ₁ + θ₂) x + (realRotate θ₁ t₂ + t₁) ∈ a.realCarrier
  rw [hstep]
  exact h₁ ⟨realRotate θ₂ x + t₂, h₂ ⟨x, hx, rfl⟩, rfl⟩

/-- Enlarging the container preserves containment of a copy. -/
lemma ContainsCopyOf.mono_container {a a' w : ConvexPolygon ℚ}
    (h : a.realCarrier ⊆ a'.realCarrier) (hc : ContainsCopyOf a w) : ContainsCopyOf a' w := by
  obtain ⟨θ, t, hsub⟩ := hc
  exact ⟨θ, t, hsub.trans h⟩

/-- Shrinking the worm preserves containment of a copy. -/
lemma ContainsCopyOf.mono_worm {a w w' : ConvexPolygon ℚ}
    (h : w'.realCarrier ⊆ w.realCarrier) (hc : ContainsCopyOf a w) : ContainsCopyOf a w' := by
  obtain ⟨θ, t, hsub⟩ := hc
  exact ⟨θ, t, (Set.image_mono h).trans hsub⟩

end ConvexPolygon

end
