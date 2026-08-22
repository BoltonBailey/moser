module

public import Mathlib
public import Moser.Real.CompactnessOutline

@[expose] public section

/-!
# Pruning bounds for the search for good worms

The project notes describe a branch-and-bound search for worms that violate a
candidate cover, resting on the following observation: if the part of a worm
already pinned down needs length `L` to be covered, then only `1 - L` of the
worm's length is left, so no point of the worm can be further than `1 - L` from
the part already pinned down.

This file makes that precise. The quantity "length needed to cover a set" is
`minCoverLength`, the infimum of the lengths of `1`-Lipschitz curves whose image
contains the set; the pruning bound is
`worm_subset_cthickening_of_image_subset` and its corollary
`worm_subset_cthickening_minCoverLength`.

Note that the bound is about the distance to the *traced portion* `f '' [a,b]` of
the worm, not to the convex hull of the finitely many points already found: a
point of the worm traced between two known points can be far from their hull, so
the naive form of the claim is false.
-/

namespace Moser.CompactnessOutline

/-- The real Euclidean plane `ℝ²`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Clamping a parameter into `[0,1]` -/

/-- Clamp a real number into `[0,1]`. -/
noncomputable def clamp01 (t : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨min 1 (max 0 t), le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

@[simp] lemma clamp01_coe (t : ℝ) : (clamp01 t : ℝ) = min 1 (max 0 t) := rfl

lemma clamp01_of_mem {t : ℝ} (h : t ∈ Set.Icc (0 : ℝ) 1) : (clamp01 t : ℝ) = t := by
  rw [clamp01_coe, max_eq_right h.1, min_eq_right h.2]

lemma clamp01_lipschitz : LipschitzWith 1 clamp01 := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  rw [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq, Real.dist_eq,
    clamp01_coe, clamp01_coe, abs_le]
  constructor <;>
    · simp only [min_def, max_def]
      split_ifs <;> cases abs_cases (s - t) <;> linarith [(abs_nonneg (s - t))]

/-! ## The length needed to cover a set -/

/-- The **minimal covering length** of a planar set `A`: the infimum of the
lengths `ℓ` for which some `1`-Lipschitz curve defined on `[0, ℓ]` has image
containing `A`. -/
noncomputable def minCoverLength (A : Set ℝ²) : ℝ :=
  sInf {ℓ : ℝ | 0 ≤ ℓ ∧ ∃ f : ℝ → ℝ², LipschitzWith 1 f ∧ A ⊆ f '' Set.Icc 0 ℓ}

lemma minCoverLength_nonneg (A : Set ℝ²) : 0 ≤ minCoverLength A :=
  Real.sInf_nonneg (fun _ hx => hx.1)

/-- The portion of a worm traced on `[a,b]` is covered by a curve of length
`b - a`, so any set it contains needs at most that length to be covered. -/
lemma minCoverLength_le_of_subset_image {f : Set.Icc (0 : ℝ) 1 → ℝ²}
    (hlip : LipschitzWith 1 f) {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) (_hb : b ≤ 1)
    {P : Set ℝ²} (hP : P ⊆ f '' {x : Set.Icc (0 : ℝ) 1 | (x : ℝ) ∈ Set.Icc a b}) :
    minCoverLength P ≤ b - a := by
  refine csInf_le ⟨0, fun ℓ hℓ => hℓ.1⟩ ⟨by linarith, fun t => f (clamp01 (a + t)), ?_, ?_⟩
  · have h1 : LipschitzWith 1 (fun t : ℝ => a + t) := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro s t
      rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq,
        show a + s - (a + t) = s - t by ring]
    simpa using (hlip.comp clamp01_lipschitz).comp h1
  · rintro p hp
    obtain ⟨x, hx, rfl⟩ := hP hp
    refine ⟨(x : ℝ) - a, ⟨by simp only [sub_nonneg]; exact hx.1, by linarith [hx.2]⟩, ?_⟩
    have hcl : clamp01 (a + ((x : ℝ) - a)) = x := by
      apply Subtype.ext
      rw [show a + ((x : ℝ) - a) = (x : ℝ) by ring, clamp01_of_mem x.2]
    change f (clamp01 (a + ((x : ℝ) - a))) = f x
    rw [hcl]

/-! ## The pruning bound -/

/-- **Pruning bound.** If the portion of a worm traced on the parameter interval
`[a,b]` lies inside a set `A`, then the whole worm lies within `1 - (b - a)` of
`A`: at most `1 - (b - a)` of the worm's unit length is left over to travel away
from `A`. -/
theorem worm_subset_cthickening_of_image_subset {f : Set.Icc (0 : ℝ) 1 → ℝ²}
    (hlip : LipschitzWith 1 f) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    {A : Set ℝ²} (hA : f '' {x : Set.Icc (0 : ℝ) 1 | (x : ℝ) ∈ Set.Icc a b} ⊆ A) :
    Set.range f ⊆ Metric.cthickening (1 - (b - a)) A := by
  have hamem : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha, le_trans hab hb⟩
  have hbmem : b ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans ha hab, hb⟩
  rintro _ ⟨x, rfl⟩
  rcases le_or_gt (a : ℝ) (x : ℝ) with hxa | hxa
  · rcases le_or_gt (x : ℝ) b with hxb | hxb
    · -- inside the traced interval
      refine Metric.self_subset_cthickening A (hA ⟨x, ⟨hxa, hxb⟩, rfl⟩)
    · -- after the traced interval: at most `1 - b` of length remains
      refine Metric.mem_cthickening_of_dist_le _ (f ⟨b, hbmem⟩) _ A
        (hA ⟨⟨b, hbmem⟩, ⟨hab, le_refl b⟩, rfl⟩) ?_
      refine le_trans (by simpa using hlip.dist_le_mul x ⟨b, hbmem⟩) ?_
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (by simp only [sub_nonneg]; linarith)]
      have := x.2.2
      linarith
  · -- before the traced interval: at most `a` of length remains
    refine Metric.mem_cthickening_of_dist_le _ (f ⟨a, hamem⟩) _ A
      (hA ⟨⟨a, hamem⟩, ⟨le_refl a, hab⟩, rfl⟩) ?_
    refine le_trans (by simpa using hlip.dist_le_mul x ⟨a, hamem⟩) ?_
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (by simp only [sub_nonpos]; linarith)]
    have := x.2.1
    linarith

/-- **Pruning bound, in terms of the covering length.** If a set `P` of points of
the worm is traced on the parameter interval `[a,b]`, then no point of the worm
is further than `1 - minCoverLength P` from the traced portion. -/
theorem worm_subset_cthickening_minCoverLength {f : Set.Icc (0 : ℝ) 1 → ℝ²}
    (hlip : LipschitzWith 1 f) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    {P : Set ℝ²} (hP : P ⊆ f '' {x : Set.Icc (0 : ℝ) 1 | (x : ℝ) ∈ Set.Icc a b}) :
    Set.range f ⊆ Metric.cthickening (1 - minCoverLength P)
      (f '' {x : Set.Icc (0 : ℝ) 1 | (x : ℝ) ∈ Set.Icc a b}) :=
  le_trans (worm_subset_cthickening_of_image_subset hlip ha hab hb (le_refl _))
    (Metric.cthickening_mono (by linarith [minCoverLength_le_of_subset_image hlip ha hab hb hP]) _)

end Moser.CompactnessOutline

end
