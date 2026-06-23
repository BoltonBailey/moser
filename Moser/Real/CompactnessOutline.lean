import Mathlib
import Moser.Real.GridEpsilonNet

/-!
# Compactness outline for the Moser worm problem

This file formalizes the blueprint `compactness-outline`: worms as `1`-Lipschitz
curves `[0,1] → ℝ²`, their `ε`-thickenings, the finite grid `ε`-net
(`thm:finiteEpsilonNet`), the Moser cover number, and the lower/upper bounds
together with the planar Steiner formula bounding the gap between them.

The reusable grid machinery (grid points, `GridNetWorms`, the rounding map and
the piecewise-linear interpolant) lives in `Moser.Real.GridEpsilonNet`, which
this file imports.

We mirror the canonical formalization of worms used in `FormalConjectures`
(`MoserWorm`): a worm is represented by the *range* of a `1`-Lipschitz function
from `[0,1]` to the Euclidean plane, and an (orientation-preserving) isometry is
a linear isometry equivalence with determinant `1` followed by a translation.
-/

open MeasureTheory
open scoped ENNReal

namespace Moser.CompactnessOutline

/-- The real Euclidean plane `ℝ²`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Worms and thickenings -/

/-- **Worm** (`def:worm`).
A *worm* is a `1`-Lipschitz curve `f : [0,1] → ℝ²`. Following the canonical
Mathlib formalization, the set of worms is the set of *ranges* of `1`-Lipschitz
functions from `[0,1]` to `ℝ²`. -/
def Worms : Set (Set ℝ²) :=
  {s | ∃ f : (Set.Icc (0 : ℝ) 1) → ℝ², LipschitzWith 1 f ∧ Set.range f = s}

/-- **Pinned worm** (`def:pinnedWorm`).
A worm `f` is *pinned* if `f 0 = (0,0)`. The set of pinned worms is the set of
ranges of `1`-Lipschitz functions `[0,1] → ℝ²` whose value at `0` is the origin. -/
def PinnedWorms : Set (Set ℝ²) :=
  {s | ∃ f : (Set.Icc (0 : ℝ) 1) → ℝ²,
      LipschitzWith 1 f ∧ f ⟨0, Set.left_mem_Icc.2 zero_le_one⟩ = 0 ∧ Set.range f = s}

/-- **`ε`-thickening** (`def:thickening`).
For `A ⊆ ℝ²` and `ε ≥ 0`, the `ε`-thickening of `A` is the closed
`ε`-neighbourhood `{x | dist x A ≤ ε}`. This is exactly `Metric.cthickening`,
recorded here for reference; downstream declarations use `Metric.cthickening`
directly. -/
example (ε : ℝ) (A : Set ℝ²) : Set ℝ² := Metric.cthickening ε A

/-- **`ε`-net of worms** (`def:epsilonNet`).
Let `ε > 0`. A set `S` of worms is an *`ε`-net of worms* if the image of every
pinned worm is contained in the `ε`-thickening of (the image of) some element of
`S`. -/
def IsEpsilonNet (ε : ℝ) (S : Set (Set ℝ²)) : Prop :=
  ∀ s ∈ PinnedWorms, ∃ t ∈ S, s ⊆ Metric.cthickening ε t

/-! ## A finite `ε`-net of polygonal worms -/

/-- With `k` and `δ` chosen so that `1/k < ε/2` and `2δk + δ < ε/2`, the set of
grid polygonal worms with nodes within distance `1` of the origin is an
`ε`-net of worms. -/
private lemma gridNetWorms_isEpsilonNet (ε : ℝ) (_hε : 0 < ε)
    (k : ℕ) (hk0 : 0 < k) (δ : ℝ) (hδ : 0 < δ) (h2δk : 2 * δ * (k : ℝ) ≤ 1)
    (hk : (1 : ℝ) / k < ε / 2) (hkδ : 2 * δ * (k : ℝ) + δ < ε / 2) :
    IsEpsilonNet ε (GridNetWorms k δ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
  intro s hs
  obtain ⟨f, hlip, hf0, hfrange⟩ := hs
  set L : ℝ := 1 - 2 * δ * (k : ℝ) with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; linarith [h2δk]
  have hL1 : L ≤ 1 := by rw [hLdef]; nlinarith [hδ, hkR]
  have htpmem : ∀ m : ℕ, min ((m : ℝ) / (k : ℝ)) 1 ∈ Set.Icc (0 : ℝ) 1 :=
    fun m => ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  set tp : ℕ → Set.Icc (0 : ℝ) 1 := fun m => ⟨min ((m : ℝ) / (k : ℝ)) 1, htpmem m⟩ with htpdef
  have htpval : ∀ m : ℕ, m ≤ k → (tp m : ℝ) = (m : ℝ) / (k : ℝ) := by
    intro m hm
    change min ((m : ℝ) / (k : ℝ)) 1 = (m : ℝ) / (k : ℝ)
    exact min_eq_left ((div_le_one hkR).mpr (by exact_mod_cast hm))
  set p : ℕ → ℝ² := fun m => gridRound δ (L • f (tp m)) with hpdef
  have htp0 : tp 0 = ⟨(0 : ℝ), Set.left_mem_Icc.2 zero_le_one⟩ := by
    apply Subtype.ext; simp [htpdef]
  have hf_tp0 : f (tp 0) = 0 := by rw [htp0, hf0]
  have hp0 : p 0 = 0 := by
    change gridRound δ (L • f (tp 0)) = 0
    rw [hf_tp0, smul_zero, gridRound_zero]
  have hat0 : (interp k p) ⟨(0 : ℝ), Set.left_mem_Icc.2 zero_le_one⟩ = 0 := by
    rw [interp_eq hk0 p _ 0 0 hk0 ⟨le_refl 0, zero_le_one⟩ (by simp)]
    simp [hp0]
  have hgap : ∀ j < k, ‖p (j + 1) - p j‖ ≤ 1 / (k : ℝ) := by
    intro j hj
    rw [← dist_eq_norm]
    have hstep : dist (L • f (tp (j + 1))) (L • f (tp j)) ≤ L * (1 / (k : ℝ)) := by
      have heq : dist (L • f (tp (j + 1))) (L • f (tp j))
          = L * dist (f (tp (j + 1))) (f (tp j)) := by
        rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hL0]
      rw [heq]
      have hfd : dist (f (tp (j + 1))) (f (tp j)) ≤ 1 / (k : ℝ) := by
        refine le_trans (by simpa using hlip.dist_le_mul (tp (j + 1)) (tp j)) ?_
        rw [Subtype.dist_eq, Real.dist_eq, htpval (j + 1) hj, htpval j (by omega),
          div_sub_div_same]
        rw [show ((j + 1 : ℕ) : ℝ) - (j : ℝ) = 1 by push_cast; ring, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left hfd hL0
    calc dist (p (j + 1)) (p j)
        ≤ dist (p (j + 1)) (L • f (tp (j + 1))) + dist (L • f (tp (j + 1))) (p j) :=
          dist_triangle _ _ _
      _ ≤ dist (p (j + 1)) (L • f (tp (j + 1)))
          + (dist (L • f (tp (j + 1))) (L • f (tp j)) + dist (L • f (tp j)) (p j)) := by
          have := dist_triangle (L • f (tp (j + 1))) (L • f (tp j)) (p j); linarith
      _ ≤ δ + (L * (1 / (k : ℝ)) + δ) := by
          refine add_le_add (gridRound_dist_le δ hδ _) (add_le_add hstep ?_)
          rw [dist_comm]; exact gridRound_dist_le δ hδ _
      _ = 1 / (k : ℝ) := by rw [hLdef]; field_simp; ring
  have hdistnode : ∀ n, n ≤ k → dist (p n) 0 ≤ 1 := by
    intro n _
    have hfn : ‖f (tp n)‖ ≤ 1 := by
      have h1 := hlip.dist_le_mul (tp n) (tp 0)
      rw [hf_tp0, dist_zero_right] at h1
      refine le_trans (by simpa using h1) ?_
      rw [Subtype.dist_eq, Real.dist_eq, htpval 0 (Nat.zero_le k)]
      simp only [Nat.cast_zero, zero_div, sub_zero]
      rw [abs_of_nonneg (tp n).2.1]
      exact (tp n).2.2
    calc dist (p n) 0 ≤ dist (p n) (L • f (tp n)) + dist (L • f (tp n)) 0 := dist_triangle _ _ _
      _ ≤ δ + L * 1 := by
          refine add_le_add (gridRound_dist_le δ hδ _) ?_
          rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL0]
          exact mul_le_mul_of_nonneg_left hfn hL0
      _ ≤ 1 := by rw [mul_one, hLdef]; nlinarith [hδ, hk1]
  refine ⟨Set.range (interp k p),
    ⟨interp k p, p, interp_lipschitz hk0 p hgap, hat0, hp0,
      fun n => gridRound_isGrid δ (L • f (tp n)), hdistnode,
      fun x n t hn ht hx => interp_eq hk0 p x n t hn ht hx, rfl⟩, ?_⟩
  rw [← hfrange]
  rintro y ⟨x, rfl⟩
  obtain ⟨n, t, hn, htmem, hx⟩ := exists_grid_decomp hk0 x
  obtain ⟨ht0, ht1⟩ := htmem
  have hfx1 : ‖f x‖ ≤ 1 := by
    have h1 := hlip.dist_le_mul x (tp 0)
    rw [hf_tp0, dist_zero_right] at h1
    refine le_trans (by simpa using h1) ?_
    rw [Subtype.dist_eq, Real.dist_eq, htpval 0 (Nat.zero_le k)]
    simp only [Nat.cast_zero, zero_div, sub_zero]
    rw [abs_of_nonneg x.2.1]; exact x.2.2
  have hd_n : ‖f x - f (tp n)‖ ≤ t / (k : ℝ) := by
    rw [← dist_eq_norm]
    refine le_trans (by simpa using hlip.dist_le_mul x (tp n)) ?_
    rw [Subtype.dist_eq, Real.dist_eq, hx, htpval n (le_of_lt hn), div_sub_div_same,
      show ((n : ℝ) + t) - (n : ℝ) = t by ring]
    exact le_of_eq (abs_of_nonneg (div_nonneg ht0 hkR.le))
  have hd_n1 : ‖f x - f (tp (n + 1))‖ ≤ (1 - t) / (k : ℝ) := by
    rw [← dist_eq_norm]
    refine le_trans (by simpa using hlip.dist_le_mul x (tp (n + 1))) ?_
    rw [Subtype.dist_eq, Real.dist_eq, hx, htpval (n + 1) hn, div_sub_div_same,
      show ((n : ℝ) + t) - ((n + 1 : ℕ) : ℝ) = -(1 - t) by push_cast; ring, neg_div, abs_neg]
    exact le_of_eq (abs_of_nonneg (div_nonneg (by linarith) hkR.le))
  have hinterpx : interp k p x = (1 - t) • p n + t • p (n + 1) :=
    interp_eq hk0 p x n t hn ⟨ht0, ht1⟩ hx
  have hT1 : dist (f x) (L • f x) ≤ 2 * δ * (k : ℝ) := by
    rw [dist_eq_norm, show f x - L • f x = (1 - L) • f x by module, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by linarith [hL1]),
      show (1 : ℝ) - L = 2 * δ * (k : ℝ) by rw [hLdef]; ring]
    nlinarith [hfx1, (by positivity : (0 : ℝ) ≤ 2 * δ * (k : ℝ))]
  have hT2 : dist (L • f x)
      ((1 - t) • (L • f (tp n)) + t • (L • f (tp (n + 1)))) ≤ 1 / (k : ℝ) := by
    rw [dist_eq_norm, show L • f x - ((1 - t) • (L • f (tp n)) + t • (L • f (tp (n + 1))))
        = L • ((1 - t) • (f x - f (tp n)) + t • (f x - f (tp (n + 1)))) by module,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hL0]
    have hbnd : ‖(1 - t) • (f x - f (tp n)) + t • (f x - f (tp (n + 1)))‖ ≤ 1 / (k : ℝ) := by
      calc ‖(1 - t) • (f x - f (tp n)) + t • (f x - f (tp (n + 1)))‖
          ≤ (1 - t) * ‖f x - f (tp n)‖ + t * ‖f x - f (tp (n + 1))‖ := by
            refine le_trans (norm_add_le _ _) ?_
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith), abs_of_nonneg ht0]
        _ ≤ (1 - t) * (t / (k : ℝ)) + t * ((1 - t) / (k : ℝ)) :=
            add_le_add (mul_le_mul_of_nonneg_left hd_n (by linarith))
              (mul_le_mul_of_nonneg_left hd_n1 ht0)
        _ ≤ 1 / (k : ℝ) := by
            rw [show (1 - t) * (t / (k : ℝ)) + t * ((1 - t) / (k : ℝ))
              = (2 * t * (1 - t)) / (k : ℝ) by ring]
            gcongr
            nlinarith [sq_nonneg (2 * t - 1)]
    calc L * ‖(1 - t) • (f x - f (tp n)) + t • (f x - f (tp (n + 1)))‖
        ≤ L * (1 / (k : ℝ)) := mul_le_mul_of_nonneg_left hbnd hL0
      _ ≤ 1 * (1 / (k : ℝ)) := mul_le_mul_of_nonneg_right hL1 (by positivity)
      _ = 1 / (k : ℝ) := one_mul _
  have hT3 : dist ((1 - t) • (L • f (tp n)) + t • (L • f (tp (n + 1)))) (interp k p x) ≤ δ := by
    rw [hinterpx, dist_eq_norm,
      show ((1 - t) • (L • f (tp n)) + t • (L • f (tp (n + 1))))
          - ((1 - t) • p n + t • p (n + 1))
        = (1 - t) • (L • f (tp n) - p n) + t • (L • f (tp (n + 1)) - p (n + 1)) by module]
    calc ‖(1 - t) • (L • f (tp n) - p n) + t • (L • f (tp (n + 1)) - p (n + 1))‖
        ≤ (1 - t) * ‖L • f (tp n) - p n‖ + t * ‖L • f (tp (n + 1)) - p (n + 1)‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), abs_of_nonneg ht0]
      _ ≤ (1 - t) * δ + t * δ := by
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by linarith))
            (mul_le_mul_of_nonneg_left ?_ ht0)
          · rw [← dist_eq_norm, dist_comm]; exact gridRound_dist_le δ hδ _
          · rw [← dist_eq_norm, dist_comm]; exact gridRound_dist_le δ hδ _
      _ = δ := by ring
  have hdistbound : dist (f x) (interp k p x) ≤ ε := by
    have htot : dist (f x) (interp k p x) ≤ 2 * δ * (k : ℝ) + 1 / (k : ℝ) + δ := by
      calc dist (f x) (interp k p x)
          ≤ dist (f x) (L • f x) + dist (L • f x) (interp k p x) := dist_triangle _ _ _
        _ ≤ dist (f x) (L • f x)
            + (dist (L • f x) ((1 - t) • (L • f (tp n)) + t • (L • f (tp (n + 1))))
              + dist ((1 - t) • (L • f (tp n)) + t • (L • f (tp (n + 1)))) (interp k p x)) := by
            have := dist_triangle (L • f x)
              ((1 - t) • (L • f (tp n)) + t • (L • f (tp (n + 1)))) (interp k p x); linarith
        _ ≤ 2 * δ * (k : ℝ) + (1 / (k : ℝ) + δ) := add_le_add hT1 (add_le_add hT2 hT3)
        _ = 2 * δ * (k : ℝ) + 1 / (k : ℝ) + δ := by ring
    linarith [htot, hkδ, hk]
  exact Metric.mem_cthickening_of_dist_le (f x) (interp k p x) ε
    (Set.range (interp k p)) ⟨x, rfl⟩ hdistbound

/-- **A finite grid `ε`-net exists** (`thm:finiteEpsilonNet`).
For every `ε > 0` there exist `k : ℕ` and `δ > 0` such that the set `S_ε` of
`(k, δ)`-grid polygonal worms whose nodes lie within distance `1` of the origin
is finite and is an `ε`-net of worms. -/
theorem finiteEpsilonNet (ε : ℝ) (hε : 0 < ε) :
    ∃ (k : ℕ) (δ : ℝ), 0 < δ ∧
      (GridNetWorms k δ).Finite ∧ IsEpsilonNet ε (GridNetWorms k δ) := by
  obtain ⟨k, hk0, hk⟩ : ∃ k : ℕ, 0 < k ∧ (1 : ℝ) / k < ε / 2 := by
    obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
    have h2ε : (0 : ℝ) < 2 / ε := by positivity
    have hkR : (0 : ℝ) < (k : ℝ) := lt_trans h2ε hk
    have hk0 : 0 < k := by exact_mod_cast hkR
    refine ⟨k, hk0, ?_⟩
    rw [div_lt_iff₀ hε] at hk
    rw [div_lt_iff₀ hkR]
    nlinarith [hk]
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  set δ : ℝ := min (1 / (2 * (k : ℝ))) (ε / (4 * (2 * (k : ℝ) + 1))) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have h2δk : 2 * δ * (k : ℝ) ≤ 1 := by
    have hA : δ ≤ 1 / (2 * (k : ℝ)) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at hA
    nlinarith [hA]
  have hkδ : 2 * δ * (k : ℝ) + δ < ε / 2 := by
    have hB : δ ≤ ε / (4 * (2 * (k : ℝ) + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at hB
    nlinarith [hB, hε]
  exact ⟨k, δ, hδ, gridNetWorms_finite k hk0 δ hδ,
    gridNetWorms_isEpsilonNet ε hε k hk0 δ hδ h2δk hk hkδ⟩

/-! ## Bounds on the Moser number -/

/-- The set of *worm covers*: measurable sets `X` that cover every worm by an
orientation-preserving isometry (a determinant-`1` linear isometry equivalence
followed by a translation). -/
def WormCovers : Set (Set ℝ²) :=
  {X | MeasurableSet X ∧ ∀ w ∈ Worms, ∃ (e : ℝ² ≃ₗᵢ[ℝ] ℝ²) (v : ℝ²),
      e.toLinearEquiv.det = 1 ∧ w ⊆ (fun x => e x + v) '' X}

/-- **Moser cover number** (`def:moserNumber`).
The *Moser cover number* `M` is the infimum of `area C` over all convex
covers `C`. -/
noncomputable def moserCoverNumber : ℝ≥0∞ :=
  sInf {v | ∃ C ∈ WormCovers, Convex ℝ C ∧ volume C = v}

/-- The minimal area of a convex hull of placements of a set of worms `S`: the
infimum, over translation-rotations `(g_s)_{s ∈ S}`, of the area of the convex
hull of the union of the placed images. This is `area (K S)`. -/
noncomputable def minimalCoverArea (S : Set (Set ℝ²)) : ℝ≥0∞ :=
  sInf {v | ∃ (e : Set ℝ² → ℝ² ≃ₗᵢ[ℝ] ℝ²) (t : Set ℝ² → ℝ²),
      (∀ s ∈ S, (e s).toLinearEquiv.det = 1) ∧
      volume (convexHull ℝ (⋃ s ∈ S, (fun x => (e s) x + t s) '' s)) = v}

/-- **Minimal convex cover of a finite set of worms** (`def:minimalCover`).
`IsMinimalCover S K` states that `K = K S` is a convex set realizing the minimal
area `minimalCoverArea S`, obtained as the convex hull of placements of the
elements of `S` by translation-rotations. -/
def IsMinimalCover (S : Set (Set ℝ²)) (K : Set ℝ²) : Prop :=
  Convex ℝ K ∧
  (∃ (e : Set ℝ² → ℝ² ≃ₗᵢ[ℝ] ℝ²) (t : Set ℝ² → ℝ²),
      (∀ s ∈ S, (e s).toLinearEquiv.det = 1) ∧
      K = convexHull ℝ (⋃ s ∈ S, (fun x => (e s) x + t s) '' s)) ∧
  volume K = minimalCoverArea S

/-- The perimeter of a planar set `K`, defined as the `1`-dimensional Euclidean
Hausdorff measure (arc length) of its topological frontier. -/
noncomputable def perimeter (K : Set ℝ²) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure 1 (frontier K)).toReal

/-- **Lower bound on the Moser number** (`thm:lowerBound`).
For any finite set `S` of worms, `M ≥ area (K S)`. -/
theorem lowerBound (S : Set (Set ℝ²)) (hS : S.Finite) :
    minimalCoverArea S ≤ moserCoverNumber := by
  sorry

/-- **Upper bound on the Moser number** (`thm:upperBound`).
Let `ε > 0` and let `S_ε` be a finite `ε`-net of worms with minimal convex cover
`K`. Then `M ≤ area (K^ε)`, the area of the `ε`-thickening of `K`. -/
theorem upperBound (ε : ℝ) (hε : 0 < ε) (S : Set (Set ℝ²)) (hS : S.Finite)
    (hnet : IsEpsilonNet ε S) (K : Set ℝ²) (hK : IsMinimalCover S K) :
    moserCoverNumber ≤ volume (Metric.cthickening ε K) := by
  sorry

/-- **Steiner gap between the bounds** (`thm:steinerGap`).
Let `K` be a convex body in `ℝ²` with perimeter `L`. Then for every `ε ≥ 0`,
`area (K^ε) = area K + ε L + π ε²`. -/
theorem steinerGap (K : Set ℝ²) (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (hne : K.Nonempty) (ε : ℝ) (hε : 0 ≤ ε) :
    (volume (Metric.cthickening ε K)).toReal
      = (volume K).toReal + ε * perimeter K + Real.pi * ε ^ 2 := by
  sorry

/-- **Approximating the Moser number** (`thm:approxAlgorithm`).
For any target accuracy `x > 0` there is an `ε`-net `S` and a minimal convex
cover `K` of it providing a lower bound `area (K S) ≤ M` and an upper bound
`M ≤ area (K^ε)` whose gap is at most `x`. -/
theorem approxAlgorithm (x : ℝ) (hx : 0 < x) :
    ∃ (ε : ℝ) (S : Set (Set ℝ²)) (K : Set ℝ²),
      0 < ε ∧ S.Finite ∧ IsEpsilonNet ε S ∧ IsMinimalCover S K ∧
      minimalCoverArea S ≤ moserCoverNumber ∧
      moserCoverNumber ≤ volume (Metric.cthickening ε K) ∧
      (volume (Metric.cthickening ε K)).toReal - (minimalCoverArea S).toReal ≤ x := by
  sorry

end Moser.CompactnessOutline
