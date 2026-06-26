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
def IsWormEpsilonNet (ε : ℝ) (S : Set (Set ℝ²)) : Prop :=
  ∀ s ∈ PinnedWorms, ∃ t ∈ S, s ⊆ Metric.cthickening ε t

/-! ## A finite `ε`-net of polygonal worms -/

/-- With `k` and `δ` chosen so that `1/k < ε/2` and `2δk + δ < ε/2`, the set of
grid polygonal worms with nodes within distance `1` of the origin is an
`ε`-net of worms. -/
private lemma gridNetWorms_isEpsilonNet (ε : ℝ) (_hε : 0 < ε)
    (k : ℕ) (hk0 : 0 < k) (δ : ℝ) (hδ : 0 < δ) (h2δk : 2 * δ * (k : ℝ) ≤ 1)
    (hk : (1 : ℝ) / k < ε / 2) (hkδ : 2 * δ * (k : ℝ) + δ < ε / 2) :
    IsWormEpsilonNet ε (GridNetWorms k δ) := by
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
theorem finiteWormEpsilonNet (ε : ℝ) (hε : 0 < ε) :
    ∃ (k : ℕ) (δ : ℝ), 0 < δ ∧
      (GridNetWorms k δ).Finite ∧ IsWormEpsilonNet ε (GridNetWorms k δ) := by
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

/-- The infimum of `volume X` over all planar sets `X` satisfying a predicate
`P`. -/
noncomputable def minimalVolume (P : Set ℝ² → Prop) : ℝ≥0∞ :=
  sInf {v | ∃ X, P X ∧ volume X = v}

/-- A map `g : ℝ² → ℝ²` is an *orientation-preserving isometry* when it has the
form `x ↦ e x + v` for some determinant-`1` linear isometry equivalence `e` and
translation `v`. -/
def IsOrientationPreservingIsometry (g : ℝ² → ℝ²) : Prop :=
  ∃ (e : ℝ² ≃ₗᵢ[ℝ] ℝ²) (v : ℝ²),
      e.toLinearEquiv.det = 1 ∧ g = fun x => e x + v

/-- The inverse of an orientation-preserving isometry is again one, and is a
two-sided inverse of the original map. -/
private lemma IsOrientationPreservingIsometry.exists_symm {g : ℝ² → ℝ²}
    (hg : IsOrientationPreservingIsometry g) :
    ∃ g', IsOrientationPreservingIsometry g' ∧
      Function.LeftInverse g' g ∧ Function.RightInverse g' g := by
  obtain ⟨e, v, hdet, rfl⟩ := hg
  refine ⟨fun y => e.symm (y - v), ⟨e.symm, -(e.symm v), ?_, ?_⟩, ?_, ?_⟩
  · rw [LinearIsometryEquiv.toLinearEquiv_symm, LinearEquiv.det_symm, map_inv, hdet, inv_one]
  · funext y
    rw [map_sub, sub_eq_add_neg]
  · intro x; simp
  · intro y; simp

/-- An orientation-preserving isometry is an isometry. -/
private lemma IsOrientationPreservingIsometry.isometry {g : ℝ² → ℝ²}
    (hg : IsOrientationPreservingIsometry g) : Isometry g := by
  obtain ⟨e, v, _, rfl⟩ := hg
  refine Isometry.of_dist_eq (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, show e x + v - (e y + v) = e x - e y by abel,
    ← map_sub, e.norm_map]

/-- `CoversByIsometry X w` states that `X` covers the set `w` by an
orientation-preserving isometry: some such isometry places a copy of `X` over
`w`. (Used with `w` a worm in `WormCovers`, but the relation itself is generic.) -/
def CoversByIsometry (X w : Set ℝ²) : Prop :=
  ∃ g : ℝ² → ℝ², IsOrientationPreservingIsometry g ∧ w ⊆ g '' X

/-- The set of *worm covers*: measurable sets `X` that cover every worm by an
orientation-preserving isometry (a determinant-`1` linear isometry equivalence
followed by a translation). -/
def WormCovers : Set (Set ℝ²) :=
  {X | MeasurableSet X ∧ ∀ w ∈ Worms, CoversByIsometry X w}

/-- `IsPlacementCover S K` states that `K` contains the convex hull of placements
of the elements of `S` by translation-rotations: there is a determinant-`1` linear
isometry `e s` and translation `t s` for each `s`, and `K` contains the convex hull
of the union of the placed images. Allowing supersets (rather than insisting on the
hull itself) makes the predicate antitone in `S` — see `IsPlacementCover.of_subset`. -/
def IsPlacementCover (S : Set (Set ℝ²)) (K : Set ℝ²) : Prop :=
  ∃ g : Set ℝ² → ℝ² → ℝ²,
      (∀ s ∈ S, IsOrientationPreservingIsometry (g s)) ∧
      convexHull ℝ (⋃ s ∈ S, g s '' s) ⊆ K

/-- A placement cover of a larger set of worms is also a placement cover of any
subset: reuse the same placements and shrink the union of placed images. -/
lemma IsPlacementCover.of_subset {S T : Set (Set ℝ²)} {K : Set ℝ²}
    (hST : S ⊆ T) (hK : IsPlacementCover T K) : IsPlacementCover S K := by
  obtain ⟨g, hgop, hsub⟩ := hK
  exact ⟨g, fun s hs => hgop s (hST hs),
    (convexHull_mono (Set.biUnion_subset_biUnion_left hST)).trans hsub⟩

/-- The minimal area of a convex hull of placements of a set of worms `S`: the
infimum, over translation-rotations `(g_s)_{s ∈ S}`, of the area of the convex
hull of the union of the placed images. This is `area (K S)`. -/
noncomputable def minimalCoverArea (S : Set (Set ℝ²)) : ℝ≥0∞ :=
  minimalVolume (IsPlacementCover S)

/-- `minimalCoverArea` is monotone in its set of worms: enlarging the set can only
increase the minimal cover area. Indeed, any placement cover of the larger set `T`
restricts (via the same family of placements) to a placement cover of `S ⊆ T`, and
the convex hull of the placed copies of `S` is contained in that of `T`, hence of
no larger area. -/
lemma minimalCoverArea_mono {S T : Set (Set ℝ²)} (hST : S ⊆ T) :
    minimalCoverArea S ≤ minimalCoverArea T := by
  simp only [minimalCoverArea, minimalVolume]
  -- A placement cover of the larger set `T` is also a placement cover of `S`, so the
  -- set of achievable areas for `T` is contained in that for `S`; `sInf` is antitone.
  refine sInf_le_sInf ?_
  rintro v ⟨K, hK, rfl⟩
  exact ⟨K, hK.of_subset hST, rfl⟩

/-- **Moser cover number** (`def:moserNumber`).
The *Moser cover number* `M` is the minimal area of a convex hull of placements
of *all* worms, i.e. `minimalCoverArea Worms`. Equivalently, it is the infimum of
`area C` over all convex covers `C` (a convex hull of placements is itself a
convex cover, and every convex cover contains such a hull). -/
noncomputable def moserCoverNumber : ℝ≥0∞ :=
  minimalCoverArea Worms

/-- **Minimal convex cover of a finite set of worms** (`def:minimalCover`).
`IsMinimalCover S K` states that `K = K S` is a convex set realizing the minimal
area `minimalCoverArea S` while containing the convex hull of placements of the
elements of `S` by translation-rotations. Since its area equals the minimum, `K`
agrees up to null sets with the optimal such hull. -/
def IsMinimalCover (S : Set (Set ℝ²)) (K : Set ℝ²) : Prop :=
  Convex ℝ K ∧ IsPlacementCover S K ∧ volume K = minimalCoverArea S

/-- The perimeter of a planar set `K`, defined as the `1`-dimensional Euclidean
Hausdorff measure (arc length) of its topological frontier. -/
noncomputable def perimeter (K : Set ℝ²) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure 1 (frontier K)).toReal

/-- **Lower bound on the Moser number** (`thm:lowerBound`).
For any finite set `S` of worms, `M ≥ area (K S)`. -/
theorem moserCoverNumber_lowerBound (S : Set (Set ℝ²)) (_hS : S.Finite)
    (hSworms : S ⊆ Worms) :
    minimalCoverArea S ≤ moserCoverNumber :=
  -- `M = minimalCoverArea Worms`, so this is just monotonicity of `minimalCoverArea`
  -- applied to `S ⊆ Worms`.
  minimalCoverArea_mono hSworms

/-- **Upper bound on the Moser number** (`thm:upperBound`).
Let `ε > 0` and let `S_ε` be a finite `ε`-net of worms with minimal convex cover
`K`. Then `M ≤ area (K^ε)`, the area of the `ε`-thickening of `K`. -/
theorem moserCoverNumber_upperBound (ε : ℝ) (_hε : 0 < ε) (S : Set (Set ℝ²)) (_hS : S.Finite)
    (hnet : IsWormEpsilonNet ε S) (K : Set ℝ²) (hK : IsMinimalCover S K) :
    moserCoverNumber ≤ volume (Metric.cthickening ε K) := by
  obtain ⟨hKconv, ⟨hfun, hfunop, hKeq⟩, _⟩ := hK
  -- Each worm admits an orientation-preserving placement into the `ε`-thickening of
  -- `K`; the convex hull of all these placements is a placement cover of `Worms`
  -- contained in `K^ε`, hence of no larger area.
  have hplace : ∀ w ∈ Worms, ∃ g, IsOrientationPreservingIsometry g ∧
      g '' w ⊆ Metric.cthickening ε K := by
    rintro w ⟨f, hlip, rfl⟩
    set f₀ : ℝ² := f ⟨0, Set.left_mem_Icc.2 zero_le_one⟩ with hf₀
    -- Pin the worm by translating its start to the origin.
    set f' : (Set.Icc (0 : ℝ) 1) → ℝ² := fun x => f x - f₀ with hf'
    have hlip' : LipschitzWith 1 f' := by
      rw [lipschitzWith_iff_dist_le_mul] at hlip ⊢
      intro x y
      refine le_trans (le_of_eq ?_) (hlip x y)
      simp only [hf', dist_eq_norm]; congr 1; abel
    have hf'0 : f' ⟨0, Set.left_mem_Icc.2 zero_le_one⟩ = 0 := by rw [hf']; simp [hf₀]
    have hpin : Set.range f' ∈ PinnedWorms := ⟨f', hlip', hf'0, rfl⟩
    -- Find a net element near the pinned worm and the placement carrying it into `K`.
    obtain ⟨t, htS, htsub⟩ := hnet _ hpin
    have htsubK : hfun t '' t ⊆ K :=
      ((Set.subset_biUnion_of_mem (u := fun s => hfun s '' s) htS).trans
        (subset_convexHull ℝ _)).trans hKeq
    have htiso : Isometry (hfun t) := (hfunop t htS).isometry
    -- The placement maps the `ε`-thickening of the net element into that of `K`.
    have hmap : ∀ z ∈ Metric.cthickening ε t, hfun t z ∈ Metric.cthickening ε K := by
      intro z hz
      rw [Metric.mem_cthickening_iff] at hz ⊢
      refine le_trans (Metric.infEDist_anti htsubK) ?_
      rw [Metric.infEDist_image htiso]
      exact hz
    -- The composite "pin then place" is an orientation-preserving isometry carrying
    -- the worm `w = range f` into the `ε`-thickening of `K`.
    obtain ⟨e, v, hdet, hfe⟩ := hfunop t htS
    refine ⟨fun y => hfun t (y - f₀), ⟨e, v - e f₀, hdet, ?_⟩, ?_⟩
    · funext y; simp only [hfe, map_sub]; abel
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact hmap _ (htsub (Set.mem_range_self x))
  choose! gfun hgop hgsub using hplace
  -- The `ε`-thickening of `K` is convex and contains the convex hull of all these
  -- placements, so it is itself a placement cover of `Worms`.
  have hPC : IsPlacementCover Worms (Metric.cthickening ε K) :=
    ⟨gfun, fun w hw => hgop w hw,
      convexHull_min (Set.iUnion₂_subset fun w hw => hgsub w hw) (hKconv.cthickening ε)⟩
  rw [moserCoverNumber, minimalCoverArea, minimalVolume]
  exact sInf_le ⟨Metric.cthickening ε K, hPC, rfl⟩

/-- **Steiner gap between the bounds** (`thm:steinerGap`).
Let `K` be a convex body in `ℝ²` with perimeter `L`. Then for every `ε ≥ 0`,
`area (K^ε) = area K + ε L + π ε²`. -/
theorem steinerGap (K : Set ℝ²) (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (hne : K.Nonempty) (ε : ℝ) (hε : 0 ≤ ε) :
    (volume (Metric.cthickening ε K)).toReal
      = (volume K).toReal + ε * perimeter K + Real.pi * ε ^ 2 := by
  -- This is the planar Steiner formula for convex bodies. Mathlib currently has
  -- no Steiner formula / mixed-volume / intrinsic-volume theory, so a full proof
  -- would require building that convex-geometry machinery from scratch. Left as a
  -- standalone TODO; the bounds above (`moserCoverNumber_lowerBound`,
  -- `moserCoverNumber_upperBound`) do not depend on it.
  sorry

/-- **Approximating the Moser number** (`thm:approxAlgorithm`).
For any target accuracy `x > 0` there is an `ε`-net `S` and a minimal convex
cover `K` of it providing a lower bound `area (K S) ≤ M` and an upper bound
`M ≤ area (K^ε)` whose gap is at most `x`. -/
theorem approxAlgorithm (x : ℝ) (hx : 0 < x) :
    ∃ (ε : ℝ) (S : Set (Set ℝ²)) (K : Set ℝ²),
      0 < ε ∧ S.Finite ∧ IsWormEpsilonNet ε S ∧ IsMinimalCover S K ∧
      minimalCoverArea S ≤ moserCoverNumber ∧
      moserCoverNumber ≤ volume (Metric.cthickening ε K) ∧
      (volume (Metric.cthickening ε K)).toReal - (minimalCoverArea S).toReal ≤ x := by
  -- Combining the two bounds with the Steiner gap. Blocked on `steinerGap` (to
  -- control the gap by `ε L + π ε²`) and additionally requires exhibiting an
  -- area-minimizing convex cover `K` with `IsMinimalCover S K` (attainment of the
  -- infimum) together with an a priori perimeter bound on `K(Sε)`
  -- (Remark `rem:perimeterBound` in the blueprint). Left as a TODO.
  sorry

end Moser.CompactnessOutline
