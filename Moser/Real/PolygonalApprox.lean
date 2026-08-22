module

public import Mathlib
public import Moser.Real.CompactnessOutline

@[expose] public section

/-!
# Approximating worms by polygonal worms with few segments

The project notes ask for a function `ε(m)` such that every worm lies inside the
`ε(m)`-thickening of some worm made of `m` segments. This file answers that
question with `ε(m) = 1/(2m)`, by the direct construction: sample the worm at the
`m + 1` equally spaced parameters `j/m` and join consecutive samples by segments.

The notes propose instead to take supporting-line contact points and apply
Carathéodory's theorem, which yields `3m + 2` segments for a comparable accuracy;
uniform sampling is both simpler and sharper. `polygonalApprox_hausdorff` gives
the two-sided bound, and `convexHull_subset_cthickening_polygonalApprox` transfers
it to the convex hulls, which is what matters for covering problems.
-/

namespace Moser.CompactnessOutline

/-- The real Euclidean plane `ℝ²`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Polygonal worms -/

/-- **Polygonal worms with `m` segments**: unions of `m` segments joining
consecutive nodes `p 0, …, p m`, each of length at most `1/m` (so that the
polygonal path, traversed at constant speed on `[0,1]`, is `1`-Lipschitz). -/
def PolygonalWorms (m : ℕ) : Set (Set ℝ²) :=
  {s | ∃ p : ℕ → ℝ², (∀ j < m, ‖p (j + 1) - p j‖ ≤ 1 / (m : ℝ)) ∧
      s = ⋃ j : Fin m, segment ℝ (p (j : ℕ)) (p ((j : ℕ) + 1))}

/-- A polygonal worm is a worm: the piecewise-linear interpolant of its nodes is
`1`-Lipschitz and has it as range. -/
lemma polygonalWorms_subset_worms {m : ℕ} (hm : 0 < m) : PolygonalWorms m ⊆ Worms := by
  rintro s ⟨p, hgap, rfl⟩
  refine ⟨interp m p, interp_lipschitz hm p hgap, ?_⟩
  exact worm_range_eq_iUnion hm p (interp m p) (fun x n t hn ht hx => interp_eq hm p x n t hn ht hx)

/-! ## Uniform sampling -/

/-- The `j`-th sampling parameter `min (j/m) 1 ∈ [0,1]`. -/
noncomputable def nodeParam (m j : ℕ) : Set.Icc (0 : ℝ) 1 :=
  ⟨min ((j : ℝ) / m) 1, le_min (by positivity) zero_le_one, min_le_right _ _⟩

lemma nodeParam_coe {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) : (nodeParam m j : ℝ) = (j : ℝ) / m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  exact min_eq_left ((div_le_one hmR).mpr (by exact_mod_cast hj))

/-- The nodes of the uniform polygonal approximation of a worm `f`. -/
noncomputable def uniformNode (m : ℕ) (f : Set.Icc (0 : ℝ) 1 → ℝ²) (j : ℕ) : ℝ² :=
  f (nodeParam m j)

lemma uniformNode_mem_range (m : ℕ) (f : Set.Icc (0 : ℝ) 1 → ℝ²) (j : ℕ) :
    uniformNode m f j ∈ Set.range f := ⟨_, rfl⟩

/-- Consecutive samples of a `1`-Lipschitz curve are at distance at most `1/m`. -/
lemma uniformNode_gap {m : ℕ} (hm : 0 < m) {f : Set.Icc (0 : ℝ) 1 → ℝ²}
    (hlip : LipschitzWith 1 f) (j : ℕ) (hj : j < m) :
    ‖uniformNode m f (j + 1) - uniformNode m f j‖ ≤ 1 / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [← dist_eq_norm]
  refine le_trans (by simpa using hlip.dist_le_mul (nodeParam m (j + 1)) (nodeParam m j)) ?_
  rw [Subtype.dist_eq, Real.dist_eq, nodeParam_coe (j := j + 1) hm (by omega),
    nodeParam_coe (j := j) hm hj.le, div_sub_div_same,
    show ((j + 1 : ℕ) : ℝ) - (j : ℝ) = 1 by push_cast; ring, abs_of_pos (by positivity)]

/-- Every parameter is within `1/(2m)` of one of the `m + 1` sampling
parameters. -/
lemma exists_nearest_node {m : ℕ} (hm : 0 < m) (x : Set.Icc (0 : ℝ) 1) :
    ∃ j ≤ m, |(x : ℝ) - (j : ℝ) / m| ≤ 1 / (2 * m) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := x.2.1
  have hx1 : (x : ℝ) ≤ 1 := x.2.2
  have h0 : (0 : ℝ) ≤ (x : ℝ) * m + 1 / 2 := by positivity
  set j : ℕ := ⌊(x : ℝ) * m + 1 / 2⌋₊ with hj
  have hfl : (j : ℝ) ≤ (x : ℝ) * m + 1 / 2 := Nat.floor_le h0
  have hfl2 : (x : ℝ) * m + 1 / 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨j, ?_, ?_⟩
  · by_contra hcon
    have : (m : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ j)
    nlinarith [hx1, hmR]
  · have key : |(x : ℝ) * m - (j : ℝ)| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    have heq : (x : ℝ) - (j : ℝ) / m = ((x : ℝ) * m - (j : ℝ)) / m := by field_simp
    rw [heq, abs_div, abs_of_pos hmR, div_le_iff₀ hmR]
    have : 1 / (2 * (m : ℝ)) * m = 1 / 2 := by field_simp
    linarith [key, this]

/-- A sample point is a vertex of the interpolant, hence lies on it. -/
lemma uniformNode_mem_range_interp {m : ℕ} (hm : 0 < m) (f : Set.Icc (0 : ℝ) 1 → ℝ²)
    {j : ℕ} (hj : j ≤ m) :
    uniformNode m f j ∈ Set.range (interp m (uniformNode m f)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  refine ⟨nodeParam m j, ?_⟩
  rcases lt_or_eq_of_le hj with h | h
  · rw [interp_eq hm _ _ j 0 h ⟨le_rfl, zero_le_one⟩
      (by rw [nodeParam_coe hm hj]; ring)]
    simp
  · subst h
    rw [interp_eq hm _ _ (j - 1) 1 (by omega) ⟨zero_le_one, le_rfl⟩ ?_]
    · have : j - 1 + 1 = j := by omega
      rw [this]; simp
    · rw [nodeParam_coe hm le_rfl, Nat.cast_sub hm]
      push_cast; field_simp; ring

/-! ## The approximation theorem -/

/-- **Uniform polygonal approximation** (answering the `ε(m)` question of the
notes). Every worm is within Hausdorff distance `1/(2m)` of a polygonal worm with
`m` segments, namely the one obtained by joining its samples at the parameters
`j/m`. -/
theorem exists_polygonalWorm_approx {m : ℕ} (hm : 0 < m) {w : Set ℝ²} (hw : w ∈ Worms) :
    ∃ w' ∈ PolygonalWorms m,
      w ⊆ Metric.cthickening (1 / (2 * m)) w' ∧ w' ⊆ Metric.cthickening (1 / (2 * m)) w := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨f, hlip, rfl⟩ := hw
  set p : ℕ → ℝ² := uniformNode m f with hp
  have hgap : ∀ j < m, ‖p (j + 1) - p j‖ ≤ 1 / (m : ℝ) := uniformNode_gap hm hlip
  refine ⟨Set.range (interp m p), ⟨p, hgap, worm_range_eq_iUnion hm p (interp m p)
      (fun x n t hn ht hx => interp_eq hm p x n t hn ht hx)⟩, ?_, ?_⟩
  · -- every point of the worm is near a sample, hence near the polygon
    rintro _ ⟨x, rfl⟩
    obtain ⟨j, hj, hdist⟩ := exists_nearest_node hm x
    refine Metric.mem_cthickening_of_dist_le _ (p j) _ _
      (uniformNode_mem_range_interp hm f hj) ?_
    refine le_trans (by simpa using hlip.dist_le_mul x (nodeParam m j)) ?_
    rw [Subtype.dist_eq, Real.dist_eq, nodeParam_coe hm hj]
    exact hdist
  · -- every point of the polygon is within half a step of one of its endpoints
    rintro _ ⟨x, rfl⟩
    obtain ⟨n, t, hn, ⟨ht0, ht1⟩, hx⟩ := exists_grid_decomp hm x
    rw [interp_eq hm p x n t hn ⟨ht0, ht1⟩ hx]
    rcases le_total t (1 / 2) with h | h
    · refine Metric.mem_cthickening_of_dist_le _ (p n) _ _ (uniformNode_mem_range m f n) ?_
      rw [dist_eq_norm, show (1 - t) • p n + t • p (n + 1) - p n = t • (p (n + 1) - p n) by module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      calc t * ‖p (n + 1) - p n‖ ≤ (1 / 2) * (1 / (m : ℝ)) := by
            refine mul_le_mul h (hgap n hn) (norm_nonneg _) (by norm_num)
        _ = 1 / (2 * (m : ℝ)) := by ring
    · refine Metric.mem_cthickening_of_dist_le _ (p (n + 1)) _ _
        (uniformNode_mem_range m f (n + 1)) ?_
      rw [dist_eq_norm,
        show (1 - t) • p n + t • p (n + 1) - p (n + 1) = (1 - t) • (p n - p (n + 1)) by module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_sub_rev]
      calc (1 - t) * ‖p (n + 1) - p n‖ ≤ (1 / 2) * (1 / (m : ℝ)) := by
            refine mul_le_mul (by linarith) (hgap n hn) (norm_nonneg _) (by norm_num)
        _ = 1 / (2 * (m : ℝ)) := by ring

/-- A thickening bound between sets transfers to their convex hulls, because the
thickening of a convex set is convex. -/
lemma convexHull_subset_cthickening {ε : ℝ} {A B : Set ℝ²} (h : A ⊆ Metric.cthickening ε B) :
    convexHull ℝ A ⊆ Metric.cthickening ε (convexHull ℝ B) :=
  convexHull_min (h.trans (Metric.cthickening_subset_of_subset _
    (subset_convexHull ℝ B))) ((convex_convexHull ℝ B).cthickening ε)

/-- **Hulls of worms are approximated by hulls of polygonal worms.** -/
theorem exists_polygonalWorm_convexHull_approx {m : ℕ} (hm : 0 < m) {w : Set ℝ²}
    (hw : w ∈ Worms) :
    ∃ w' ∈ PolygonalWorms m,
      convexHull ℝ w ⊆ Metric.cthickening (1 / (2 * m)) (convexHull ℝ w') ∧
        convexHull ℝ w' ⊆ Metric.cthickening (1 / (2 * m)) (convexHull ℝ w) := by
  obtain ⟨w', hw', h1, h2⟩ := exists_polygonalWorm_approx hm hw
  exact ⟨w', hw', convexHull_subset_cthickening h1, convexHull_subset_cthickening h2⟩

end Moser.CompactnessOutline

end
