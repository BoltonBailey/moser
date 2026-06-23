import Mathlib
import Moser.Real.CompactnessOutline

/-!
# A finite grid `ε`-net for the Moser worm problem

This file builds the finite grid `ε`-net of `thm:finiteEpsilonNet`: grid points,
`(k, δ)`-grid polygonal worms, the candidate net `GridNetWorms`, and the proof
that for every `ε > 0` there exist `k` and `δ > 0` making this net finite and an
`ε`-net of worms.

The worm definitions (`Worms`, `PinnedWorms`, `IsEpsilonNet`) and the
Moser-number bounds live in `Moser.Real.CompactnessOutline`, which this file
imports.
-/

namespace Moser.CompactnessOutline

/-- The real Euclidean plane `ℝ²`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Grid points and grid polygonal worms -/

/-- A point `p ∈ ℝ²` lies on the grid `δℤ × δℤ`. -/
def IsGridPoint (δ : ℝ) (p : ℝ²) : Prop :=
  ∃ a b : ℤ, p 0 = δ * a ∧ p 1 = δ * b

/-- **Grid polygonal worm** (`def:gridPolygonalWorm`).
For a step `δ > 0` and a vertex count `k : ℕ`, a `(k, δ)`-grid polygonal worm is
a pinned worm obtained from grid nodes `p₀, …, p_k ∈ δℤ × δℤ` with `p₀ = 0`,
`f̃(n/k) = pₙ`, interpolated linearly on each `[n/k, (n+1)/k]`, and required to be
`1`-Lipschitz. We represent it by the range of such an interpolating function. -/
def GridPolygonalWorms (k : ℕ) (δ : ℝ) : Set (Set ℝ²) :=
  {s | ∃ (f : (Set.Icc (0 : ℝ) 1) → ℝ²) (p : ℕ → ℝ²),
      LipschitzWith 1 f ∧
      f ⟨0, Set.left_mem_Icc.2 zero_le_one⟩ = 0 ∧
      p 0 = 0 ∧
      (∀ n, IsGridPoint δ (p n)) ∧
      (∀ (x : (Set.Icc (0 : ℝ) 1)) (n : ℕ) (t : ℝ), n < k → t ∈ Set.Icc (0 : ℝ) 1 →
          (x : ℝ) = (↑n + t) / ↑k → f x = (1 - t) • p n + t • p (n + 1)) ∧
      Set.range f = s}

/-! ## A finite `ε`-net of polygonal worms -/

/-- The set `S_ε` of `(k, δ)`-grid polygonal worms whose nodes lie within
distance `1` of the origin. This is the candidate finite `ε`-net of
`thm:finiteEpsilonNet`. -/
def GridNetWorms (k : ℕ) (δ : ℝ) : Set (Set ℝ²) :=
  {s | ∃ (f : (Set.Icc (0 : ℝ) 1) → ℝ²) (p : ℕ → ℝ²),
      LipschitzWith 1 f ∧
      f ⟨0, Set.left_mem_Icc.2 zero_le_one⟩ = 0 ∧
      p 0 = 0 ∧
      (∀ n, IsGridPoint δ (p n)) ∧
      (∀ n ≤ k, dist (p n) 0 ≤ 1) ∧
      (∀ (x : (Set.Icc (0 : ℝ) 1)) (n : ℕ) (t : ℝ), n < k → t ∈ Set.Icc (0 : ℝ) 1 →
          (x : ℝ) = (↑n + t) / ↑k → f x = (1 - t) • p n + t • p (n + 1)) ∧
      Set.range f = s}

/-- Each coordinate of a point of `ℝ²` is bounded in absolute value by its
distance to the origin. -/
private lemma euclid_coord_abs_le (q : ℝ²) (i : Fin 2) : |q i| ≤ dist q 0 := by
  rw [EuclideanSpace.dist_eq]
  have hle : dist (q.ofLp i) ((0 : ℝ²).ofLp i) ^ 2
      ≤ ∑ j, dist (q.ofLp j) ((0 : ℝ²).ofLp j) ^ 2 :=
    Finset.single_le_sum (f := fun j => dist (q.ofLp j) ((0 : ℝ²).ofLp j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h1 : |q i| = dist (q.ofLp i) ((0 : ℝ²).ofLp i) := by
    simp
  rw [h1, show dist (q.ofLp i) ((0 : ℝ²).ofLp i)
      = Real.sqrt (dist (q.ofLp i) ((0 : ℝ²).ofLp i) ^ 2) from
        (Real.sqrt_sq dist_nonneg).symm]
  exact Real.sqrt_le_sqrt hle

/-- The grid points of `δℤ × δℤ` within distance `1` of the origin form a finite
set. -/
private lemma gridPoints_disc_finite (δ : ℝ) (hδ : 0 < δ) :
    {q : ℝ² | IsGridPoint δ q ∧ dist q 0 ≤ 1}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / δ)
  apply Set.Finite.subset
    (Set.Finite.image
      (fun ab : ℤ × ℤ => (WithLp.toLp 2 ![δ * (ab.1 : ℝ), δ * (ab.2 : ℝ)] : ℝ²))
      ((Set.finite_Icc (-(N : ℤ)) (N : ℤ)).prod (Set.finite_Icc (-(N : ℤ)) (N : ℤ))))
  rintro q ⟨⟨a, b, ha, hb⟩, hdist⟩
  have hbound : ∀ (c : ℤ) (i : Fin 2), q i = δ * (c : ℝ) → |c| ≤ (N : ℤ) := by
    intro c i hc
    have h1 : |q i| ≤ 1 := le_trans (euclid_coord_abs_le q i) hdist
    rw [hc, abs_mul, abs_of_pos hδ] at h1
    have hcle : |(c : ℝ)| ≤ (N : ℝ) := by
      have : |(c : ℝ)| ≤ 1 / δ := by rw [le_div_iff₀ hδ, mul_comm]; exact h1
      exact le_trans this hN
    exact_mod_cast hcle
  have hbound0 := hbound a 0 ha
  have hbound1 := hbound b 1 hb
  refine ⟨(a, b), ⟨?_, ?_⟩, ?_⟩
  · exact ⟨(abs_le.mp hbound0).1, (abs_le.mp hbound0).2⟩
  · exact ⟨(abs_le.mp hbound1).1, (abs_le.mp hbound1).2⟩
  · ext i
    fin_cases i <;> simp [ha, hb]

/-- The range of a `(k, δ)`-grid polygonal worm (`k ≥ 1`) is the union of the
segments joining consecutive nodes, hence determined by the nodes `p 0, …, p k`. -/
private lemma worm_range_eq_iUnion {k : ℕ} (hk0 : 0 < k) (p : ℕ → ℝ²)
    (f : (Set.Icc (0 : ℝ) 1) → ℝ²)
    (hinterp : ∀ (x : (Set.Icc (0 : ℝ) 1)) (n : ℕ) (t : ℝ), n < k →
        t ∈ Set.Icc (0 : ℝ) 1 → (x : ℝ) = (↑n + t) / ↑k →
        f x = (1 - t) • p n + t • p (n + 1)) :
    Set.range f = ⋃ n : Fin k, segment ℝ (p (n : ℕ)) (p ((n : ℕ) + 1)) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  ext y
  simp only [Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨hx0, hx1⟩ := x.2
    rcases eq_or_lt_of_le hx1 with h1 | hlt
    · refine ⟨⟨k - 1, by omega⟩, ?_⟩
      have hn : k - 1 < k := by omega
      have heq : (x : ℝ) = (↑(k - 1) + (1 : ℝ)) / ↑k := by
        rw [h1, Nat.cast_sub hk0]; push_cast; field_simp; ring
      rw [hinterp x (k - 1) 1 hn ⟨zero_le_one, le_refl 1⟩ heq, segment_eq_image]
      exact ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩
    · have hxk0 : (0 : ℝ) ≤ (x : ℝ) * k := mul_nonneg hx0 (le_of_lt hkR)
      set m : ℕ := ⌊(x : ℝ) * k⌋₊ with hm
      have hmk : m < k := by
        rw [hm, Nat.floor_lt hxk0]
        calc (x : ℝ) * k < 1 * k := by exact mul_lt_mul_of_pos_right hlt hkR
          _ = k := one_mul _
      refine ⟨⟨m, hmk⟩, ?_⟩
      set t : ℝ := (x : ℝ) * k - m with ht
      have ht0 : 0 ≤ t := by rw [ht]; linarith [Nat.floor_le hxk0]
      have ht1 : t ≤ 1 := by rw [ht]; linarith [Nat.lt_floor_add_one ((x : ℝ) * k)]
      have htmem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
      have heq : (x : ℝ) = (↑m + t) / ↑k := by rw [ht]; field_simp; ring
      rw [hinterp x m t hmk htmem heq, segment_eq_image]
      exact ⟨t, htmem, rfl⟩
  · rintro ⟨i, hi⟩
    rw [segment_eq_image] at hi
    obtain ⟨t, htmem, hty⟩ := hi
    have hik : (i : ℕ) < k := i.2
    have hxmem : (↑(i : ℕ) + t) / ↑k ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg (add_nonneg (Nat.cast_nonneg _) htmem.1) (le_of_lt hkR), ?_⟩
      · rw [div_le_one hkR]
        have hi1 : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik
        linarith [htmem.2]
    refine ⟨⟨(↑(i : ℕ) + t) / ↑k, hxmem⟩, ?_⟩
    rw [hinterp ⟨(↑(i : ℕ) + t) / ↑k, hxmem⟩ (i : ℕ) t hik htmem rfl]
    exact hty

/-- The set of grid polygonal worms with nodes within distance `1` of the origin
is finite: each of the `k + 1` relevant nodes ranges over the finitely many grid
points of `δℤ × δℤ` inside the unit disc, and the worm's range is determined by
its nodes. -/
private lemma gridNetWorms_finite (k : ℕ) (hk0 : 0 < k) (δ : ℝ) (hδ : 0 < δ) :
    (GridNetWorms k δ).Finite := by
  set G : Set ℝ² := {q : ℝ² | IsGridPoint δ q ∧ dist q 0 ≤ 1} with hGdef
  have hG : G.Finite := gridPoints_disc_finite δ hδ
  refine Set.Finite.subset (s := (fun v : Fin (k + 1) → ℝ² =>
      ⋃ n : Fin k, segment ℝ (v n.castSucc) (v n.succ)) ''
        (Set.univ.pi (fun _ : Fin (k + 1) => G)))
    ((Set.Finite.pi (fun _ => hG)).image _) ?_
  rintro s ⟨f, p, _hlip, _hf0, _hp0, hgrid, hdist, hinterp, rfl⟩
  refine ⟨fun i : Fin (k + 1) => p (i : ℕ), ?_, ?_⟩
  · intro i _
    exact ⟨hgrid (i : ℕ), hdist (i : ℕ) (Nat.lt_succ_iff.mp i.2)⟩
  · rw [worm_range_eq_iUnion hk0 p f hinterp]
    refine Set.iUnion_congr (fun n => ?_)
    simp only [Fin.val_castSucc, Fin.val_succ]

/-- The clamp functions `t ↦ max 0 (min 1 (s - j))` for `j = 0, …, k-1` sum to
`min s k` (for `s ≥ 0`): only one summand is partial at a time. -/
private lemma sum_clamp_eq_min (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ∑ j ∈ Finset.range k, max 0 (min 1 (s - (j : ℝ))) = min s (k : ℝ) := by
  induction k with
  | zero => simp [min_eq_right hs]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    simp only [min_def, max_def]
    split_ifs <;> linarith

/-- Round a point of `ℝ²` to the nearest grid point of `δℤ × δℤ`. -/
private noncomputable def gridRound (δ : ℝ) (z : ℝ²) : ℝ² :=
  WithLp.toLp 2 ![δ * (round (z 0 / δ) : ℝ), δ * (round (z 1 / δ) : ℝ)]

private lemma gridRound_apply_zero (δ : ℝ) (z : ℝ²) :
    (gridRound δ z) 0 = δ * (round (z 0 / δ) : ℝ) := by simp [gridRound]

private lemma gridRound_apply_one (δ : ℝ) (z : ℝ²) :
    (gridRound δ z) 1 = δ * (round (z 1 / δ) : ℝ) := by simp [gridRound]

private lemma gridRound_isGrid (δ : ℝ) (z : ℝ²) : IsGridPoint δ (gridRound δ z) :=
  ⟨round (z 0 / δ), round (z 1 / δ), gridRound_apply_zero δ z, gridRound_apply_one δ z⟩

private lemma gridRound_zero (δ : ℝ) : gridRound δ (0 : ℝ²) = 0 := by
  ext i; fin_cases i <;> simp [gridRound]

private lemma gridRound_dist_le (δ : ℝ) (hδ : 0 < δ) (z : ℝ²) :
    dist (gridRound δ z) z ≤ δ := by
  have hcoord : ∀ w : ℝ, (δ * (round (w / δ) : ℝ) - w) ^ 2 ≤ (δ / 2) ^ 2 := by
    intro w
    have h1 : |δ * (round (w / δ) : ℝ) - w| ≤ δ / 2 := by
      have heq : δ * (round (w / δ) : ℝ) - w = δ * ((round (w / δ) : ℝ) - w / δ) := by
        field_simp
      rw [heq, abs_mul, abs_of_pos hδ]
      have hr := abs_sub_round (w / δ)
      rw [abs_sub_comm] at hr
      nlinarith [hr, hδ]
    nlinarith [sq_abs (δ * (round (w / δ) : ℝ) - w), h1,
      abs_nonneg (δ * (round (w / δ) : ℝ) - w)]
  rw [EuclideanSpace.dist_eq]
  have hsum : (∑ i, dist ((gridRound δ z).ofLp i) (z.ofLp i) ^ 2) ≤ δ ^ 2 := by
    rw [Fin.sum_univ_two]
    have e0 : (gridRound δ z).ofLp 0 = δ * (round (z 0 / δ) : ℝ) := gridRound_apply_zero δ z
    have e1 : (gridRound δ z).ofLp 1 = δ * (round (z 1 / δ) : ℝ) := gridRound_apply_one δ z
    rw [e0, e1, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs,
      show z.ofLp 0 = z 0 from rfl, show z.ofLp 1 = z 1 from rfl]
    nlinarith [hcoord (z 0), hcoord (z 1)]
  calc Real.sqrt (∑ i, dist ((gridRound δ z).ofLp i) (z.ofLp i) ^ 2)
      ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = δ := Real.sqrt_sq hδ.le

/-- Every parameter `x ∈ [0,1]` decomposes as `(n + t)/k` with `n < k`,
`t ∈ [0,1]`. -/
private lemma exists_grid_decomp {k : ℕ} (hk0 : 0 < k) (x : Set.Icc (0 : ℝ) 1) :
    ∃ (n : ℕ) (t : ℝ), n < k ∧ t ∈ Set.Icc (0 : ℝ) 1 ∧ (x : ℝ) = (↑n + t) / ↑k := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  obtain ⟨hx0, hx1⟩ := x.2
  rcases eq_or_lt_of_le hx1 with h1 | hlt
  · refine ⟨k - 1, 1, by omega, ⟨zero_le_one, le_refl 1⟩, ?_⟩
    rw [h1, Nat.cast_sub hk0]; push_cast; field_simp; ring
  · have hxk0 : (0 : ℝ) ≤ (x : ℝ) * k := mul_nonneg hx0 (le_of_lt hkR)
    refine ⟨⌊(x : ℝ) * k⌋₊, (x : ℝ) * k - ⌊(x : ℝ) * k⌋₊, ?_, ⟨?_, ?_⟩, ?_⟩
    · rw [Nat.floor_lt hxk0]; nlinarith [hlt, hkR]
    · linarith [Nat.floor_le hxk0]
    · linarith [Nat.lt_floor_add_one ((x : ℝ) * k)]
    · field_simp; ring

/-- The piecewise-linear interpolant through grid nodes `p 0, …, p k`, written
as a sum of clamped ramps so that it is manifestly `1`-Lipschitz. -/
private noncomputable def interp (k : ℕ) (p : ℕ → ℝ²) (x : Set.Icc (0 : ℝ) 1) : ℝ² :=
  p 0 + ∑ j ∈ Finset.range k, max 0 (min 1 ((x : ℝ) * k - (j : ℝ))) • (p (j + 1) - p j)

/-- The interpolant satisfies the grid-worm interpolation identity. -/
private lemma interp_eq {k : ℕ} (hk0 : 0 < k) (p : ℕ → ℝ²) (x : Set.Icc (0 : ℝ) 1)
    (n : ℕ) (t : ℝ) (hn : n < k) (htmem : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : (x : ℝ) = (↑n + t) / ↑k) :
    interp k p x = (1 - t) • p n + t • p (n + 1) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hxk : (x : ℝ) * k = ↑n + t := by rw [hx]; field_simp
  obtain ⟨ht0, ht1⟩ := htmem
  rw [interp]
  have hterm : ∀ j ∈ Finset.range k,
      max 0 (min 1 ((x : ℝ) * k - (j : ℝ))) • (p (j + 1) - p j)
        = (if j < n then (p (j + 1) - p j) else 0)
          + (if j = n then t • (p (j + 1) - p j) else 0) := by
    intro j _
    rw [hxk]
    rcases lt_trichotomy j n with h | h | h
    · rw [if_pos h, if_neg (by omega), add_zero]
      have hc : max 0 (min 1 (↑n + t - (j : ℝ))) = 1 := by
        have hj1 : (j : ℝ) + 1 ≤ n := by exact_mod_cast h
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      rw [hc, one_smul]
    · subst h
      rw [if_neg (lt_irrefl _), if_pos rfl, zero_add]
      have hc : max 0 (min 1 ((j : ℝ) + t - (j : ℝ))) = t := by
        rw [show (j : ℝ) + t - (j : ℝ) = t by ring, min_eq_right ht1, max_eq_right ht0]
      rw [hc]
    · rw [if_neg (by omega), if_neg (by omega), add_zero]
      have hc : max 0 (min 1 (↑n + t - (j : ℝ))) = 0 := by
        have hj1 : (n : ℝ) + 1 ≤ j := by exact_mod_cast h
        rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      rw [hc, zero_smul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hfilter : Finset.filter (· < n) (Finset.range k) = Finset.range n := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  have hA : (∑ j ∈ Finset.range k, (if j < n then (p (j + 1) - p j) else 0)) = p n - p 0 := by
    rw [← Finset.sum_filter, hfilter, Finset.sum_range_sub p n]
  have hB : (∑ j ∈ Finset.range k, (if j = n then t • (p (j + 1) - p j) else 0))
      = t • (p (n + 1) - p n) := by
    rw [Finset.sum_ite_eq' (Finset.range k) n (fun j => t • (p (j + 1) - p j))]
    simp [Finset.mem_range.mpr hn]
  rw [hA, hB]
  module

/-- If consecutive nodes are within `1/k`, the interpolant is `1`-Lipschitz. -/
private lemma interp_lipschitz {k : ℕ} (hk0 : 0 < k) (p : ℕ → ℝ²)
    (hgap : ∀ j < k, ‖p (j + 1) - p j‖ ≤ 1 / (k : ℝ)) :
    LipschitzWith 1 (interp k p) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have key : ∀ a b : Set.Icc (0 : ℝ) 1, (a : ℝ) ≤ (b : ℝ) →
      ‖interp k p a - interp k p b‖ ≤ (b : ℝ) - (a : ℝ) := by
    intro a b hab
    have hdiff : interp k p a - interp k p b
        = ∑ j ∈ Finset.range k,
            (max 0 (min 1 ((a : ℝ) * k - (j : ℝ))) - max 0 (min 1 ((b : ℝ) * k - (j : ℝ))))
              • (p (j + 1) - p j) := by
      rw [interp, interp, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [← sub_smul])
    have hsumdiff : ∑ j ∈ Finset.range k,
        |max 0 (min 1 ((a : ℝ) * k - (j : ℝ))) - max 0 (min 1 ((b : ℝ) * k - (j : ℝ)))|
          ≤ (k : ℝ) * ((b : ℝ) - (a : ℝ)) := by
      have hmono : ∀ j ∈ Finset.range k,
          |max 0 (min 1 ((a : ℝ) * k - (j : ℝ))) - max 0 (min 1 ((b : ℝ) * k - (j : ℝ)))|
            = max 0 (min 1 ((b : ℝ) * k - (j : ℝ))) - max 0 (min 1 ((a : ℝ) * k - (j : ℝ))) := by
        intro j _
        rw [abs_of_nonpos]
        · ring
        · have huv : (a : ℝ) * k - (j : ℝ) ≤ (b : ℝ) * k - (j : ℝ) := by
            have := mul_le_mul_of_nonneg_right hab hkR.le; linarith
          have := max_le_max (le_refl (0 : ℝ)) (min_le_min (le_refl (1 : ℝ)) huv)
          linarith
      rw [Finset.sum_congr rfl hmono, Finset.sum_sub_distrib,
        sum_clamp_eq_min k ((b : ℝ) * k) (mul_nonneg b.2.1 hkR.le),
        sum_clamp_eq_min k ((a : ℝ) * k) (mul_nonneg a.2.1 hkR.le)]
      have hP : (a : ℝ) * k ≤ (b : ℝ) * k := mul_le_mul_of_nonneg_right hab hkR.le
      rcases le_total ((a : ℝ) * k) (k : ℝ) with hak1 | hak1
      · rw [min_eq_left hak1]
        nlinarith [min_le_left ((b : ℝ) * k) (k : ℝ)]
      · have hbk1 : (k : ℝ) ≤ (b : ℝ) * k := le_trans hak1 hP
        rw [min_eq_right hak1, min_eq_right hbk1]
        nlinarith [hab, hkR]
    rw [hdiff]
    calc ‖∑ j ∈ Finset.range k,
            (max 0 (min 1 ((a : ℝ) * k - (j : ℝ))) - max 0 (min 1 ((b : ℝ) * k - (j : ℝ))))
              • (p (j + 1) - p j)‖
        ≤ ∑ j ∈ Finset.range k,
            ‖(max 0 (min 1 ((a : ℝ) * k - (j : ℝ))) - max 0 (min 1 ((b : ℝ) * k - (j : ℝ))))
              • (p (j + 1) - p j)‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.range k,
            |max 0 (min 1 ((a : ℝ) * k - (j : ℝ))) - max 0 (min 1 ((b : ℝ) * k - (j : ℝ)))|
              * ‖p (j + 1) - p j‖ :=
            Finset.sum_congr rfl (fun j _ => by rw [norm_smul, Real.norm_eq_abs])
      _ ≤ ∑ j ∈ Finset.range k,
            |max 0 (min 1 ((a : ℝ) * k - (j : ℝ))) - max 0 (min 1 ((b : ℝ) * k - (j : ℝ)))|
              * (1 / (k : ℝ)) :=
            Finset.sum_le_sum (fun j hj =>
              mul_le_mul_of_nonneg_left (hgap j (Finset.mem_range.mp hj)) (abs_nonneg _))
      _ = (1 / (k : ℝ)) * ∑ j ∈ Finset.range k,
            |max 0 (min 1 ((a : ℝ) * k - (j : ℝ))) - max 0 (min 1 ((b : ℝ) * k - (j : ℝ)))| := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ (1 / (k : ℝ)) * ((k : ℝ) * ((b : ℝ) - (a : ℝ))) :=
            mul_le_mul_of_nonneg_left hsumdiff (by positivity)
      _ = (b : ℝ) - (a : ℝ) := by rw [one_div]; exact inv_mul_cancel_left₀ (ne_of_gt hkR) _
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [dist_eq_norm, NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq]
  rcases le_total (x : ℝ) (y : ℝ) with h | h
  · rw [abs_of_nonpos (by linarith), neg_sub]; exact key x y h
  · rw [abs_of_nonneg (by linarith), norm_sub_rev]; exact key y x h

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

end Moser.CompactnessOutline
