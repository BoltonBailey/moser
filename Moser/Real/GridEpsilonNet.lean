import Mathlib

/-!
# Grid machinery for the Moser worm finite `ε`-net

This file collects the grid-specific definitions and helper lemmas used to build
the finite grid `ε`-net of `thm:finiteEpsilonNet`: grid points, `(k, δ)`-grid
polygonal worms, the candidate net `GridNetWorms`, its finiteness, the rounding
map `gridRound`, and the piecewise-linear interpolant `interp` together with its
interpolation identity and `1`-Lipschitz bound.

These declarations do not depend on the worm base definitions, so this file
imports only Mathlib. The `ε`-net theorem `finiteEpsilonNet` (which couples this
machinery to `PinnedWorms` / `IsEpsilonNet`) lives in
`Moser.Real.CompactnessOutline`, which imports this file.
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

/-! ## Finiteness of the candidate net -/

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
lemma gridNetWorms_finite (k : ℕ) (hk0 : 0 < k) (δ : ℝ) (hδ : 0 < δ) :
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

/-! ## Rounding and the piecewise-linear interpolant -/

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
noncomputable def gridRound (δ : ℝ) (z : ℝ²) : ℝ² :=
  WithLp.toLp 2 ![δ * (round (z 0 / δ) : ℝ), δ * (round (z 1 / δ) : ℝ)]

private lemma gridRound_apply_zero (δ : ℝ) (z : ℝ²) :
    (gridRound δ z) 0 = δ * (round (z 0 / δ) : ℝ) := by simp [gridRound]

private lemma gridRound_apply_one (δ : ℝ) (z : ℝ²) :
    (gridRound δ z) 1 = δ * (round (z 1 / δ) : ℝ) := by simp [gridRound]

lemma gridRound_isGrid (δ : ℝ) (z : ℝ²) : IsGridPoint δ (gridRound δ z) :=
  ⟨round (z 0 / δ), round (z 1 / δ), gridRound_apply_zero δ z, gridRound_apply_one δ z⟩

lemma gridRound_zero (δ : ℝ) : gridRound δ (0 : ℝ²) = 0 := by
  ext i; fin_cases i <;> simp [gridRound]

lemma gridRound_dist_le (δ : ℝ) (hδ : 0 < δ) (z : ℝ²) :
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
lemma exists_grid_decomp {k : ℕ} (hk0 : 0 < k) (x : Set.Icc (0 : ℝ) 1) :
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
noncomputable def interp (k : ℕ) (p : ℕ → ℝ²) (x : Set.Icc (0 : ℝ) 1) : ℝ² :=
  p 0 + ∑ j ∈ Finset.range k, max 0 (min 1 ((x : ℝ) * k - (j : ℝ))) • (p (j + 1) - p j)

/-- The interpolant satisfies the grid-worm interpolation identity. -/
lemma interp_eq {k : ℕ} (hk0 : 0 < k) (p : ℕ → ℝ²) (x : Set.Icc (0 : ℝ) 1)
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
lemma interp_lipschitz {k : ℕ} (hk0 : 0 < k) (p : ℕ → ℝ²)
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

end Moser.CompactnessOutline
