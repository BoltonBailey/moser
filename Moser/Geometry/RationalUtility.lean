import Mathlib

/-!
# Rational Utility

Helper functions and lemmas for constructing rational numbers with prescribed square bounds.
-/

/--
Helper function to find a positive rational number whose square is between two given rationals.
Assumes `0 ≤ lower` and `lower < upper`.

Construction: Let `N = ⌈(upper+1)/(upper-lower)⌉ + 1` and `m = Nat.sqrt ⌊N²·lower⌋ + 1`.
Return `m / N`. The choice of `N` ensures `N·(√upper − √lower) ≥ 1`, which bounds `m` above by
`N·√upper`, so `(m/N)² ≤ upper`. The floor construction ensures `(m/N)² > lower`.
-/
@[nolint unusedArguments]
def findRationalWithSquareBetween (lower upper : ℚ) (_h0 : 0 ≤ lower) (_hlt : lower < upper) : ℚ :=
  let d := upper - lower
  let N : ℕ := (⌈(upper + 1) / d⌉).toNat + 1
  let lF : ℕ := (⌊lower * (N : ℚ) ^ 2⌋).toNat
  (Nat.sqrt lF + 1 : ℚ) / N

lemma findRationalWithSquareBetween_positive (lower upper : ℚ)
    (h0 : 0 ≤ lower) (hlt : lower < upper) :
    0 < findRationalWithSquareBetween lower upper h0 hlt := by
  unfold findRationalWithSquareBetween
  apply div_pos
  · positivity
  · exact_mod_cast Nat.succ_pos _

/-- Key bound: `N ≥ (upper+1)/(upper-lower)` as rationals -/
private lemma findRat_N_bound (lower upper : ℚ) (h0 : 0 ≤ lower) (hlt : lower < upper) :
    (upper + 1) / (upper - lower) ≤
    ((⌈(upper + 1) / (upper - lower)⌉).toNat + 1 : ℕ) := by
  have hd : (0 : ℚ) < upper - lower := by linarith
  have hceil_pos : (0 : ℤ) < ⌈(upper + 1) / (upper - lower)⌉ :=
    Int.ceil_pos.mpr (div_pos (by linarith) hd)  -- upper > lower ≥ 0, so upper + 1 > 0
  have hceil_nn : (0 : ℤ) ≤ ⌈(upper + 1) / (upper - lower)⌉ := le_of_lt hceil_pos
  have hcast : ((⌈(upper + 1) / (upper - lower)⌉.toNat : ℕ) : ℤ) =
               ⌈(upper + 1) / (upper - lower)⌉ := Int.toNat_of_nonneg hceil_nn
  calc (upper + 1) / (upper - lower)
      ≤ (⌈(upper + 1) / (upper - lower)⌉ : ℚ) := Int.le_ceil _
    _ = ((⌈(upper + 1) / (upper - lower)⌉.toNat : ℕ) : ℚ) := by exact_mod_cast hcast.symm
    _ ≤ ((⌈(upper + 1) / (upper - lower)⌉.toNat + 1 : ℕ) : ℚ) := by
        exact_mod_cast Nat.le_succ _

/-- `√x ≤ (x+1)/2` for `x ≥ 0` (AM-GM with 1) -/
private lemma sqrt_le_half_add_one (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ≤ (x + 1) / 2 := by
  nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1)]

/-- `√upper + √lower ≤ upper + 1` -/
private lemma sqrt_sum_le (lower upper : ℚ) (h0 : 0 ≤ lower) (hlt : lower < upper) :
    Real.sqrt (upper : ℝ) + Real.sqrt (lower : ℝ) ≤ (upper : ℝ) + 1 := by
  have h0' : (0 : ℝ) ≤ lower := by exact_mod_cast h0
  have hlt' : (lower : ℝ) < upper := by exact_mod_cast hlt
  have h_upper_nn : (0 : ℝ) ≤ upper := le_of_lt (lt_of_le_of_lt h0' hlt')
  have := sqrt_le_half_add_one upper h_upper_nn
  have := sqrt_le_half_add_one lower h0'
  linarith [show (lower : ℝ) ≤ upper from le_of_lt hlt']

lemma findRationalWithSquareBetween_spec (lower upper : ℚ)
    (h0 : 0 ≤ lower) (hlt : lower < upper) :
    let r := findRationalWithSquareBetween lower upper h0 hlt
    lower ≤ r * r ∧ r * r ≤ upper := by
  simp only [findRationalWithSquareBetween]
  set d := upper - lower with hd_def
  set N : ℕ := (⌈(upper + 1) / d⌉).toNat + 1
  set lF : ℕ := (⌊lower * (N : ℚ) ^ 2⌋).toNat
  set m : ℕ := Nat.sqrt lF + 1
  -- Abbreviations in ℝ
  set sqL := Real.sqrt (lower : ℝ)
  set sqU := Real.sqrt (upper : ℝ)
  have hd : (0 : ℚ) < d := by simp [hd_def]; linarith
  have h0' : (0 : ℝ) ≤ (lower : ℝ) := by exact_mod_cast h0
  have hlt' : (lower : ℝ) < (upper : ℝ) := by exact_mod_cast hlt
  have h_upper_nn : (0 : ℝ) ≤ (upper : ℝ) := le_of_lt (lt_of_le_of_lt h0' hlt')
  have hN_pos : (0 : ℚ) < N := by exact_mod_cast Nat.succ_pos _
  -- lF = ⌊lower * N²⌋ with key floor facts
  have hlF_nn : (0 : ℤ) ≤ ⌊lower * (N : ℚ) ^ 2⌋ :=
    Int.floor_nonneg.mpr (by positivity)
  have hlF_cast : ((lF : ℕ) : ℤ) = ⌊lower * (N : ℚ) ^ 2⌋ :=
    Int.toNat_of_nonneg hlF_nn
  have hlF_le : (lF : ℚ) ≤ lower * (N : ℚ) ^ 2 := by
    have h1 : (⌊lower * (N : ℚ) ^ 2⌋ : ℚ) ≤ lower * (N : ℚ) ^ 2 := Int.floor_le _
    have h2 : ((lF : ℕ) : ℚ) = ((⌊lower * (N : ℚ) ^ 2⌋ : ℤ) : ℚ) := by exact_mod_cast hlF_cast
    linarith [h2 ▸ h1]
  have hlF_lt : lower * (N : ℚ) ^ 2 < (lF : ℚ) + 1 := by
    have h1 : lower * (N : ℚ) ^ 2 < (⌊lower * (N : ℚ) ^ 2⌋ : ℚ) + 1 := Int.lt_floor_add_one _
    have h2 : ((lF : ℕ) : ℚ) = ((⌊lower * (N : ℚ) ^ 2⌋ : ℤ) : ℚ) := by exact_mod_cast hlF_cast
    linarith [h2 ▸ h1]
  -- Nat.sqrt key facts: lF < m*m and Nat.sqrt(lF)*Nat.sqrt(lF) ≤ lF
  have hm_sq_gt : lF < m * m := Nat.sqrt_lt.mp (Nat.lt_succ_self _)
  have hsqrt_sq : Nat.sqrt lF * Nat.sqrt lF ≤ lF := by
    rw [← not_lt, ← Nat.sqrt_lt]; exact lt_irrefl _
  -- Cast m = Nat.sqrt lF + 1 to ℚ and ℝ
  have hm_eq : (m : ℚ) = (Nat.sqrt lF : ℚ) + 1 := by norm_cast
  have hm_eq_R : (m : ℝ) = (Nat.sqrt lF : ℝ) + 1 := by norm_cast
  -- Lower bound: lower ≤ (m/N)²
  refine ⟨?_, ?_⟩
  · -- lower ≤ (m/N)*(m/N)
    rw [div_mul_div_comm]
    have h2 : (lF : ℚ) + 1 ≤ (m : ℚ) * m := by exact_mod_cast Nat.succ_le_of_lt hm_sq_gt
    have h_key : lower * ((N : ℚ) * N) ≤ (m : ℚ) * m := by nlinarith [hlF_lt]
    have hNN : (0 : ℚ) < (N : ℚ) * N := by positivity
    rw [← hm_eq, le_div_iff₀ hNN]
    linarith
  · -- Upper bound: (m/N)*(m/N) ≤ upper
    rw [div_mul_div_comm]
    have hNN : (0 : ℚ) < (N : ℚ) * N := by positivity
    -- Suffices to show m * m ≤ upper * (N * N)
    suffices h : (m : ℚ) * m ≤ upper * ((N : ℚ) * N) by
      rw [← hm_eq, div_le_iff₀ hNN]; linarith
    -- Prove m * m ≤ upper * N * N via Real.sqrt
    -- Step 1: (Nat.sqrt lF : ℝ) ≤ N * √lower
    have hsqrtlF_le : (Nat.sqrt lF : ℝ) ≤ (N : ℝ) * Real.sqrt lower := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ Nat.sqrt lF),
          ← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (N : ℝ) * Real.sqrt lower)]
      apply Real.sqrt_le_sqrt
      have h1 : (Nat.sqrt lF : ℝ) * Nat.sqrt lF ≤ (lF : ℝ) := by exact_mod_cast hsqrt_sq
      have h2 : (lF : ℝ) ≤ (lower : ℝ) * (N : ℝ) ^ 2 := by exact_mod_cast hlF_le
      nlinarith [Real.sq_sqrt h0', Real.sqrt_nonneg (lower : ℝ)]
    -- Step 2: 1 ≤ N * (√upper - √lower)
    have hgap : 1 ≤ (N : ℝ) * (Real.sqrt upper - Real.sqrt lower) := by
      have hsum_pos : 0 < Real.sqrt upper + Real.sqrt lower := by
        have := Real.sqrt_pos.mpr (lt_of_le_of_lt h0' hlt')
        linarith [Real.sqrt_nonneg (lower : ℝ)]
      have hsum_le : Real.sqrt upper + Real.sqrt lower ≤ (upper : ℝ) + 1 :=
        sqrt_sum_le lower upper h0 hlt
      have hfactor : (Real.sqrt upper - Real.sqrt lower) * (Real.sqrt upper + Real.sqrt lower) =
                     (upper : ℝ) - lower := by
        linear_combination Real.mul_self_sqrt h_upper_nn - Real.mul_self_sqrt h0'
      have hN_bound : ((upper : ℝ) + 1) / ((upper : ℝ) - lower) ≤ (N : ℝ) :=
        by exact_mod_cast findRat_N_bound lower upper h0 hlt
      have hUL_R : (0 : ℝ) < (upper : ℝ) - lower := by exact_mod_cast hd
      have hN_UL : (upper : ℝ) + 1 ≤ (N : ℝ) * ((upper : ℝ) - lower) :=
        (div_le_iff₀ hUL_R).mp hN_bound
      -- N*(√U-√L)*(√U+√L) = N*(U-L) ≥ U+1 ≥ √U+√L, so N*(√U-√L) ≥ 1
      have hprod : Real.sqrt upper + Real.sqrt lower ≤
          (N : ℝ) * (Real.sqrt upper - Real.sqrt lower) * (Real.sqrt upper + Real.sqrt lower) :=
        calc Real.sqrt upper + Real.sqrt lower
            ≤ (upper : ℝ) + 1 := hsum_le
          _ ≤ (N : ℝ) * ((upper : ℝ) - lower) := hN_UL
          _ = (N : ℝ) * ((Real.sqrt upper - Real.sqrt lower)
                * (Real.sqrt upper + Real.sqrt lower)) := by
              rw [hfactor]
          _ = (N : ℝ) * (Real.sqrt upper - Real.sqrt lower)
                * (Real.sqrt upper + Real.sqrt lower) := by
              ring
      apply le_of_mul_le_mul_right _ hsum_pos
      linarith
    -- Step 3: m ≤ N * √upper
    have hm_le : (m : ℝ) ≤ (N : ℝ) * Real.sqrt upper := by
      rw [hm_eq_R]; linarith [hsqrtlF_le, hgap]
    -- Conclude: m * m ≤ upper * N * N
    have hkey : ((m : ℚ) * m : ℝ) ≤ ((upper * ((N : ℚ) * N) : ℚ) : ℝ) := by
      push_cast
      have := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ (m : ℝ)) hm_le
      nlinarith [Real.mul_self_sqrt h_upper_nn]
    exact_mod_cast hkey
