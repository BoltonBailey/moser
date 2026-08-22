module

public import Mathlib
public import Moser.Real.CompactnessOutline

@[expose] public section

/-!
# Quantitative approximation of the Moser cover number

This file supplies the quantitative ingredients of the approximation algorithm
sketched in the project notes: an explicit a priori upper bound on the Moser
cover number, an explicit ball contained in every worm cover, and the resulting
dilation bound controlling the gap between the lower and the upper bound.
-/

open MeasureTheory
open scoped ENNReal

namespace Moser.CompactnessOutline

/-- The real Euclidean plane `ℝ²`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Every worm fits in a disc of radius `1/2` -/

/-- Every worm is contained in the closed ball of radius `1/2` around the image
of its midpoint: a `1`-Lipschitz curve on `[0,1]` never travels further than
`1/2` from `f(1/2)`. -/
lemma exists_closedBall_superset_of_mem_worms {s : Set ℝ²} (hs : s ∈ Worms) :
    ∃ c : ℝ², s ⊆ Metric.closedBall c (1 / 2) := by
  obtain ⟨f, hlip, rfl⟩ := hs
  set m : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩ with hm
  refine ⟨f m, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [Metric.mem_closedBall]
  refine le_trans (by simpa using hlip.dist_le_mul x m) ?_
  have hmval : (m : ℝ) = 1 / 2 := rfl
  rw [Subtype.dist_eq, Real.dist_eq, hmval, abs_le]
  obtain ⟨h0, h1⟩ := x.2
  constructor <;> linarith

/-- Translation by `-c` is an orientation-preserving isometry. -/
lemma isOrientationPreservingIsometry_sub (c : ℝ²) :
    IsOrientationPreservingIsometry (fun x : ℝ² => x - c) :=
  ⟨LinearIsometryEquiv.refl ℝ ℝ², -c, by
    rw [show (LinearIsometryEquiv.refl ℝ ℝ²).toLinearEquiv = LinearEquiv.refl ℝ ℝ² from rfl,
      LinearEquiv.det_refl], by
    funext x; simp [sub_eq_add_neg]⟩

/-- **A priori upper bound on the Moser cover number.**
The closed disc of radius `1/2` covers every worm (translate the worm so that its
midpoint sits at the origin), hence `M ≤ π/4`. -/
theorem moserCoverNumber_le_pi_div_four :
    moserCoverNumber ≤ ENNReal.ofReal (Real.pi / 4) := by
  have h : ∀ s ∈ Worms, ∃ c : ℝ², s ⊆ Metric.closedBall c (1 / 2) :=
    fun _ hs => exists_closedBall_superset_of_mem_worms hs
  choose! c hc using h
  have hPC : IsPlacementCover Worms (Metric.closedBall (0 : ℝ²) (1 / 2)) := by
    refine ⟨fun s x => x - c s, fun s _ => isOrientationPreservingIsometry_sub (c s), ?_⟩
    refine convexHull_min (Set.iUnion₂_subset fun s hs => ?_) (convex_closedBall _ _)
    rintro _ ⟨y, hy, rfl⟩
    have hy' := hc s hs hy
    rw [Metric.mem_closedBall] at hy' ⊢
    rw [dist_zero_right, ← dist_eq_norm]
    exact hy'
  have hvol : volume (Metric.closedBall (0 : ℝ²) (1 / 2)) = ENNReal.ofReal (Real.pi / 4) := by
    rw [EuclideanSpace.volume_closedBall]
    have hcard : Fintype.card (Fin 2) = 2 := by simp
    rw [hcard, show ((2 : ℕ) : ℝ) / 2 + 1 = 2 by norm_num, Real.Gamma_two,
      Real.sq_sqrt Real.pi_nonneg, div_one, ← ENNReal.ofReal_pow (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [moserCoverNumber, minimalCoverArea, minimalVolume, ← hvol]
  exact sInf_le ⟨_, hPC, rfl⟩

/-! ## A dilation bound for thickenings of convex sets -/

/-- The closure of a convex set has no larger volume: the frontier of a convex
set is null (`Convex.addHaar_frontier`). -/
lemma volume_closure_le_of_convex {K : Set ℝ²} (hK : Convex ℝ K) :
    volume (closure K) ≤ volume K := by
  have hsub : closure K ⊆ K ∪ frontier K := by
    intro x hx
    by_cases h : x ∈ K
    · exact Or.inl h
    · exact Or.inr ⟨hx, fun hx' => h (interior_subset hx')⟩
  calc volume (closure K) ≤ volume (K ∪ frontier K) := measure_mono hsub
    _ ≤ volume K + volume (frontier K) := measure_union_le _ _
    _ = volume K := by rw [hK.addHaar_frontier volume, add_zero]

/-- **Dilation bound.** If a closed convex set `K` contains the disc of radius
`r > 0` centred at `c`, then its `ε`-thickening is contained in the image of `K`
under the homothety of centre `c` and ratio `1 + ε/r`.

Geometrically: a displacement of size at most `ε` can be absorbed by scaling `K`
about the disc it contains, since the displacement direction, scaled up to length
`r`, points at a point of that disc. -/
lemma cthickening_subset_homothety {K : Set ℝ²} (hK : Convex ℝ K) (hKcl : IsClosed K)
    {c : ℝ²} {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hball : Metric.closedBall c r ⊆ K) :
    Metric.cthickening ε K ⊆ AffineMap.homothety c (1 + ε / r) '' K := by
  have hcK : c ∈ K := hball (Metric.mem_closedBall_self hr.le)
  rcases eq_or_lt_of_le hε with rfl | hεpos
  · simp [Metric.cthickening_zero]
  have hlam : (0 : ℝ) < 1 + ε / r := by positivity
  have hlamne : (1 : ℝ) + ε / r ≠ 0 := ne_of_gt hlam
  intro z hz
  -- `K` is closed and nonempty in a proper space, so the distance to `K` is attained.
  obtain ⟨y, hyK, hy⟩ := hKcl.exists_infDist_eq_dist ⟨c, hcK⟩ z
  have hinf : Metric.infDist z K ≤ ε := by
    rw [Metric.infDist, ← ENNReal.toReal_ofReal hε]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (Metric.mem_cthickening_iff.mp hz)
  have hbnorm : ‖z - y‖ ≤ ε := by rw [← dist_eq_norm, ← hy]; exact hinf
  -- The point of the disc lying in the direction of the displacement `z - y`.
  have huK : c + (r / ε) • (z - y) ∈ K := by
    refine hball ?_
    rw [Metric.mem_closedBall, dist_eq_norm, show c + (r / ε) • (z - y) - c = (r / ε) • (z - y) by
      abel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hεpos]
    nlinarith [hbnorm, hr.le, norm_nonneg (z - y)]
  refine ⟨(1 / (1 + ε / r)) • y + (1 - 1 / (1 + ε / r)) • (c + (r / ε) • (z - y)), ?_, ?_⟩
  · refine hK hyK huK (by positivity) ?_ (by ring)
    have : 1 / (1 + ε / r) ≤ 1 := by
      rw [div_le_one hlam]
      have : 0 < ε / r := by positivity
      linarith
    linarith
  · rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    match_scalars <;> field_simp <;> ring

/-- Volume form of the dilation bound: the `ε`-thickening of a convex set
containing a disc of radius `r` has volume at most `(1 + ε/r)²` times its own. -/
lemma volume_cthickening_le_of_closedBall_subset {K : Set ℝ²} (hK : Convex ℝ K)
    {c : ℝ²} {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hball : Metric.closedBall c r ⊆ K) :
    volume (Metric.cthickening ε K) ≤ ENNReal.ofReal ((1 + ε / r) ^ 2) * volume K := by
  have hclconv : Convex ℝ (closure K) := hK.closure
  have hclball : Metric.closedBall c r ⊆ closure K := hball.trans subset_closure
  calc volume (Metric.cthickening ε K)
      = volume (Metric.cthickening ε (closure K)) := by rw [Metric.cthickening_closure]
    _ ≤ volume (AffineMap.homothety c (1 + ε / r) '' closure K) :=
        measure_mono (cthickening_subset_homothety hclconv isClosed_closure hr hε hclball)
    _ = ENNReal.ofReal |(1 + ε / r) ^ (Module.finrank ℝ ℝ²)| * volume (closure K) :=
        MeasureTheory.Measure.addHaar_image_homothety volume _ _ _
    _ = ENNReal.ofReal ((1 + ε / r) ^ 2) * volume (closure K) := by
        rw [finrank_euclideanSpace_fin, abs_of_nonneg (by positivity)]
    _ ≤ ENNReal.ofReal ((1 + ε / r) ^ 2) * volume K :=
        mul_le_mul' le_rfl (volume_closure_le_of_convex hK)

/-! ## Every worm cover contains a disc of radius `1/20` -/

/-- Convex combinations of three points of a convex set stay in the set. -/
private lemma mem_of_convex_three {s : Set ℝ²} (hs : Convex ℝ s) {A B C : ℝ²}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 1) :
    a • A + b • B + c • C ∈ s := by
  have h := hs.sum_mem (t := Finset.univ) (w := ![a, b, c]) (z := ![A, B, C])
    (by intro i _; fin_cases i <;> simpa)
    (by simp [Fin.sum_univ_three]; linarith)
    (by intro i _; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_three] using h

/-- Each coordinate of a point of `ℝ²` differs from that of another by at most
their distance. -/
lemma abs_sub_coord_le_dist (p q : ℝ²) (i : Fin 2) : |p i - q i| ≤ dist p q := by
  rw [EuclideanSpace.dist_eq]
  have hle : dist (p.ofLp i) (q.ofLp i) ^ 2 ≤ ∑ j, dist (p.ofLp j) (q.ofLp j) ^ 2 :=
    Finset.single_le_sum (f := fun j => dist (p.ofLp j) (q.ofLp j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h1 : |p i - q i| = dist (p.ofLp i) (q.ofLp i) := (Real.dist_eq _ _).symm
  rw [h1, show dist (p.ofLp i) (q.ofLp i)
      = Real.sqrt (dist (p.ofLp i) (q.ofLp i) ^ 2) from (Real.sqrt_sq dist_nonneg).symm]
  exact Real.sqrt_le_sqrt hle

/-- The parametrisation of the "V" worm: the unit-length path running from
`(0,0)` to `(1/2,0)` and then to `(1/2,1/2)`. -/
noncomputable def vPath (u : ℝ) : ℝ² :=
  WithLp.toLp 2 ![min u (1 / 2), max (u - 1 / 2) 0]

@[simp] lemma vPath_apply_zero (u : ℝ) : vPath u 0 = min u (1 / 2) := by simp [vPath]

@[simp] lemma vPath_apply_one (u : ℝ) : vPath u 1 = max (u - 1 / 2) 0 := by simp [vPath]

/-- The two coordinate ramps of `vPath` add up to the parameter. -/
private lemma vPath_coord_add (u : ℝ) : min u (1 / 2) + max (u - 1 / 2) 0 = u := by
  rcases le_total u (1 / 2) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring

private lemma vPath_dist_le {s t : ℝ} (hst : s ≤ t) : dist (vPath s) (vPath t) ≤ t - s := by
  set A : ℝ := min t (1 / 2) - min s (1 / 2) with hA
  set B : ℝ := max (t - 1 / 2) 0 - max (s - 1 / 2) 0 with hB
  have hA0 : 0 ≤ A := by rw [hA]; simp only [sub_nonneg]; exact min_le_min hst le_rfl
  have hB0 : 0 ≤ B := by
    rw [hB]; simp only [sub_nonneg]; exact max_le_max (by linarith) le_rfl
  have hAB : A + B = t - s := by
    rw [hA, hB]
    have h1 := vPath_coord_add t
    have h2 := vPath_coord_add s
    linarith
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  have e0 : dist ((vPath s).ofLp 0) ((vPath t).ofLp 0) = A := by
    rw [show (vPath s).ofLp 0 = min s (1 / 2) from vPath_apply_zero s,
      show (vPath t).ofLp 0 = min t (1 / 2) from vPath_apply_zero t, Real.dist_eq, hA,
      abs_sub_comm, abs_of_nonneg (by rw [← hA] at *; linarith [hA0])]
  have e1 : dist ((vPath s).ofLp 1) ((vPath t).ofLp 1) = B := by
    rw [show (vPath s).ofLp 1 = max (s - 1 / 2) 0 from vPath_apply_one s,
      show (vPath t).ofLp 1 = max (t - 1 / 2) 0 from vPath_apply_one t, Real.dist_eq, hB,
      abs_sub_comm, abs_of_nonneg (by rw [← hB] at *; linarith [hB0])]
  rw [e0, e1, ← hAB]
  calc Real.sqrt (A ^ 2 + B ^ 2) ≤ Real.sqrt ((A + B) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = A + B := Real.sqrt_sq (by linarith)

/-- The **V worm**: the unit-length path from `(0,0)` to `(1/2,0)` to `(1/2,1/2)`. -/
noncomputable def vWorm : Set ℝ² := Set.range (fun x : Set.Icc (0 : ℝ) 1 => vPath (x : ℝ))

lemma vWorm_mem_worms : vWorm ∈ Worms := by
  refine ⟨fun x => vPath (x : ℝ), ?_, rfl⟩
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq]
  rcases le_total (x : ℝ) (y : ℝ) with h | h
  · rw [abs_of_nonpos (by linarith), neg_sub]; exact vPath_dist_le h
  · rw [abs_of_nonneg (by linarith), dist_comm]; exact vPath_dist_le h

/-- The disc of radius `1/20` centred at `(3/10, 1/10)` lies inside the convex
hull of the V worm (the triangle with vertices `(0,0)`, `(1/2,0)`, `(1/2,1/2)`). -/
lemma closedBall_subset_convexHull_vWorm :
    Metric.closedBall (WithLp.toLp 2 ![3 / 10, 1 / 10] : ℝ²) (1 / 20) ⊆ convexHull ℝ vWorm := by
  have hmem : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → vPath u ∈ vWorm := fun u hu => ⟨⟨u, hu⟩, rfl⟩
  have h0 : vPath 0 ∈ convexHull ℝ vWorm :=
    subset_convexHull _ _ (hmem 0 ⟨le_rfl, zero_le_one⟩)
  have h1 : vPath (1 / 2) ∈ convexHull ℝ vWorm :=
    subset_convexHull _ _ (hmem (1 / 2) ⟨by norm_num, by norm_num⟩)
  have h2 : vPath 1 ∈ convexHull ℝ vWorm :=
    subset_convexHull _ _ (hmem 1 ⟨zero_le_one, le_rfl⟩)
  intro p hp
  rw [Metric.mem_closedBall] at hp
  have hc0 : (WithLp.toLp 2 ![3 / 10, 1 / 10] : ℝ²) 0 = 3 / 10 := by simp
  have hc1 : (WithLp.toLp 2 ![3 / 10, 1 / 10] : ℝ²) 1 = 1 / 10 := by simp
  have hd0 : |p 0 - 3 / 10| ≤ 1 / 20 := by
    have := abs_sub_coord_le_dist p (WithLp.toLp 2 ![3 / 10, 1 / 10] : ℝ²) 0
    rw [hc0] at this; linarith
  have hd1 : |p 1 - 1 / 10| ≤ 1 / 20 := by
    have := abs_sub_coord_le_dist p (WithLp.toLp 2 ![3 / 10, 1 / 10] : ℝ²) 1
    rw [hc1] at this; linarith
  rw [abs_le] at hd0 hd1
  have hp_eq : p = (1 - 2 * p 0) • vPath 0 + (2 * p 0 - 2 * p 1) • vPath (1 / 2)
      + (2 * p 1) • vPath 1 := by
    ext i
    fin_cases i <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> (norm_num; try ring)
  rw [hp_eq]
  refine mem_of_convex_three (convex_convexHull ℝ vWorm) h0 h1 h2 ?_ ?_ ?_ (by ring)
  · linarith [hd0.2]
  · linarith [hd0.1, hd1.2]
  · linarith [hd1.1]

/-- **Every cover of a family containing the V worm contains a disc of radius
`1/20`.** The cover must contain a placed copy of the V worm, hence (being a
superset of the convex hull of the placed copies) a placed copy of the disc
inside the worm's hull. -/
lemma exists_closedBall_subset_of_isPlacementCover {S : Set (Set ℝ²)} {K : Set ℝ²}
    (hvW : vWorm ∈ S) (hK : IsPlacementCover S K) :
    ∃ c : ℝ², Metric.closedBall c (1 / 20) ⊆ K := by
  obtain ⟨g, hgop, hsub⟩ := hK
  set g₀ : ℝ² → ℝ² := g vWorm with hg₀
  have hgop₀ : IsOrientationPreservingIsometry g₀ := hgop vWorm hvW
  have hgopc : IsOrientationPreservingIsometry g₀ := hgop₀
  obtain ⟨e, v, _hdet, hgeq⟩ := hgop₀
  set c₀ : ℝ² := WithLp.toLp 2 ![3 / 10, 1 / 10] with hc₀
  refine ⟨g₀ c₀, ?_⟩
  -- The placed copy of the hull of the V worm sits inside `K`.
  have himg : g₀ '' convexHull ℝ vWorm ⊆ K := by
    have haff : ∀ (a b : ℝ) (x y : ℝ²), a + b = 1 → g₀ (a • x + b • y) = a • g₀ x + b • g₀ y := by
      intro a b x y hab
      rw [hgeq]
      simp only [map_add, map_smul]
      rw [show (a : ℝ) • e x + b • e y + v = a • (e x + v) + b • (e y + v) - (a + b) • v + v by
        module, hab, one_smul]
      abel
    have hconv : Convex ℝ (g₀ ⁻¹' convexHull ℝ (g₀ '' vWorm)) := by
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_preimage] at hx hy ⊢
      rw [haff a b x y hab]
      exact (convex_convexHull ℝ _) hx hy ha hb hab
    have hstep : convexHull ℝ vWorm ⊆ g₀ ⁻¹' convexHull ℝ (g₀ '' vWorm) :=
      convexHull_min (fun x hx => subset_convexHull _ _ ⟨x, hx, rfl⟩) hconv
    have hfinal : convexHull ℝ (g₀ '' vWorm) ⊆ K :=
      (convexHull_mono (Set.subset_biUnion_of_mem (u := fun s => g s '' s) hvW)).trans hsub
    rintro _ ⟨x, hx, rfl⟩
    exact hfinal (hstep hx)
  -- The placement is a surjective isometry, so it carries discs to discs.
  obtain ⟨g', _hg'op, hleft, hright⟩ := hgopc.exists_symm
  have hiso : Isometry g₀ := hgopc.isometry
  intro z hz
  rw [Metric.mem_closedBall] at hz
  refine himg ⟨g' z, ?_, hright z⟩
  refine closedBall_subset_convexHull_vWorm ?_
  rw [Metric.mem_closedBall, ← hiso.dist_eq (g' z) c₀, hright z]
  exact hz

/-! ## Near-minimal covers and the approximation algorithm -/

/-- Grid polygonal worms are worms. -/
lemma gridPolygonalWorms_subset_worms (k : ℕ) (δ : ℝ) : GridPolygonalWorms k δ ⊆ Worms := by
  rintro s ⟨f, p, hlip, -, -, -, -, rfl⟩
  exact ⟨f, hlip, rfl⟩

/-- `IsNearMinimalCover S K η` states that `K` is a convex placement cover of `S`
whose area exceeds the minimal cover area by at most `η`.

This replaces the exact minimiser of `IsMinimalCover`: attainment of the
infimum needs the Blaschke selection theorem, which Mathlib does not have, while
near-minimisers exist by the definition of an infimum and serve the same purpose
in the approximation algorithm. -/
def IsNearMinimalCover (S : Set (Set ℝ²)) (K : Set ℝ²) (η : ℝ≥0∞) : Prop :=
  Convex ℝ K ∧ IsPlacementCover S K ∧ volume K ≤ minimalCoverArea S + η

/-- Near-minimal convex covers exist: pick a placement cover of area within `η`
of the infimum and replace it by the convex hull of its placed copies, which is
convex, is still a placement cover, and has no larger area. -/
lemma exists_isNearMinimalCover (S : Set (Set ℝ²)) {η : ℝ≥0∞} (hη : 0 < η)
    (hfin : minimalCoverArea S ≠ ⊤) : ∃ K, IsNearMinimalCover S K η := by
  have hlt : sInf {v | ∃ X, IsPlacementCover S X ∧ volume X = v}
      < minimalCoverArea S + η := ENNReal.lt_add_right hfin hη.ne'
  obtain ⟨v, ⟨X, hX, rfl⟩, hv⟩ := sInf_lt_iff.mp hlt
  obtain ⟨g, hgop, hgsub⟩ := hX
  exact ⟨convexHull ℝ (⋃ s ∈ S, g s '' s), convex_convexHull _ _, ⟨g, hgop, subset_rfl⟩,
    le_trans (measure_mono hgsub) hv.le⟩

/-- **Approximating the Moser number** (`thm:approxAlgorithm`).
For any target accuracy `x > 0` there are a finite `ε`-net `S` of worms and a
convex placement cover `K` of `S` giving the lower bound `area (K S) ≤ M` and the
upper bound `M ≤ area (K^ε)`, with the two bounds differing by at most `x`.

The three ingredients are the finite grid `ε`-net (`finiteWormEpsilonNet`), the a
priori bound `M ≤ π/4` (`moserCoverNumber_le_pi_div_four`), and the dilation
bound (`volume_cthickening_le_of_closedBall_subset`) applied to the disc of
radius `1/20` that every cover must contain
(`exists_closedBall_subset_of_isPlacementCover`). -/
theorem approxAlgorithm (x : ℝ) (hx : 0 < x) :
    ∃ (ε : ℝ) (S : Set (Set ℝ²)) (K : Set ℝ²),
      0 < ε ∧ S.Finite ∧ IsWormEpsilonNet ε S ∧ S ⊆ Worms ∧
      Convex ℝ K ∧ IsPlacementCover S K ∧
      minimalCoverArea S ≤ moserCoverNumber ∧
      moserCoverNumber ≤ volume (Metric.cthickening ε K) ∧
      volume (Metric.cthickening ε K) ≠ ⊤ ∧
      (volume (Metric.cthickening ε K)).toReal - (minimalCoverArea S).toReal ≤ x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set d : ℝ := x / (2 * (Real.pi / 4 + 1)) with hddef
  have hd0 : 0 < d := by rw [hddef]; positivity
  set ε : ℝ := min (d / 80) (1 / 400) with hεdef
  have hε0 : 0 < ε := lt_min (by positivity) (by norm_num)
  -- The finite net, enlarged by the V worm so that every cover of it contains a disc.
  obtain ⟨k, δ, hδ, hSfin, hnet⟩ := finiteWormEpsilonNet ε hε0
  set S : Set (Set ℝ²) := insert vWorm (GridPolygonalWorms k δ) with hSdef
  have hSfin' : S.Finite := hSfin.insert _
  have hnet' : IsWormEpsilonNet ε S := by
    intro s hs
    obtain ⟨t, ht, hsub⟩ := hnet s hs
    exact ⟨t, Set.mem_insert_of_mem _ ht, hsub⟩
  have hSw : S ⊆ Worms :=
    Set.insert_subset_iff.mpr ⟨vWorm_mem_worms, gridPolygonalWorms_subset_worms k δ⟩
  have hlow : minimalCoverArea S ≤ moserCoverNumber := moserCoverNumber_lowerBound S hSfin' hSw
  have hLfin : minimalCoverArea S ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hlow.trans moserCoverNumber_le_pi_div_four)
  -- A near-minimal convex cover of the net.
  set η : ℝ := x / (4 * (1 + d)) with hηdef
  have hη0 : 0 < η := by rw [hηdef]; positivity
  obtain ⟨K, hKconv, hKPC, hKvol⟩ :=
    exists_isNearMinimalCover S (η := ENNReal.ofReal η) (by simpa using hη0) hLfin
  -- Quantitative gap estimate.
  obtain ⟨c, hc⟩ := exists_closedBall_subset_of_isPlacementCover (Set.mem_insert _ _) hKPC
  have hlam : volume (Metric.cthickening ε K)
      ≤ ENNReal.ofReal ((1 + ε / (1 / 20)) ^ 2) * volume K :=
    volume_cthickening_le_of_closedBall_subset hKconv (by norm_num) hε0.le hc
  set lam : ℝ := (1 + ε / (1 / 20)) ^ 2 with hlamdef
  have hlam1 : 1 ≤ lam := by
    rw [hlamdef]; nlinarith [hε0]
  have hlamd : lam ≤ 1 + d := by
    rw [hlamdef]
    have h1 : ε ≤ d / 80 := min_le_left _ _
    have h2 : ε ≤ 1 / 400 := min_le_right _ _
    have : (1 + ε / (1 / 20)) ^ 2 = 1 + 40 * ε + 400 * ε ^ 2 := by field_simp; ring
    rw [this]
    nlinarith [hε0, hd0]
  -- Finiteness of the volumes involved.
  have hKfin : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [hLfin]) hKvol
  have hAle : (volume K).toReal ≤ (minimalCoverArea S).toReal + η := by
    have := ENNReal.toReal_mono (by simp [hLfin]) hKvol
    rwa [ENNReal.toReal_add hLfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hη0.le] at this
  have hLpi : (minimalCoverArea S).toReal ≤ Real.pi / 4 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hlow.trans moserCoverNumber_le_pi_div_four)
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hLnn : 0 ≤ (minimalCoverArea S).toReal := ENNReal.toReal_nonneg
  have hAnn : 0 ≤ (volume K).toReal := ENNReal.toReal_nonneg
  have hne : ENNReal.ofReal lam * volume K ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin
  have hthickfin : volume (Metric.cthickening ε K) ≠ ⊤ := ne_top_of_le_ne_top hne hlam
  refine ⟨ε, S, K, hε0, hSfin', hnet', hSw, hKconv, hKPC, hlow,
    moserCoverNumber_le_volume_cthickening ε S hnet' K hKconv hKPC, hthickfin, ?_⟩
  have hgap : (volume (Metric.cthickening ε K)).toReal ≤ lam * (volume K).toReal := by
    have := ENNReal.toReal_mono hne hlam
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
  -- Arithmetic: `(λ - 1) * area(K) + λ * η ≤ x/2 + x/4 ≤ x`.
  have hstep1 : lam * (volume K).toReal
      ≤ lam * ((minimalCoverArea S).toReal + η) := by
    exact mul_le_mul_of_nonneg_left hAle (by linarith)
  have hstep2 : (lam - 1) * (minimalCoverArea S).toReal ≤ d * (Real.pi / 4) := by
    have h1 : lam - 1 ≤ d := by linarith
    nlinarith [hLnn, hLpi, hd0]
  have hstep3 : lam * η ≤ x / 4 := by
    have : lam * η ≤ (1 + d) * η := mul_le_mul_of_nonneg_right hlamd hη0.le
    rw [hηdef] at this ⊢
    have hne : (1 : ℝ) + d ≠ 0 := by positivity
    calc lam * (x / (4 * (1 + d))) ≤ (1 + d) * (x / (4 * (1 + d))) := this
      _ = x / 4 := by field_simp
  have hstep4 : d * (Real.pi / 4) ≤ x / 2 := by
    rw [hddef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hpi, hx.le]
  linarith

/-- **Convergent bounds on the Moser cover number.**
There are sequences of lower and upper bounds, each obtained from a finite
`ε`-net and a convex near-minimal cover, whose gap is at most `1/(n+1)`. -/
theorem exists_bounds_converging :
    ∃ L U : ℕ → ℝ≥0∞,
      (∀ n, L n ≤ moserCoverNumber) ∧ (∀ n, moserCoverNumber ≤ U n) ∧
        (∀ n, U n ≠ ⊤) ∧ (∀ n, (U n).toReal - (L n).toReal ≤ 1 / (n + 1)) := by
  have h : ∀ n : ℕ, ∃ p : ℝ≥0∞ × ℝ≥0∞,
      p.1 ≤ moserCoverNumber ∧ moserCoverNumber ≤ p.2 ∧ p.2 ≠ ⊤ ∧
        p.2.toReal - p.1.toReal ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨ε, S, K, -, -, -, -, -, -, hlow, hup, hfin, hgap⟩ :=
      approxAlgorithm (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨(minimalCoverArea S, volume (Metric.cthickening ε K)), hlow, hup, hfin, hgap⟩
  choose p hp using h
  exact ⟨fun n => (p n).1, fun n => (p n).2, fun n => (hp n).1, fun n => (hp n).2.1,
    fun n => (hp n).2.2.1, fun n => (hp n).2.2.2⟩

/-- **The Moser cover number is approximable to any accuracy.**
The gap between the computed lower and upper bounds tends to `0`, so the two
sequences converge to `M` from below and above. This is the mathematical content
of the claim that the Moser constant can be approximated to within any `ε > 0`:
each bound is the area of an explicit convex cover of an explicit finite net of
polygonal worms. -/
theorem tendsto_bounds_gap_zero :
    ∃ L U : ℕ → ℝ≥0∞,
      (∀ n, L n ≤ moserCoverNumber) ∧ (∀ n, moserCoverNumber ≤ U n) ∧
        Filter.Tendsto (fun n => (U n).toReal - (L n).toReal) Filter.atTop (nhds 0) := by
  obtain ⟨L, U, hL, hU, hUfin, hgap⟩ := exists_bounds_converging
  refine ⟨L, U, hL, hU, ?_⟩
  refine squeeze_zero (fun n => ?_) hgap tendsto_one_div_add_atTop_nhds_zero_nat
  have : (L n).toReal ≤ (U n).toReal :=
    ENNReal.toReal_mono (hUfin n) ((hL n).trans (hU n))
  linarith

end Moser.CompactnessOutline

end
