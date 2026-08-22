module

public import Mathlib
public import Moser.Real.ClippedArea
public import Moser.Real.ExplicitBounds
meta import Mathlib
meta import Moser.Geometry.Polygon
meta import Moser.Geometry.PolygonArea
meta import Moser.Real.ExplicitBounds

public section

/-!
# Lower-bound certificates

A *cover certificate* is a finite collection `𝒦` of convex sets such that every
Moser cover contains an isometric copy of at least one member of `𝒦`. Such a
collection immediately bounds the Moser cover number from below by the smallest
area in the collection (`le_moserCoverNumber_of_certificate`).

This is the shape of the working-set invariant `WorkingSet.Sound` of
`Moser.LowerBound`, stated directly in the real plane so that a certificate can
be exhibited and verified without the rational-polygon search machinery.

## The certificate built here

`certList` is a list of **96 convex sets** with
`certificate_le_moserCoverNumber : 41/250 ≤ M`, improving the single-worm bound
`3233/20808 ≈ 0.1554` of `Moser.hexWormArea_le_moserCoverNumber`.

The construction has three ingredients.

* Every cover contains a placed copy of the hexagonal worm, hence of its hull
  `H`, and `H` contains a disc of radius `hexRho` about `hexCenter`
  (`disc_subset_hexHull`).
* Every cover contains a unit segment, so it contains a point `p` at distance at
  least `1/2` from that disc's centre (`exists_far_point`); rescaling puts it at
  distance exactly `1/2`.
* The 96 offsets `farPt i` are spread around a circle of radius `farD` so that
  their hull contains the disc of radius `2 * farK` (`disc_subset_farHull`).
  Hence some offset satisfies `⟪farPt i, v⟫ ≥ farK` for the direction `v` of `p`
  (`exists_farPt_dotp`), and that inequality is exactly what puts
  `hexCenter + farPt i` inside the hull of the inscribed disc and `p`
  (`mem_hull_ball_point`).

So the cover contains the hull of `H` together with `hexCenter + farPt i`, which
is `certSet i`. The case analysis is over the 96 directions; no discretisation of
translations is needed, because the copy of `H` is pinned and the far point is
localised only up to direction.
-/

open MeasureTheory
open scoped ENNReal

namespace Moser

open Moser.CompactnessOutline ConvexPolygon

/-- The real Euclidean plane `ℝ²`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- **Cover certificate**: every Moser cover contains an isometric copy of some
member of `𝒦`. -/
def IsCoverCertificate (𝒦 : List (Set ℝ²)) : Prop :=
  ∀ C : Set ℝ², Convex ℝ C → (∀ w ∈ Worms, CoversByIsometry C w) →
    ∃ K ∈ 𝒦, ∃ g : ℝ² → ℝ², IsOrientationPreservingIsometry g ∧ g '' K ⊆ C

/-- **A certificate bounds the Moser cover number from below** by the least area
occurring in it. -/
theorem le_moserCoverNumber_of_certificate {𝒦 : List (Set ℝ²)} {a : ℝ≥0∞}
    (hcert : IsCoverCertificate 𝒦) (hmeas : ∀ K ∈ 𝒦, MeasurableSet K)
    (harea : ∀ K ∈ 𝒦, a ≤ volume K) : a ≤ moserCoverNumber := by
  refine le_moserCoverNumber_of_forall_convex_cover (fun C hconv hcov => ?_)
  obtain ⟨K, hK, g, hgop, hsub⟩ := hcert C hconv hcov
  calc a ≤ volume K := harea K hK
    _ = volume (g '' K) :=
        (volume_image_of_isOrientationPreservingIsometry hgop (hmeas K hK)).symm
    _ ≤ volume C := measure_mono hsub

/-- **Refining a certificate.** If every set of a certificate contains some set
from another list, that list is a certificate too.

This is the merging principle: a group of certificate sets may be replaced by
any common subset — in particular by their intersection — which is how a large
certificate is compressed into a small one. -/
lemma IsCoverCertificate.refine {𝒦 𝒦' : List (Set ℝ²)} (h : IsCoverCertificate 𝒦)
    (hsub : ∀ K ∈ 𝒦, ∃ K' ∈ 𝒦', K' ⊆ K) : IsCoverCertificate 𝒦' := by
  intro C hconv hcov
  obtain ⟨K, hK, g, hgop, hg⟩ := h C hconv hcov
  obtain ⟨K', hK', hKK⟩ := hsub K hK
  exact ⟨K', hK', g, hgop, (Set.image_mono hKK).trans hg⟩

/-! ## Planar tools -/

lemma norm_sq_eq (u : ℝ²) : ‖u‖ ^ 2 = (u 0) ^ 2 + (u 1) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

/-- Cauchy–Schwarz for the planar cross product. -/
lemma abs_rcross_le (u v : ℝ²) : |rcross u v| ≤ ‖u‖ * ‖v‖ := by
  have hsq : (rcross u v) ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    rw [mul_pow, norm_sq_eq, norm_sq_eq, rcross_def]
    nlinarith [sq_nonneg (u 0 * v 0 + u 1 * v 1)]
  calc |rcross u v| = Real.sqrt ((rcross u v) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((‖u‖ * ‖v‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖u‖ * ‖v‖ := Real.sqrt_sq (by positivity)

/-- **A disc inside a convex polygon.** If every directed edge of a fan-convex
vertex cycle stays at signed distance at least `r` from `c`, the closed ball of
radius `r` around `c` lies in the hull of the vertices. -/
lemma closedBall_subset_convexHull_of_edges (w : ℕ → ℝ²) (n : ℕ) (hn : 3 ≤ n) (c : ℝ²) (r : ℝ)
    (hfan : ∀ k, 1 ≤ k → k + 2 ≤ n → 0 < rcross (w (k + 1) - w k) (w 0 - w k))
    (hedge : ∀ k, k + 1 < n → r * ‖w (k + 1) - w k‖ ≤ rcross (w (k + 1) - w k) (c - w k))
    (hclose : r * ‖w 0 - w (n - 1)‖ ≤ rcross (w 0 - w (n - 1)) (c - w (n - 1))) :
    Metric.closedBall c r ⊆ convexHull ℝ (w '' Set.Iio n) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have key : ∀ u : ℝ², ∀ b : ℝ², r * ‖u‖ ≤ rcross u (c - b) → 0 ≤ rcross u (z - b) := by
    intro u b hub
    have hsplit : rcross u (z - b) = rcross u (c - b) + rcross u (z - c) := by
      simp only [rcross_def, PiLp.sub_apply]; ring
    have habs := abs_rcross_le u (z - c)
    rw [abs_le] at habs
    have hmul : ‖u‖ * ‖z - c‖ ≤ ‖u‖ * r := by
      exact mul_le_mul_of_nonneg_left hz (norm_nonneg u)
    rw [hsplit]
    nlinarith [habs.1, hmul, hub]
  refine mem_convexHull_fan w z n hn (fun k hk => key _ _ (hedge k hk)) (key _ _ hclose) hfan

/-! ## Transfer to rational data -/

lemma norm_sq_toEuclidean_sub (a b : Point ℚ) :
    ‖Point.toEuclidean b - Point.toEuclidean a‖ ^ 2 = ((Point.lengthSq (b - a) : ℚ) : ℝ) := by
  rw [norm_sq_eq]
  simp only [PiLp.sub_apply, toEuclidean_apply, Point.lengthSq, Pi.sub_apply]
  push_cast
  ring

lemma mul_norm_le_of_sq_le {r x : ℝ} (u : ℝ²) (hr : 0 ≤ r) (hx : 0 ≤ x)
    (h : r ^ 2 * ‖u‖ ^ 2 ≤ x ^ 2) : r * ‖u‖ ≤ x := by
  nlinarith [norm_nonneg u, hr, hx, h]

/-- The disc-in-polygon criterion, with all hypotheses stated as **decidable**
conditions on rational data. -/
lemma closedBall_subset_convexHull_of_rat (p : ℕ → Point ℚ) (n : ℕ) (hn : 3 ≤ n)
    (c : Point ℚ) (r : ℚ) (hr : 0 ≤ r)
    (hfan : ∀ k ∈ Finset.range n, 1 ≤ k → k + 2 ≤ n →
      0 < Point.crossProduct (p (k + 1) - p k) (p 0 - p k))
    (hedge : ∀ k ∈ Finset.range n, k + 1 < n →
      0 ≤ Point.crossProduct (p (k + 1) - p k) (c - p k) ∧
        r ^ 2 * Point.lengthSq (p (k + 1) - p k)
          ≤ (Point.crossProduct (p (k + 1) - p k) (c - p k)) ^ 2)
    (hclose0 : 0 ≤ Point.crossProduct (p 0 - p (n - 1)) (c - p (n - 1)))
    (hclose1 : r ^ 2 * Point.lengthSq (p 0 - p (n - 1))
      ≤ (Point.crossProduct (p 0 - p (n - 1)) (c - p (n - 1))) ^ 2) :
    Metric.closedBall (Point.toEuclidean c) (r : ℝ)
      ⊆ convexHull ℝ ((fun k => Point.toEuclidean (p k)) '' Set.Iio n) := by
  refine closedBall_subset_convexHull_of_edges (fun k => Point.toEuclidean (p k)) n hn _ _
    ?_ ?_ ?_
  · intro k hk1 hk2
    have := hfan k (Finset.mem_range.mpr (by omega)) hk1 hk2
    rw [rcross_toEuclidean]
    exact_mod_cast this
  · intro k hk
    obtain ⟨h1, h2⟩ := hedge k (Finset.mem_range.mpr (by omega)) hk
    refine mul_norm_le_of_sq_le _ (by exact_mod_cast hr) ?_ ?_
    · rw [rcross_toEuclidean]; exact_mod_cast h1
    · rw [rcross_toEuclidean, norm_sq_toEuclidean_sub]
      have : ((r ^ 2 * Point.lengthSq (p (k + 1) - p k) : ℚ) : ℝ)
          ≤ ((Point.crossProduct (p (k + 1) - p k) (c - p k) ^ 2 : ℚ) : ℝ) := by
        exact_mod_cast h2
      push_cast at this ⊢
      linarith
  · refine mul_norm_le_of_sq_le _ (by exact_mod_cast hr) ?_ ?_
    · rw [rcross_toEuclidean]; exact_mod_cast hclose0
    · rw [rcross_toEuclidean, norm_sq_toEuclidean_sub]
      have : ((r ^ 2 * Point.lengthSq (p 0 - p (n - 1)) : ℚ) : ℝ)
          ≤ ((Point.crossProduct (p 0 - p (n - 1)) (c - p (n - 1)) ^ 2 : ℚ) : ℝ) := by
        exact_mod_cast hclose1
      push_cast at this ⊢
      linarith

/-! ## The cone lemma

If `w` points into the ball's "shadow" from a far point `v`, then `c + w` lies in
the hull of the ball around `c` and the point `c + v`.
-/

/-- Planar dot product. -/
def dotp (u v : ℝ²) : ℝ := u 0 * v 0 + u 1 * v 1

lemma norm_sq_eq_dotp (u : ℝ²) : ‖u‖ ^ 2 = dotp u u := by
  rw [norm_sq_eq, dotp]; ring

lemma mem_hull_ball_point {c : ℝ²} {ρ d K : ℝ} (hρ : 0 ≤ ρ) (hd : 0 < d) (hd2 : 2 * d < 1)
    (hK : K = (2 * d ^ 2 - (1 - 2 * d) ^ 2 * ρ ^ 2) / (4 * d))
    {w v : ℝ²} (hw : ‖w‖ ^ 2 ≤ d ^ 2) (hv : ‖v‖ = 1 / 2) (hwv : K ≤ dotp w v) :
    c + w ∈ convexHull ℝ (Metric.closedBall c ρ ∪ {c + v}) := by
  have h1d : (0 : ℝ) < 1 - 2 * d := by linarith
  set z : ℝ² := c + (1 / (1 - 2 * d)) • (w - (2 * d) • v) with hz
  -- the auxiliary point lies in the ball
  have hnormsq : ‖w - (2 * d) • v‖ ^ 2 ≤ ((1 - 2 * d) * ρ) ^ 2 := by
    have hexp : ‖w - (2 * d) • v‖ ^ 2
        = ‖w‖ ^ 2 - 4 * d * dotp w v + 4 * d ^ 2 * ‖v‖ ^ 2 := by
      simp only [norm_sq_eq, dotp, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have hK' : 4 * d * K = 2 * d ^ 2 - (1 - 2 * d) ^ 2 * ρ ^ 2 := by
      rw [hK]; field_simp
    rw [hexp, hv]
    nlinarith [hwv, hw, hd, hK']
  have hzball : z ∈ Metric.closedBall c ρ := by
    rw [Metric.mem_closedBall, dist_eq_norm, hz, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h1d]
    have hnn : 0 ≤ ‖w - (2 * d) • v‖ := norm_nonneg _
    nlinarith [hnormsq, hnn, h1d, hρ, mul_nonneg h1d.le hρ]
  -- and `c + w` is a convex combination of it and `c + v`
  have hcomb : c + w = (1 - 2 * d) • z + (2 * d) • (c + v) := by
    rw [hz]
    rw [smul_add, smul_smul, mul_one_div, div_self (ne_of_gt h1d)]
    module
  rw [hcomb]
  refine (convex_convexHull ℝ _) (subset_convexHull ℝ _ (Set.mem_union_left _ hzball))
    (subset_convexHull ℝ _ (Set.mem_union_right (Metric.closedBall c ρ)
      (Set.mem_singleton (c + v)))) (a := 1 - 2 * d) (b := 2 * d) ?_ ?_ ?_
  · linarith
  · linarith
  · ring

/-! ## The certificate data

`hexCenter` is the centre of a disc of radius `hexRho` inscribed in the hull of
the hexagonal worm; `farPt i`, for `i < 96`, are 96 offsets of length at most
`farD` spread around the circle.
-/

/-- Centre of a disc inscribed in the hexagonal worm's hull. -/
def hexCenter : Point ℚ := ![22/102, 28/102]

/-- Radius of that inscribed disc. -/
def hexRho : ℚ := 1367/10000

/-- Distance of the certificate's far points from `hexCenter`. -/
def farD : ℚ := 221/500

/-- Threshold for the extraction lemma: `⟪farPt i, v⟫ ≥ farK` says that
`hexCenter + farPt i` lies in the hull of the inscribed disc and `hexCenter + v`. -/
def farK : ℚ := (2 * farD ^ 2 - (1 - 2 * farD) ^ 2 * hexRho ^ 2) / (4 * farD)

def farPt : ℕ → Point ℚ
  | 0 => ![(221/500 : ℚ), (0 : ℚ)]
  | 1 => ![(441053/1000000 : ℚ), (7227/250000 : ℚ)]
  | 2 => ![(219109/500000 : ℚ), (57693/1000000 : ℚ)]
  | 3 => ![(433507/1000000 : ℚ), (8623/100000 : ℚ)]
  | 4 => ![(426939/1000000 : ℚ), (57199/500000 : ℚ)]
  | 5 => ![(418543/1000000 : ℚ), (35519/250000 : ℚ)]
  | 6 => ![(204177/500000 : ℚ), (84573/500000 : ℚ)]
  | 7 => ![(396417/1000000 : ℚ), (48873/250000 : ℚ)]
  | 8 => ![(382783/1000000 : ℚ), (221/1000 : ℚ)]
  | 9 => ![(367509/1000000 : ℚ), (122781/500000 : ℚ)]
  | 10 => ![(350661/1000000 : ℚ), (269073/1000000 : ℚ)]
  | 11 => ![(332313/1000000 : ℚ), (291431/1000000 : ℚ)]
  | 12 => ![(312541/1000000 : ℚ), (312541/1000000 : ℚ)]
  | 13 => ![(291431/1000000 : ℚ), (332313/1000000 : ℚ)]
  | 14 => ![(269073/1000000 : ℚ), (350661/1000000 : ℚ)]
  | 15 => ![(122781/500000 : ℚ), (367509/1000000 : ℚ)]
  | 16 => ![(221/1000 : ℚ), (382783/1000000 : ℚ)]
  | 17 => ![(48873/250000 : ℚ), (396417/1000000 : ℚ)]
  | 18 => ![(84573/500000 : ℚ), (204177/500000 : ℚ)]
  | 19 => ![(35519/250000 : ℚ), (418543/1000000 : ℚ)]
  | 20 => ![(57199/500000 : ℚ), (426939/1000000 : ℚ)]
  | 21 => ![(8623/100000 : ℚ), (433507/1000000 : ℚ)]
  | 22 => ![(57693/1000000 : ℚ), (219109/500000 : ℚ)]
  | 23 => ![(7227/250000 : ℚ), (441053/1000000 : ℚ)]
  | 24 => ![(0 : ℚ), (221/500 : ℚ)]
  | 25 => ![(-7227/250000 : ℚ), (441053/1000000 : ℚ)]
  | 26 => ![(-57693/1000000 : ℚ), (219109/500000 : ℚ)]
  | 27 => ![(-8623/100000 : ℚ), (433507/1000000 : ℚ)]
  | 28 => ![(-57199/500000 : ℚ), (426939/1000000 : ℚ)]
  | 29 => ![(-35519/250000 : ℚ), (418543/1000000 : ℚ)]
  | 30 => ![(-84573/500000 : ℚ), (204177/500000 : ℚ)]
  | 31 => ![(-48873/250000 : ℚ), (396417/1000000 : ℚ)]
  | 32 => ![(-221/1000 : ℚ), (382783/1000000 : ℚ)]
  | 33 => ![(-122781/500000 : ℚ), (367509/1000000 : ℚ)]
  | 34 => ![(-269073/1000000 : ℚ), (350661/1000000 : ℚ)]
  | 35 => ![(-291431/1000000 : ℚ), (332313/1000000 : ℚ)]
  | 36 => ![(-312541/1000000 : ℚ), (312541/1000000 : ℚ)]
  | 37 => ![(-332313/1000000 : ℚ), (291431/1000000 : ℚ)]
  | 38 => ![(-350661/1000000 : ℚ), (269073/1000000 : ℚ)]
  | 39 => ![(-367509/1000000 : ℚ), (122781/500000 : ℚ)]
  | 40 => ![(-382783/1000000 : ℚ), (221/1000 : ℚ)]
  | 41 => ![(-396417/1000000 : ℚ), (48873/250000 : ℚ)]
  | 42 => ![(-204177/500000 : ℚ), (84573/500000 : ℚ)]
  | 43 => ![(-418543/1000000 : ℚ), (35519/250000 : ℚ)]
  | 44 => ![(-426939/1000000 : ℚ), (57199/500000 : ℚ)]
  | 45 => ![(-433507/1000000 : ℚ), (8623/100000 : ℚ)]
  | 46 => ![(-219109/500000 : ℚ), (57693/1000000 : ℚ)]
  | 47 => ![(-441053/1000000 : ℚ), (7227/250000 : ℚ)]
  | 48 => ![(-221/500 : ℚ), (0 : ℚ)]
  | 49 => ![(-441053/1000000 : ℚ), (-7227/250000 : ℚ)]
  | 50 => ![(-219109/500000 : ℚ), (-57693/1000000 : ℚ)]
  | 51 => ![(-433507/1000000 : ℚ), (-8623/100000 : ℚ)]
  | 52 => ![(-426939/1000000 : ℚ), (-57199/500000 : ℚ)]
  | 53 => ![(-418543/1000000 : ℚ), (-35519/250000 : ℚ)]
  | 54 => ![(-204177/500000 : ℚ), (-84573/500000 : ℚ)]
  | 55 => ![(-396417/1000000 : ℚ), (-48873/250000 : ℚ)]
  | 56 => ![(-382783/1000000 : ℚ), (-221/1000 : ℚ)]
  | 57 => ![(-367509/1000000 : ℚ), (-122781/500000 : ℚ)]
  | 58 => ![(-350661/1000000 : ℚ), (-269073/1000000 : ℚ)]
  | 59 => ![(-332313/1000000 : ℚ), (-291431/1000000 : ℚ)]
  | 60 => ![(-312541/1000000 : ℚ), (-312541/1000000 : ℚ)]
  | 61 => ![(-291431/1000000 : ℚ), (-332313/1000000 : ℚ)]
  | 62 => ![(-269073/1000000 : ℚ), (-350661/1000000 : ℚ)]
  | 63 => ![(-122781/500000 : ℚ), (-367509/1000000 : ℚ)]
  | 64 => ![(-221/1000 : ℚ), (-382783/1000000 : ℚ)]
  | 65 => ![(-48873/250000 : ℚ), (-396417/1000000 : ℚ)]
  | 66 => ![(-84573/500000 : ℚ), (-204177/500000 : ℚ)]
  | 67 => ![(-35519/250000 : ℚ), (-418543/1000000 : ℚ)]
  | 68 => ![(-57199/500000 : ℚ), (-426939/1000000 : ℚ)]
  | 69 => ![(-8623/100000 : ℚ), (-433507/1000000 : ℚ)]
  | 70 => ![(-57693/1000000 : ℚ), (-219109/500000 : ℚ)]
  | 71 => ![(-7227/250000 : ℚ), (-441053/1000000 : ℚ)]
  | 72 => ![(0 : ℚ), (-221/500 : ℚ)]
  | 73 => ![(7227/250000 : ℚ), (-441053/1000000 : ℚ)]
  | 74 => ![(57693/1000000 : ℚ), (-219109/500000 : ℚ)]
  | 75 => ![(8623/100000 : ℚ), (-433507/1000000 : ℚ)]
  | 76 => ![(57199/500000 : ℚ), (-426939/1000000 : ℚ)]
  | 77 => ![(35519/250000 : ℚ), (-418543/1000000 : ℚ)]
  | 78 => ![(84573/500000 : ℚ), (-204177/500000 : ℚ)]
  | 79 => ![(48873/250000 : ℚ), (-396417/1000000 : ℚ)]
  | 80 => ![(221/1000 : ℚ), (-382783/1000000 : ℚ)]
  | 81 => ![(122781/500000 : ℚ), (-367509/1000000 : ℚ)]
  | 82 => ![(269073/1000000 : ℚ), (-350661/1000000 : ℚ)]
  | 83 => ![(291431/1000000 : ℚ), (-332313/1000000 : ℚ)]
  | 84 => ![(312541/1000000 : ℚ), (-312541/1000000 : ℚ)]
  | 85 => ![(332313/1000000 : ℚ), (-291431/1000000 : ℚ)]
  | 86 => ![(350661/1000000 : ℚ), (-269073/1000000 : ℚ)]
  | 87 => ![(367509/1000000 : ℚ), (-122781/500000 : ℚ)]
  | 88 => ![(382783/1000000 : ℚ), (-221/1000 : ℚ)]
  | 89 => ![(396417/1000000 : ℚ), (-48873/250000 : ℚ)]
  | 90 => ![(204177/500000 : ℚ), (-84573/500000 : ℚ)]
  | 91 => ![(418543/1000000 : ℚ), (-35519/250000 : ℚ)]
  | 92 => ![(426939/1000000 : ℚ), (-57199/500000 : ℚ)]
  | 93 => ![(433507/1000000 : ℚ), (-8623/100000 : ℚ)]
  | 94 => ![(219109/500000 : ℚ), (-57693/1000000 : ℚ)]
  | 95 => ![(441053/1000000 : ℚ), (-7227/250000 : ℚ)]
  | _ => ![(221/500 : ℚ), (0 : ℚ)]

/-! ## The two inscribed discs -/

lemma toEuclidean_zero : Point.toEuclidean ![0, 0] = (0 : ℝ²) := by
  ext i; fin_cases i <;> simp [toEuclidean_apply]

lemma hexNode_image :
    (fun k => Point.toEuclidean (hexNodeQ k)) '' Set.Iio 7
      = Set.range fun i : Fin HexWormPoly.vertex_count =>
          Point.toEuclidean (HexWormPoly.vertices i) := by
  have hvc : HexWormPoly.vertex_count = 7 := hexWormPoly_vertex_count
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp only [Set.mem_Iio] at hk
    refine ⟨⟨k, by omega⟩, ?_⟩
    show Point.toEuclidean (HexWormPoly.vertices ⟨k, by omega⟩) = _
    rw [hexWormPoly_vertices]
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    refine ⟨(i : ℕ), ?_, ?_⟩
    · simp only [Set.mem_Iio]; omega
    · show Point.toEuclidean (hexNodeQ (i : ℕ)) = Point.toEuclidean (HexWormPoly.vertices i)
      rw [hexWormPoly_vertices]

/-- A disc of radius `hexRho` around `hexCenter` sits inside the hexagonal worm's
convex hull. -/
lemma disc_subset_hexHull :
    Metric.closedBall (Point.toEuclidean hexCenter) ((hexRho : ℚ) : ℝ)
      ⊆ convexHull ℝ hexWorm := by
  have h := closedBall_subset_convexHull_of_rat hexNodeQ 7 (by norm_num) hexCenter hexRho
    (by norm_num [hexRho]) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  refine h.trans (le_of_eq ?_)
  rw [convexHull_hexWorm, ConvexPolygon.realHull_eq, hexNode_image]

/-- A disc of radius `2 * farK` around the origin sits inside the hull of the 96
far offsets. -/
lemma disc_subset_farHull :
    Metric.closedBall (0 : ℝ²) ((2 * farK : ℚ) : ℝ)
      ⊆ convexHull ℝ ((fun k => Point.toEuclidean (farPt k)) '' Set.Iio 96) := by
  have h := closedBall_subset_convexHull_of_rat farPt 96 (by norm_num) ![0, 0] (2 * farK)
    (by norm_num [farK, farD, hexRho]) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  rwa [toEuclidean_zero] at h

/-! ## The unit segment worm and the far point -/

/-- The unit segment, as a worm. -/
noncomputable def segPath (u : ℝ) : ℝ² := WithLp.toLp 2 ![u, 0]

lemma segPath_dist (s t : ℝ) : dist (segPath s) (segPath t) = |s - t| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  have e0 : ∀ u : ℝ, (segPath u : ℝ²) 0 = u := by intro u; simp [segPath]
  have e1 : ∀ u : ℝ, (segPath u : ℝ²) 1 = 0 := by intro u; simp [segPath]
  rw [show (WithLp.ofLp (segPath s)) 0 = s from e0 s, show (WithLp.ofLp (segPath t)) 0 = t from e0 t,
    show (WithLp.ofLp (segPath s)) 1 = (0:ℝ) from e1 s,
    show (WithLp.ofLp (segPath t)) 1 = (0:ℝ) from e1 t]
  simp only [Real.dist_eq, sub_zero, abs_zero]
  rw [show |s - t| ^ 2 + (0:ℝ) ^ 2 = |s - t| ^ 2 by ring, Real.sqrt_sq (abs_nonneg _)]

/-- The unit segment worm. -/
noncomputable def segWorm : Set ℝ² := Set.range (fun x : Set.Icc (0 : ℝ) 1 => segPath (x : ℝ))

lemma segWorm_mem_worms : segWorm ∈ Worms := by
  refine ⟨fun x => segPath (x : ℝ), ?_, rfl⟩
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [NNReal.coe_one, one_mul, segPath_dist, Subtype.dist_eq, Real.dist_eq]

/-- **Any cover contains a point far from any given point of it**: it contains a
unit segment, one of whose endpoints is at distance at least `1/2`. -/
lemma exists_far_point {C : Set ℝ²} (hcov : ∀ w ∈ Worms, CoversByIsometry C w) (c : ℝ²) :
    ∃ p ∈ C, 1 / 2 ≤ dist p c := by
  obtain ⟨g, hgop, hsub⟩ := hcov segWorm segWorm_mem_worms
  obtain ⟨h, hhop, hleft, hright⟩ := hgop.exists_symm
  have hmem : ∀ z ∈ segWorm, h z ∈ C := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hsub hz
    rwa [hleft y]
  have h0 : segPath 0 ∈ segWorm := ⟨⟨0, by constructor <;> norm_num⟩, rfl⟩
  have h1 : segPath 1 ∈ segWorm := ⟨⟨1, by constructor <;> norm_num⟩, rfl⟩
  have hd : dist (h (segPath 0)) (h (segPath 1)) = 1 := by
    rw [hhop.isometry.dist_eq, segPath_dist]
    norm_num
  by_contra hcon
  push Not at hcon
  have hA := hcon _ (hmem _ h0)
  have hB := hcon _ (hmem _ h1)
  have := dist_triangle (h (segPath 0)) c (h (segPath 1))
  rw [hd, dist_comm c (h (segPath 1))] at this
  linarith

/-! ## Extraction: some far offset points towards any given direction -/

lemma dotp_smul_left (a : ℝ) (u v : ℝ²) : dotp (a • u) v = a * dotp u v := by
  simp only [dotp, PiLp.smul_apply, smul_eq_mul]; ring

lemma convex_dotp_le (v : ℝ²) (m : ℝ) : Convex ℝ {x : ℝ² | dotp x v ≤ m} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq, dotp, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  have hrw : (a * x 0 + b * y 0) * v 0 + (a * x 1 + b * y 1) * v 1
      = a * (x 0 * v 0 + x 1 * v 1) + b * (y 0 * v 0 + y 1 * v 1) := by ring
  rw [hrw]
  calc a * (x 0 * v 0 + x 1 * v 1) + b * (y 0 * v 0 + y 1 * v 1) ≤ a * m + b * m :=
        add_le_add h1 h2
    _ = m := by rw [← add_mul, hab, one_mul]

/-- **Extraction lemma.** For every direction `v` of length `1/2` some far offset
has inner product at least `farK` with it — because the hull of the offsets
contains the disc of radius `2 * farK`. -/
lemma exists_farPt_dotp {v : ℝ²} (hv : ‖v‖ = 1 / 2) :
    ∃ i < 96, ((farK : ℚ) : ℝ) ≤ dotp (Point.toEuclidean (farPt i)) v := by
  have hKpos : (0 : ℝ) < ((farK : ℚ) : ℝ) := by
    have : (0 : ℚ) < farK := by norm_num [farK, farD, hexRho]
    exact_mod_cast this
  set S : Finset ℕ := Finset.range 96 with hS
  have hSne : S.Nonempty := ⟨0, by simp [hS]⟩
  obtain ⟨j, hjS, hjmax⟩ := S.exists_max_image (fun i => dotp (Point.toEuclidean (farPt i)) v) hSne
  refine ⟨j, by simpa [hS] using hjS, ?_⟩
  -- the scaled direction lies in the hull of the offsets
  set z : ℝ² := (4 * ((farK : ℚ) : ℝ)) • v with hz
  have hzball : z ∈ Metric.closedBall (0 : ℝ²) ((2 * farK : ℚ) : ℝ) := by
    rw [Metric.mem_closedBall, dist_zero_right, hz, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith), hv]
    push_cast
    linarith
  have hzhull := disc_subset_farHull hzball
  -- the half-plane through the maximum contains all offsets, hence their hull
  have hsub : (fun k => Point.toEuclidean (farPt k)) '' Set.Iio 96
      ⊆ {x : ℝ² | dotp x v ≤ dotp (Point.toEuclidean (farPt j)) v} := by
    rintro _ ⟨k, hk, rfl⟩
    exact hjmax k (by simpa [hS] using hk)
  have hzle : dotp z v ≤ dotp (Point.toEuclidean (farPt j)) v :=
    convexHull_min hsub (convex_dotp_le v _) hzhull
  have hdz : dotp z v = ((farK : ℚ) : ℝ) := by
    rw [hz, dotp_smul_left]
    have : dotp v v = ‖v‖ ^ 2 := (norm_sq_eq_dotp v).symm
    rw [this, hv]
    ring
  linarith [hdz ▸ hzle]

/-! ## The certificate -/

lemma toEuclidean_add (a b : Point ℚ) :
    Point.toEuclidean (a + b) = Point.toEuclidean a + Point.toEuclidean b := by
  ext i
  fin_cases i <;>
    · simp only [toEuclidean_apply, PiLp.add_apply, Pi.add_apply]
      push_cast
      ring

lemma norm_sq_toEuclidean (a : Point ℚ) :
    ‖Point.toEuclidean a‖ ^ 2 = ((Point.lengthSq a : ℚ) : ℝ) := by
  rw [norm_sq_eq]
  simp only [toEuclidean_apply, Point.lengthSq]
  push_cast
  ring

/-- The `i`-th certificate set: the convex hull of the hexagonal worm's vertices
together with the `i`-th far point. -/
noncomputable def certSet (i : ℕ) : Set ℝ² :=
  convexHull ℝ (Point.toEuclidean ''
    {p : Point ℚ | p ∈ (hexCenter + farPt i) :: HexWormPoly.vertex_list})

/-- The rational polygon whose real region is `certSet i`: the verified hull of
the hexagonal worm's vertices together with the `i`-th far point. This is the
computable handle on the certificate, used for display. -/
def certPolygon (i : ℕ) : Option (ConvexPolygon ℚ) :=
  ConvexPolygon.ofListChecked ((hexCenter + farPt i) :: HexWormPoly.vertex_list)

/-- What `certPolygon` returns really is the certificate set. -/
lemma certPolygon_realHull {i : ℕ} {q : ConvexPolygon ℚ} (h : certPolygon i = some q) :
    q.realHull = certSet i :=
  ConvexPolygon.realHull_ofListChecked h

/-- Every one of the 96 certificate polygons is nondegenerate, so the picture
really does show all 96 sets. -/
lemma certPolygon_isSome : ∀ i ∈ Finset.range 96, (certPolygon i).isSome := by
  native_decide

/-- **The certificate**: a list of 96 convex sets. -/
noncomputable def certList : List (Set ℝ²) := (List.range 96).map certSet

lemma certList_length : certList.length = 96 := by simp [certList]

/-- Unfolding lemma for `certList`, usable from other modules. -/
lemma certList_eq : certList = (List.range 96).map certSet := by rw [certList]

/-- Each far offset is at distance at most `farD` from the centre. -/
lemma farPt_lengthSq : ∀ i ∈ Finset.range 96, Point.lengthSq (farPt i) ≤ farD ^ 2 := by
  native_decide

/-- Each certificate set has area at least `41/250`. -/
lemma cert_area_check : ∀ i ∈ Finset.range 96,
    ((ConvexPolygon.ofListChecked ((hexCenter + farPt i) :: HexWormPoly.vertex_list)).map
      (fun q => decide ((41 / 250 : ℚ) ≤ q.area))).getD false = true := by
  native_decide

lemma certSet_measurable (i : ℕ) : MeasurableSet (certSet i) := by
  refine (Set.Finite.isCompact_convexHull ℝ (Set.Finite.image _ ?_)).isClosed.measurableSet
  exact List.finite_toSet _

lemma certSet_volume {i : ℕ} (hi : i < 96) :
    ENNReal.ofReal ((41 : ℝ) / 250) ≤ volume (certSet i) := by
  have hcheck := cert_area_check i (Finset.mem_range.mpr hi)
  rcases hof : ConvexPolygon.ofListChecked ((hexCenter + farPt i) :: HexWormPoly.vertex_list) with
    _ | q
  · rw [hof] at hcheck; simp at hcheck
  · rw [hof] at hcheck
    simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at hcheck
    have hreal := ConvexPolygon.realHull_ofListChecked hof
    have hvol := ConvexPolygon.volume_realHull q
    rw [hreal] at hvol
    rw [certSet, hvol]
    refine ENNReal.ofReal_le_ofReal ?_
    have hc2 : ((41 / 250 : ℚ) : ℝ) ≤ ((q.area : ℚ) : ℝ) := by exact_mod_cast hcheck
    push_cast at hc2
    linarith

/-- **The 96 sets form a cover certificate.** -/
theorem isCoverCertificate_certList : IsCoverCertificate certList := by
  intro C hconv hcov
  -- place the hexagonal worm inside `C`
  obtain ⟨g, hgop, hsub⟩ := hcov hexWorm hexWorm_mem_worms
  obtain ⟨h, hhop, hleft, hright⟩ := hgop.exists_symm
  have hhopc : IsOrientationPreservingIsometry h := hhop
  have hmemW : ∀ z ∈ hexWorm, h z ∈ C := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hsub hz
    rwa [hleft y]
  have hhull : ∀ z ∈ convexHull ℝ hexWorm, h z ∈ C := by
    intro z hz
    refine (image_convexHull_subset hhopc _).trans (convexHull_min ?_ hconv) ⟨z, hz, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmemW y hy
  set ĉ : ℝ² := h (Point.toEuclidean hexCenter) with hcdef
  have hisom : Isometry h := hhop.isometry
  -- the placed inscribed disc lies in `C`
  have hdiscC : ∀ z : ℝ², dist z ĉ ≤ ((hexRho : ℚ) : ℝ) → z ∈ C := by
    intro z hz
    have hzy : h (g z) = z := hleft z
    have hd : dist (g z) (Point.toEuclidean hexCenter) = dist z ĉ := by
      rw [hcdef, ← hisom.dist_eq (g z) (Point.toEuclidean hexCenter), hzy]
    refine hzy ▸ hhull _ (disc_subset_hexHull ?_)
    rw [Metric.mem_closedBall, hd]
    exact hz
  have hrho0 : (0 : ℝ) ≤ ((hexRho : ℚ) : ℝ) := by
    exact_mod_cast (by norm_num [hexRho] : (0 : ℚ) ≤ hexRho)
  have hfarD0 : (0 : ℝ) < ((farD : ℚ) : ℝ) := by
    exact_mod_cast (by norm_num [farD] : (0 : ℚ) < farD)
  have hfarD1 : 2 * ((farD : ℚ) : ℝ) < 1 := by
    have : (2 : ℚ) * farD < 1 := by norm_num [farD]
    exact_mod_cast this
  have hcC : ĉ ∈ C := hdiscC ĉ (by rw [dist_self]; exact hrho0)
  -- a far point of `C`
  obtain ⟨p, hpC, hpfar⟩ := exists_far_point hcov ĉ
  have hL : (0 : ℝ) < dist p ĉ := lt_of_lt_of_le (by norm_num) hpfar
  set p' : ℝ² := ĉ + ((1 / 2) / dist p ĉ) • (p - ĉ) with hp'
  have hp'C : p' ∈ C := by
    have hcomb : p' = (1 - (1 / 2) / dist p ĉ) • ĉ + ((1 / 2) / dist p ĉ) • p := by
      rw [hp']; module
    rw [hcomb]
    refine hconv hcC hpC ?_ (by positivity) (by ring)
    have : (1 / 2) / dist p ĉ ≤ 1 := by
      rw [div_le_one hL]; linarith
    linarith
  have hp'dist : ‖p' - ĉ‖ = 1 / 2 := by
    rw [hp', add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      ← dist_eq_norm]
    field_simp
  -- pull the direction back through the placement
  obtain ⟨e, tr, hdet, hheq⟩ := hhop
  set v : ℝ² := e.symm (p' - ĉ) with hv
  have hvnorm : ‖v‖ = 1 / 2 := by rw [hv, LinearIsometryEquiv.norm_map, hp'dist]
  have hev : e v = p' - ĉ := by rw [hv, LinearIsometryEquiv.apply_symm_apply]
  have hshift : h (Point.toEuclidean hexCenter + v) = p' := by
    have h1 : h (Point.toEuclidean hexCenter + v)
        = e (Point.toEuclidean hexCenter) + e v + tr := by
      rw [hheq]; simp only [map_add]; try abel
    have h2 : ĉ = e (Point.toEuclidean hexCenter) + tr := by simp [hcdef, hheq]
    rw [h1, hev, h2]
    try abel
  -- pick the far offset pointing that way
  obtain ⟨i, hi, hdot⟩ := exists_farPt_dotp hvnorm
  -- the cone lemma places `hexCenter + farPt i` inside the hull of the disc and `p'`
  have hcone : Point.toEuclidean hexCenter + Point.toEuclidean (farPt i)
      ∈ convexHull ℝ (Metric.closedBall (Point.toEuclidean hexCenter) ((hexRho : ℚ) : ℝ)
          ∪ {Point.toEuclidean hexCenter + v}) := by
    refine mem_hull_ball_point hrho0 hfarD0 hfarD1 ?_ ?_ hvnorm hdot
    · rw [farK]; push_cast; ring
    · rw [norm_sq_toEuclidean]
      have := farPt_lengthSq i (Finset.mem_range.mpr hi)
      have hcast : ((Point.lengthSq (farPt i) : ℚ) : ℝ) ≤ ((farD ^ 2 : ℚ) : ℝ) := by
        exact_mod_cast this
      push_cast at hcast ⊢
      linarith
  have hfarC : h (Point.toEuclidean (hexCenter + farPt i)) ∈ C := by
    rw [toEuclidean_add]
    refine (image_convexHull_subset hhopc _).trans (convexHull_min ?_ hconv) ⟨_, hcone, rfl⟩
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · refine hdiscC _ ?_
      rw [hcdef, hisom.dist_eq]
      rw [Metric.mem_closedBall] at hz
      exact hz
    · rw [Set.mem_singleton_iff] at hz
      rw [hz, hshift]
      exact hp'C
  -- conclude
  refine ⟨certSet i, ?_, h, hhopc, ?_⟩
  · rw [certList, List.mem_map]
    exact ⟨i, List.mem_range.mpr hi, rfl⟩
  · refine (image_convexHull_subset hhopc _).trans (convexHull_min ?_ hconv)
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    rcases List.mem_cons.mp hq with rfl | hmem
    · exact hfarC
    · refine hhull _ ?_
      rw [convexHull_hexWorm]
      exact toEuclidean_mem_realHull_of_mem_vertex_list hmem

/-- **A new lower bound from the certificate**: `M ≥ 41/250 = 0.164`. -/
theorem certificate_le_moserCoverNumber :
    ENNReal.ofReal ((41 : ℝ) / 250) ≤ moserCoverNumber := by
  refine le_moserCoverNumber_of_certificate isCoverCertificate_certList ?_ ?_
  · intro K hK
    rw [certList, List.mem_map] at hK
    obtain ⟨i, -, rfl⟩ := hK
    exact certSet_measurable i
  · intro K hK
    rw [certList, List.mem_map] at hK
    obtain ⟨i, hi, rfl⟩ := hK
    exact certSet_volume (List.mem_range.mp hi)

/-- The certificate uses at most 100 sets. -/
theorem certList_length_le : certList.length ≤ 100 := by
  rw [certList_length]; norm_num

/-- **The bounds, in decimal form**: `0.164 ≤ M ≤ 0.44635`. -/
theorem moserCoverNumber_bounds_certificate :
    0.164 ≤ moserCoverNumber.toReal ∧ moserCoverNumber.toReal ≤ 0.44635 := by
  refine ⟨?_, moserCoverNumber_toReal_bounds.2⟩
  have h := ENNReal.toReal_mono moserCoverNumber_ne_top certificate_le_moserCoverNumber
  rw [ENNReal.toReal_ofReal (by norm_num)] at h
  linarith

end Moser

end
