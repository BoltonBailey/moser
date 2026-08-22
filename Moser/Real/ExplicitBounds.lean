module

public import Mathlib
public import Moser.LowerBound
public import Moser.Real.Approximation
meta import Mathlib
meta import Moser.Geometry.Polygon
meta import Moser.Geometry.PolygonArea

public section

/-!
# Explicit unconditional bounds on the Moser cover number

This file turns the machinery of the development into concrete, unconditional
numeric bounds on `moserCoverNumber` — the minimal area of a convex set covering
every unit worm up to orientation-preserving isometry:

    0.15537 ≤ M ≤ 0.44635.

* **Lower bound** `hexWormArea_le_moserCoverNumber`: `M ≥ 3233/20808 ≈ 0.15537`.
  Every cover contains a placed copy of any single worm, hence of its convex
  hull. The worm used is a six-segment approximation to the semicircle, built
  from rational unit directions so that its length is exactly `1` and its hull
  area is exactly rational; the semicircle maximises the hull area of a unit
  arc, at `1/(2π) ≈ 0.15915`, so this worm captures `97.6%` of what any single
  worm can give.

* **Upper bound** `moserCoverNumber_le_stadium`: `M ≤ 1/4 + π/16 ≈ 0.44635`.
  Every worm lies within `1/4` of one of its two quarter points, which are at
  distance at most `1/2`; rotating that pair onto the `x`-axis places every worm
  inside the stadium of radius `1/4` around the segment from `(-1/4,0)` to
  `(1/4,0)`. This improves the disc bound `M ≤ π/4 ≈ 0.785` of
  `moserCoverNumber_le_pi_div_four` by a factor of `1.76`.

For orientation, the literature has `0.232239 ≤ M ≤ 0.260437`; the point here is
that these are complete, machine-checked proofs from first principles.
-/

open MeasureTheory

namespace Moser

open Moser.CompactnessOutline

/-- The real Euclidean plane `ℝ²`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## A hexagonal worm

Six segments of length `1/6`, whose directions are the rational unit vectors
`(17,0)/17`, `(15,8)/17`, `(8,15)/17`, `(0,17)/17`, `(-8,15)/17`, `(-15,8)/17`.
Rational directions keep every segment length exactly `1/6`, so the worm has
length exactly `1`, while its vertices stay rational and its hull area is an
exactly computable rational number.  The shape approximates the semicircle,
which maximises the hull area of a unit arc (`1/(2π) ≈ 0.15915`).
-/

/-- The seven nodes of the hexagonal worm. -/
def hexNodeQ : ℕ → Point ℚ
  | 0 => ![0, 0]
  | 1 => ![17 / 102, 0]
  | 2 => ![32 / 102, 8 / 102]
  | 3 => ![40 / 102, 23 / 102]
  | 4 => ![40 / 102, 40 / 102]
  | 5 => ![32 / 102, 55 / 102]
  | _ => ![17 / 102, 63 / 102]

/-- The convex hull of the hexagonal worm, as a convex polygon. -/
def HexWormPoly : ConvexPolygon ℚ where
  vertex_count := 7
  vertex_count_pos := inferInstance
  three_le_vertex_count := by norm_num
  vertices := fun i => hexNodeQ i.val
  nodup := by native_decide
  vertices_extremePoints := by native_decide

lemma hexWormPoly_vertex_count : HexWormPoly.vertex_count = 7 := by
  simp [HexWormPoly]

lemma hexWormPoly_vertices (i : Fin HexWormPoly.vertex_count) :
    HexWormPoly.vertices i = hexNodeQ (i : ℕ) := by
  simp [HexWormPoly]

/-- The hull of the hexagonal worm has area `3233/20808 ≈ 0.15537`. -/
lemma hexWormPoly_area : HexWormPoly.area = 3233 / 20808 := by native_decide

/-! ### The worm itself -/

/-- The nodes of the hexagonal worm in the real plane. -/
noncomputable def hexNode (n : ℕ) : ℝ² := Point.toEuclidean (hexNodeQ n)

lemma norm_toEuclidean_sub (a b : Point ℚ) :
    ‖Point.toEuclidean a - Point.toEuclidean b‖
      = Real.sqrt ((((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 : ℚ) : ℝ)) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fin.sum_univ_two]
  simp only [PiLp.sub_apply, toEuclidean_apply, Real.norm_eq_abs, sq_abs]
  push_cast
  ring

lemma norm_toEuclidean_sub_eq {a b : Point ℚ} {r : ℝ} (hr : 0 ≤ r)
    (h : (((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 : ℚ) : ℝ) = r ^ 2) :
    ‖Point.toEuclidean a - Point.toEuclidean b‖ = r := by
  rw [norm_toEuclidean_sub, h, Real.sqrt_sq hr]

/-- Every segment of the hexagonal worm has length exactly `1/6`. -/
lemma hexNode_gap : ∀ j < 6, ‖hexNode (j + 1) - hexNode j‖ ≤ 1 / (6 : ℝ) := by
  intro j hj
  have hle : ∀ a b : Point ℚ,
      (((a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 : ℚ) : ℝ) = (1 / 6 : ℝ) ^ 2 →
      ‖Point.toEuclidean a - Point.toEuclidean b‖ ≤ 1 / (6 : ℝ) := by
    intro a b h
    exact le_of_eq (norm_toEuclidean_sub_eq (by norm_num) h)
  interval_cases j <;>
    · refine hle _ _ ?_
      norm_num [hexNodeQ]

/-- **The hexagonal worm**: six segments of length `1/6`, so of length exactly `1`. -/
noncomputable def hexWorm : Set ℝ² := Set.range (interp 6 hexNode)

lemma hexWorm_mem_worms : hexWorm ∈ Worms :=
  ⟨interp 6 hexNode, interp_lipschitz (by norm_num) hexNode hexNode_gap, rfl⟩

/-- The convex hull of the hexagonal worm is the region of `HexWormPoly`. -/
lemma convexHull_hexWorm : convexHull ℝ hexWorm = HexWormPoly.realHull := by
  have hrange : hexWorm = ⋃ j : Fin 6, segment ℝ (hexNode (j : ℕ)) (hexNode ((j : ℕ) + 1)) := by
    rw [hexWorm]
    exact worm_range_eq_iUnion (by norm_num) hexNode (interp 6 hexNode)
      (fun x n t hn ht hx => interp_eq (by norm_num) hexNode x n t hn ht hx)
  have hvc : HexWormPoly.vertex_count = 7 := rfl
  have hvert : ∀ i : Fin HexWormPoly.vertex_count,
      Point.toEuclidean (HexWormPoly.vertices i) = hexNode (i : ℕ) := fun _ => rfl
  rw [hrange, ConvexPolygon.realHull_eq]
  refine Set.Subset.antisymm (convexHull_min (Set.iUnion_subset fun j => ?_)
    (convex_convexHull ℝ _)) (convexHull_mono ?_)
  · refine (convex_convexHull ℝ _).segment_subset ?_ ?_
    · exact subset_convexHull ℝ _ ⟨⟨(j : ℕ), by omega⟩, hvert _⟩
    · exact subset_convexHull ℝ _ ⟨⟨(j : ℕ) + 1, by omega⟩, hvert _⟩
  · rintro _ ⟨i, rfl⟩
    have hilt : (i : ℕ) < 7 := by have := i.isLt; omega
    show hexNode (i : ℕ) ∈ _
    rcases Nat.lt_or_ge (i : ℕ) 6 with hi | hi
    · exact Set.mem_iUnion.mpr ⟨⟨(i : ℕ), hi⟩, left_mem_segment ℝ _ _⟩
    · have hi6 : (i : ℕ) = 6 := by omega
      refine Set.mem_iUnion.mpr ⟨⟨5, by norm_num⟩, ?_⟩
      rw [hi6]
      exact right_mem_segment ℝ _ _

/-! ## Placements preserve area

An orientation-preserving isometry is measure preserving, and carries convex
hulls into convex hulls, so a placed copy of a worm's hull has the same area.
-/

lemma image_convexHull_subset {g : ℝ² → ℝ²} (hg : IsOrientationPreservingIsometry g)
    (S : Set ℝ²) : g '' convexHull ℝ S ⊆ convexHull ℝ (g '' S) := by
  obtain ⟨e, v, -, rfl⟩ := hg
  have haff : ∀ (a b : ℝ) (x y : ℝ²), a + b = 1 →
      e (a • x + b • y) + v = a • (e x + v) + b • (e y + v) := by
    intro a b x y hab
    simp only [map_add, map_smul]
    rw [show a • (e x + v) + b • (e y + v)
        = a • e x + b • e y + (a + b) • v by module, hab, one_smul]
  have hconv : Convex ℝ ((fun x => e x + v) ⁻¹' convexHull ℝ ((fun x => e x + v) '' S)) := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_preimage] at hx hy ⊢
    rw [haff a b x y hab]
    exact (convex_convexHull ℝ _) hx hy ha hb hab
  rintro _ ⟨x, hx, rfl⟩
  refine convexHull_min (fun z hz => ?_) hconv hx
  exact subset_convexHull ℝ _ (Set.mem_image_of_mem _ hz)

lemma measurePreserving_of_isOrientationPreservingIsometry {g : ℝ² → ℝ²}
    (hg : IsOrientationPreservingIsometry g) : MeasurePreserving g volume volume := by
  obtain ⟨e, v, -, rfl⟩ := hg
  exact (measurePreserving_add_right volume v).comp e.measurePreserving

lemma volume_image_of_isOrientationPreservingIsometry {g : ℝ² → ℝ²}
    (hg : IsOrientationPreservingIsometry g) {s : Set ℝ²} (hs : MeasurableSet s) :
    volume (g '' s) = volume s := by
  obtain ⟨g', hg'op, hleft, hright⟩ := hg.exists_symm
  rw [Set.image_eq_preimage_of_inverse hleft hright]
  exact (measurePreserving_of_isOrientationPreservingIsometry hg'op).measure_preimage
    hs.nullMeasurableSet

/-! ## The lower bound -/

/-- The area of the hexagonal worm's hull, as an extended real. -/
lemma volume_convexHull_hexWorm :
    volume (convexHull ℝ hexWorm) = ENNReal.ofReal ((3233 : ℝ) / 20808) := by
  rw [convexHull_hexWorm, ConvexPolygon.volume_realHull, hexWormPoly_area]
  norm_num

lemma measurableSet_convexHull_hexWorm : MeasurableSet (convexHull ℝ hexWorm) := by
  rw [convexHull_hexWorm, ConvexPolygon.realHull_eq]
  exact (Set.Finite.isCompact_convexHull ℝ (Set.finite_range _)).isClosed.measurableSet

/-- **A lower bound for the Moser cover number.**
Every cover must contain a placed copy of the hexagonal worm, hence of its
convex hull, whose area is `3233/20808 ≈ 0.15537`. -/
theorem hexWormArea_le_moserCoverNumber :
    ENNReal.ofReal ((3233 : ℝ) / 20808) ≤ moserCoverNumber := by
  rw [moserCoverNumber, minimalCoverArea, minimalVolume]
  refine le_sInf ?_
  rintro v ⟨X, ⟨g, hgop, hsub⟩, rfl⟩
  have hGop : IsOrientationPreservingIsometry (g hexWorm) := hgop hexWorm hexWorm_mem_worms
  have hplaced : (g hexWorm) '' (convexHull ℝ hexWorm) ⊆ X :=
    (image_convexHull_subset hGop hexWorm).trans
      ((convexHull_mono (Set.subset_biUnion_of_mem (u := fun s => g s '' s)
        hexWorm_mem_worms)).trans hsub)
  calc ENNReal.ofReal ((3233 : ℝ) / 20808)
      = volume (convexHull ℝ hexWorm) := volume_convexHull_hexWorm.symm
    _ = volume ((g hexWorm) '' (convexHull ℝ hexWorm)) :=
        (volume_image_of_isOrientationPreservingIsometry hGop
          measurableSet_convexHull_hexWorm).symm
    _ ≤ volume X := measure_mono hplaced

/-! ## An upper bound

Every worm lies within `1/4` of one of its two quarter points, which are at
distance at most `1/2` from each other.  Rotating that pair of points onto the
`x`-axis places every worm inside a fixed `1 × 1/2` box.
-/

/-- The volume of an axis-parallel box in the Euclidean plane. -/
lemma volume_box (a b c d : ℝ) :
    volume {x : ℝ² | x 0 ∈ Set.Icc a b ∧ x 1 ∈ Set.Icc c d}
      = ENNReal.ofReal (b - a) * ENNReal.ofReal (d - c) := by
  have h : {x : ℝ² | x 0 ∈ Set.Icc a b ∧ x 1 ∈ Set.Icc c d}
      = WithLp.ofLp ⁻¹' (Set.univ.pi ![Set.Icc a b, Set.Icc c d]) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi (by intro i; fin_cases i <;> exact measurableSet_Icc)).nullMeasurableSet,
    volume_pi_pi]
  simp [Fin.prod_univ_two, Real.volume_Icc]

/-- The `1 × 1/2` box that will cover every worm. -/
def boxCover : Set ℝ² :=
  {x : ℝ² | x 0 ∈ Set.Icc (-(1/2) : ℝ) (1/2) ∧ x 1 ∈ Set.Icc (-(1/4) : ℝ) (1/4)}

lemma convex_boxCover : Convex ℝ boxCover := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  refine ⟨?_, ?_⟩
  · have : (a • x + b • y) 0 = a * x 0 + b * y 0 := by simp
    rw [this]
    exact convex_Icc _ _ hx0 hy0 ha hb hab
  · have : (a • x + b • y) 1 = a * x 1 + b * y 1 := by simp
    rw [this]
    exact convex_Icc _ _ hx1 hy1 ha hb hab

lemma volume_boxCover : volume boxCover = ENNReal.ofReal (1/2) := by
  rw [boxCover, volume_box]
  rw [show (1/2 : ℝ) - -(1/2) = 1 by norm_num, show (1/4 : ℝ) - -(1/4) = 1/2 by norm_num]
  simp

/-- Two closed balls of radius `1/4` whose centres are symmetric about the
origin on the `x`-axis, at distance at most `1/2`, fit in the box. -/
lemma two_balls_subset_boxCover {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2) :
    Metric.closedBall (WithLp.toLp 2 ![-d/2, 0] : ℝ²) (1/4)
        ∪ Metric.closedBall (WithLp.toLp 2 ![d/2, 0] : ℝ²) (1/4) ⊆ boxCover := by
  have key : ∀ c : ℝ, |c| ≤ 1/4 →
      Metric.closedBall (WithLp.toLp 2 ![c, 0] : ℝ²) (1/4) ⊆ boxCover := by
    intro c hc z hz
    rw [Metric.mem_closedBall] at hz
    have h0 := Moser.CompactnessOutline.abs_sub_coord_le_dist z (WithLp.toLp 2 ![c, 0] : ℝ²) 0
    have h1 := Moser.CompactnessOutline.abs_sub_coord_le_dist z (WithLp.toLp 2 ![c, 0] : ℝ²) 1
    have e0 : (WithLp.toLp 2 ![c, 0] : ℝ²) 0 = c := by simp
    have e1 : (WithLp.toLp 2 ![c, 0] : ℝ²) 1 = 0 := by simp
    rw [e0] at h0
    rw [e1] at h1
    rw [abs_le] at h0 h1 hc
    exact ⟨⟨by linarith [h0.1, hc.1], by linarith [h0.2, hc.2]⟩,
      ⟨by linarith [h1.1], by linarith [h1.2]⟩⟩
  refine Set.union_subset (key _ ?_) (key _ ?_) <;>
    · rw [abs_le]; constructor <;> linarith

/-- A rotation followed by a translation carrying a pair of points to the
symmetric pair on the `x`-axis at the same distance. -/
lemma exists_isometry_normalizing_pair (P Q : ℝ²) :
    ∃ g : ℝ² → ℝ², IsOrientationPreservingIsometry g ∧
      g P = WithLp.toLp 2 ![-(dist P Q)/2, 0] ∧ g Q = WithLp.toLp 2 ![(dist P Q)/2, 0] := by
  haveI : Fact (Module.finrank ℝ ℝ² = 2) := ⟨finrank_euclideanSpace_fin⟩
  set o : Orientation ℝ ℝ² (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation with ho
  set d : ℝ := dist P Q with hd
  set y : ℝ² := WithLp.toLp 2 ![d, 0] with hy
  have hnormy : ‖y‖ = d := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    have e0 : (y : ℝ²) 0 = d := by rw [hy]; simp
    have e1 : (y : ℝ²) 1 = 0 := by rw [hy]; simp
    rw [e0, e1]
    simp only [Real.norm_eq_abs, sq_abs, abs_zero]
    rw [show d ^ 2 + (0:ℝ) ^ 2 = d ^ 2 by ring, Real.sqrt_sq dist_nonneg]
  have hnorm : ‖Q - P‖ = ‖y‖ := by rw [hnormy, hd, dist_eq_norm, norm_sub_rev]
  set r := o.rotation (o.oangle (Q - P) y) with hr
  have hrx : r (Q - P) = y := (o.rotation_oangle_eq_iff_norm_eq (Q - P) y).mpr hnorm
  refine ⟨fun z => r z + (WithLp.toLp 2 ![-d/2, 0] - r P),
    ⟨r, WithLp.toLp 2 ![-d/2, 0] - r P, o.linearEquiv_det_rotation _, rfl⟩, ?_, ?_⟩
  · show r P + (WithLp.toLp 2 ![-d/2, 0] - r P) = WithLp.toLp 2 ![-d/2, 0]
    abel
  show r Q + (WithLp.toLp 2 ![-d/2, 0] - r P) = WithLp.toLp 2 ![d/2, 0]
  have hstep : r Q + (WithLp.toLp 2 ![-d/2, 0] - r P)
      = r (Q - P) + WithLp.toLp 2 ![-d/2, 0] := by
    rw [map_sub]
    abel
  rw [hstep, hrx, hy]
  ext i
  fin_cases i <;> simp <;> ring

/-- **Every worm can be placed into two balls of radius `1/4`** whose centres are
symmetric about the origin on the `x`-axis at distance at most `1/2`: the two
quarter points of the worm are at distance at most `1/2` and every point of the
worm is within `1/4` of one of them. -/
lemma exists_placement_two_balls {s : Set ℝ²} (hs : s ∈ Worms) :
    ∃ (g : ℝ² → ℝ²) (d : ℝ), IsOrientationPreservingIsometry g ∧ 0 ≤ d ∧ d ≤ 1/2 ∧
      g '' s ⊆ Metric.closedBall (WithLp.toLp 2 ![-d/2, 0] : ℝ²) (1/4)
        ∪ Metric.closedBall (WithLp.toLp 2 ![d/2, 0] : ℝ²) (1/4) := by
  obtain ⟨f, hlip, rfl⟩ := hs
  set q1 : Set.Icc (0 : ℝ) 1 := ⟨1/4, by constructor <;> norm_num⟩ with hq1
  set q3 : Set.Icc (0 : ℝ) 1 := ⟨3/4, by constructor <;> norm_num⟩ with hq3
  have hq1v : (q1 : ℝ) = 1/4 := rfl
  have hq3v : (q3 : ℝ) = 3/4 := rfl
  have hPQ : dist (f q1) (f q3) ≤ 1/2 := by
    refine le_trans (by simpa using hlip.dist_le_mul q1 q3) ?_
    rw [Subtype.dist_eq, Real.dist_eq, hq1v, hq3v]
    rw [show (1/4 : ℝ) - 3/4 = -(1/2) by norm_num, abs_neg,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  obtain ⟨g, hgop, hgP, hgQ⟩ := exists_isometry_normalizing_pair (f q1) (f q3)
  refine ⟨g, dist (f q1) (f q3), hgop, dist_nonneg, hPQ, ?_⟩
  have hiso : Isometry g := hgop.isometry
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  have hcase : dist (f x) (f q1) ≤ 1/4 ∨ dist (f x) (f q3) ≤ 1/4 := by
    obtain ⟨hx0, hx1⟩ := x.2
    rcases le_total (x : ℝ) (1/2) with hx | hx
    · left
      refine le_trans (by simpa using hlip.dist_le_mul x q1) ?_
      rw [Subtype.dist_eq, Real.dist_eq, hq1v, abs_le]
      constructor <;> linarith
    · right
      refine le_trans (by simpa using hlip.dist_le_mul x q3) ?_
      rw [Subtype.dist_eq, Real.dist_eq, hq3v, abs_le]
      constructor <;> linarith
  rcases hcase with hc | hc
  · left
    rw [Metric.mem_closedBall, ← hgP, hiso.dist_eq]
    exact hc
  · right
    rw [Metric.mem_closedBall, ← hgQ, hiso.dist_eq]
    exact hc

/-- Every worm can be placed inside the `1 × 1/2` box. -/
lemma exists_placement_into_boxCover {s : Set ℝ²} (hs : s ∈ Worms) :
    ∃ g : ℝ² → ℝ², IsOrientationPreservingIsometry g ∧ g '' s ⊆ boxCover := by
  obtain ⟨g, d, hgop, hd0, hd, hsub⟩ := exists_placement_two_balls hs
  exact ⟨g, hgop, hsub.trans (two_balls_subset_boxCover hd0 hd)⟩

/-- **An upper bound for the Moser cover number**: `M ≤ 1/2`.
Compare the disc bound `M ≤ π/4 ≈ 0.785` of `moserCoverNumber_le_pi_div_four`. -/
theorem moserCoverNumber_le_half : moserCoverNumber ≤ ENNReal.ofReal (1/2) := by
  have h : ∀ s ∈ Worms, ∃ g : ℝ² → ℝ², IsOrientationPreservingIsometry g ∧ g '' s ⊆ boxCover :=
    fun _ hs => exists_placement_into_boxCover hs
  choose! g hgop hgsub using h
  have hPC : IsPlacementCover Worms boxCover :=
    ⟨g, fun s hs => hgop s hs,
      convexHull_min (Set.iUnion₂_subset fun s hs => hgsub s hs) convex_boxCover⟩
  rw [moserCoverNumber, minimalCoverArea, minimalVolume, ← volume_boxCover]
  exact sInf_le ⟨boxCover, hPC, rfl⟩

/-! ## Sharpening the upper bound: the stadium

The two balls of radius `1/4` that hold a worm have centres at distance at most
`1/2`, so they fit in the *stadium*: the set of points within `1/4` of the
segment from `(-1/4,0)` to `(1/4,0)`. Its area is `1/4 + π/16 ≈ 0.4464`, better
than the `1/2` of the box.
-/

/-- The stadium: points within `1/4` of the segment from `(-1/4,0)` to `(1/4,0)`. -/
def stadiumCover : Set ℝ² :=
  {z : ℝ² | ∃ s ∈ Set.Icc (-(1/4) : ℝ) (1/4), dist z (WithLp.toLp 2 ![s, 0]) ≤ 1/4}

lemma convex_stadiumCover : Convex ℝ stadiumCover := by
  rintro x ⟨s, hs, hxs⟩ y ⟨t, ht, hyt⟩ a b ha hb hab
  refine ⟨a * s + b * t, convex_Icc _ _ hs ht ha hb hab, ?_⟩
  have hcomb : (WithLp.toLp 2 ![a * s + b * t, 0] : ℝ²)
      = a • (WithLp.toLp 2 ![s, 0] : ℝ²) + b • (WithLp.toLp 2 ![t, 0] : ℝ²) := by
    ext i
    fin_cases i <;> simp
  rw [dist_eq_norm, hcomb,
    show a • x + b • y - (a • (WithLp.toLp 2 ![s, 0] : ℝ²) + b • (WithLp.toLp 2 ![t, 0] : ℝ²))
      = a • (x - WithLp.toLp 2 ![s, 0]) + b • (y - WithLp.toLp 2 ![t, 0]) by module]
  calc ‖a • (x - (WithLp.toLp 2 ![s, 0] : ℝ²)) + b • (y - (WithLp.toLp 2 ![t, 0] : ℝ²))‖
      ≤ a * ‖x - (WithLp.toLp 2 ![s, 0] : ℝ²)‖ + b * ‖y - (WithLp.toLp 2 ![t, 0] : ℝ²)‖ := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
          abs_of_nonneg hb]
    _ ≤ a * (1/4) + b * (1/4) := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact add_le_add (mul_le_mul_of_nonneg_left hxs ha) (mul_le_mul_of_nonneg_left hyt hb)
    _ = 1/4 := by rw [← add_mul, hab, one_mul]

lemma two_balls_subset_stadiumCover {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2) :
    Metric.closedBall (WithLp.toLp 2 ![-d/2, 0] : ℝ²) (1/4)
        ∪ Metric.closedBall (WithLp.toLp 2 ![d/2, 0] : ℝ²) (1/4) ⊆ stadiumCover := by
  rintro z (hz | hz) <;> rw [Metric.mem_closedBall] at hz
  · exact ⟨-d/2, ⟨by linarith, by linarith⟩, hz⟩
  · exact ⟨d/2, ⟨by linarith, by linarith⟩, hz⟩

/-- Every worm can be placed inside the stadium. -/
lemma exists_placement_into_stadiumCover {s : Set ℝ²} (hs : s ∈ Worms) :
    ∃ g : ℝ² → ℝ², IsOrientationPreservingIsometry g ∧ g '' s ⊆ stadiumCover := by
  obtain ⟨g, d, hgop, hd0, hd, hsub⟩ := exists_placement_two_balls hs
  exact ⟨g, hgop, hsub.trans (two_balls_subset_stadiumCover hd0 hd)⟩

/-- The coordinate half-plane is closed. -/
lemma isClosed_coord_le (c : ℝ) : IsClosed {z : ℝ² | z 0 ≤ c} := by
  have hcont : Continuous fun z : ℝ² => z 0 := by fun_prop
  exact isClosed_le hcont continuous_const

lemma isClosed_le_coord (c : ℝ) : IsClosed {z : ℝ² | c ≤ z 0} := by
  have hcont : Continuous fun z : ℝ² => z 0 := by fun_prop
  exact isClosed_le continuous_const hcont

/-- The vertical axis is a null set. -/
lemma volume_axis : volume {z : ℝ² | z 0 = 0} = 0 := by
  have hd : (WithLp.toLp 2 ![0, 1] : ℝ²) ≠ 0 := by
    intro hcon
    have := congrFun (congrArg WithLp.ofLp hcon) 1
    simp at this
  have hset : {z : ℝ² | z 0 = 0}
      = {y : ℝ² | ConvexPolygon.rcross (WithLp.toLp 2 ![0, 1] : ℝ²) (y - 0) = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, ConvexPolygon.rcross_def, sub_zero]
    constructor
    · intro h; simp [h]
    · intro h; simpa using h
  rw [hset]
  exact ConvexPolygon.volume_line 0 _ hd

/-- Half of the disc of radius `1/4` has area `π/32`. -/
lemma volume_halfDisc :
    volume (Metric.closedBall (0 : ℝ²) (1/4) ∩ {z : ℝ² | z 0 ≤ 0})
      = ENNReal.ofReal (Real.pi / 32) := by
  set D : Set ℝ² := Metric.closedBall (0 : ℝ²) (1/4) with hD
  set Hm : Set ℝ² := D ∩ {z : ℝ² | z 0 ≤ 0} with hHm
  set Hp : Set ℝ² := D ∩ {z : ℝ² | 0 ≤ z 0} with hHp
  have hvolD : volume D = ENNReal.ofReal (Real.pi / 16) := by
    rw [hD, EuclideanSpace.volume_closedBall]
    have hcard : Fintype.card (Fin 2) = 2 := by simp
    rw [hcard, show ((2 : ℕ) : ℝ) / 2 + 1 = 2 by norm_num, Real.Gamma_two,
      Real.sq_sqrt Real.pi_nonneg, div_one, ← ENNReal.ofReal_pow (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hneg : -Hm = Hp := by
    ext z
    simp only [Set.mem_neg, hHm, hHp, hD, Set.mem_inter_iff, Metric.mem_closedBall,
      dist_zero_right, norm_neg, Set.mem_setOf_eq, PiLp.neg_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  have hvolneg : volume Hp = volume Hm := by
    rw [← hneg]
    exact MeasureTheory.Measure.measure_neg volume Hm
  have hunion : Hm ∪ Hp = D := by
    ext z
    simp only [hHm, hHp, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases le_total (z 0) 0 with hz | hz
      · exact Or.inl ⟨h, hz⟩
      · exact Or.inr ⟨h, hz⟩
  have hinter : volume (Hm ∩ Hp) = 0 := by
    refine measure_mono_null (fun z hz => ?_) volume_axis
    obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := hz
    exact le_antisymm h1 h2
  have hmeasp : MeasurableSet Hp :=
    (Metric.isClosed_closedBall.inter (isClosed_le_coord 0)).measurableSet
  have hkey := measure_union_add_inter (μ := volume) Hm hmeasp
  rw [hunion, hinter, add_zero, hvolneg, hvolD] at hkey
  have hfin : volume Hm ≠ ⊤ := by
    have hle : volume Hm ≤ volume D := measure_mono Set.inter_subset_left
    rw [hvolD] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hsum : volume Hm + volume Hm = ENNReal.ofReal (Real.pi / 16) := hkey.symm
  have htoReal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hfin hfin, ENNReal.toReal_ofReal (by positivity)] at htoReal
  have hval : (volume Hm).toReal = Real.pi / 32 := by linarith
  rw [← ENNReal.ofReal_toReal hfin, hval]

/-- The other half of the disc of radius `1/4` also has area `π/32`. -/
lemma volume_halfDisc' :
    volume (Metric.closedBall (0 : ℝ²) (1/4) ∩ {z : ℝ² | 0 ≤ z 0})
      = ENNReal.ofReal (Real.pi / 32) := by
  have hneg : -(Metric.closedBall (0 : ℝ²) (1/4) ∩ {z : ℝ² | z 0 ≤ 0})
      = Metric.closedBall (0 : ℝ²) (1/4) ∩ {z : ℝ² | 0 ≤ z 0} := by
    ext z
    simp only [Set.mem_neg, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right, norm_neg,
      Set.mem_setOf_eq, PiLp.neg_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  rw [← hneg, MeasureTheory.Measure.measure_neg, volume_halfDisc]

/-- Comparing distances to two points of the `x`-axis. -/
lemma dist_toLp_le_of_abs_le {z : ℝ²} {c c' : ℝ} (h : |z 0 - c| ≤ |z 0 - c'|) :
    dist z (WithLp.toLp 2 ![c, 0] : ℝ²) ≤ dist z (WithLp.toLp 2 ![c', 0] : ℝ²) := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  refine Real.sqrt_le_sqrt ?_
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have e0 : (WithLp.toLp 2 ![c, 0] : ℝ²) 0 = c := by simp
  have e0' : (WithLp.toLp 2 ![c', 0] : ℝ²) 0 = c' := by simp
  have e1 : (WithLp.toLp 2 ![c, 0] : ℝ²) 1 = 0 := by simp
  have e1' : (WithLp.toLp 2 ![c', 0] : ℝ²) 1 = 0 := by simp
  rw [show (WithLp.ofLp z) 0 = z 0 from rfl, show (WithLp.ofLp z) 1 = z 1 from rfl]
  simp only [e0, e0', e1, e1', Real.dist_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  have key := mul_self_le_mul_self (abs_nonneg (z 0 - c)) h
  nlinarith [key]

/-- **The stadium has area at most `1/4 + π/16 ≈ 0.4464`.** -/
lemma volume_stadiumCover_le :
    volume stadiumCover ≤ ENNReal.ofReal (1/4 + Real.pi/16) := by
  set A : ℝ² := WithLp.toLp 2 ![-(1/4), 0] with hA
  set B : ℝ² := WithLp.toLp 2 ![(1/4 : ℝ), 0] with hB
  set Box : Set ℝ² :=
    {z : ℝ² | z 0 ∈ Set.Icc (-(1/4) : ℝ) (1/4) ∧ z 1 ∈ Set.Icc (-(1/4) : ℝ) (1/4)} with hBox
  set L : Set ℝ² := Metric.closedBall A (1/4) ∩ {z : ℝ² | z 0 ≤ -(1/4)} with hL
  set R : Set ℝ² := Metric.closedBall B (1/4) ∩ {z : ℝ² | (1/4 : ℝ) ≤ z 0} with hR
  have hA0 : A 0 = -(1/4) := by rw [hA]; simp
  have hB0 : B 0 = 1/4 := by rw [hB]; simp
  -- the stadium is covered by the middle square and the two end half-discs
  have hsub : stadiumCover ⊆ Box ∪ L ∪ R := by
    rintro z ⟨s, ⟨hs1, hs2⟩, hdist⟩
    have hz1 : |z 1| ≤ 1/4 := by
      have h1 := Moser.CompactnessOutline.abs_sub_coord_le_dist z
        (WithLp.toLp 2 ![s, 0] : ℝ²) 1
      have e1 : (WithLp.toLp 2 ![s, 0] : ℝ²) 1 = 0 := by simp
      rw [e1, sub_zero] at h1
      linarith
    rw [abs_le] at hz1
    rcases lt_trichotomy (z 0) (-(1/4)) with hz | hz | hz
    · refine Or.inl (Or.inr ⟨?_, by simp only [Set.mem_setOf_eq]; linarith⟩)
      rw [Metric.mem_closedBall, hA]
      refine le_trans (dist_toLp_le_of_abs_le ?_) hdist
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · exact Or.inl (Or.inl ⟨⟨by linarith, by linarith⟩, ⟨hz1.1, hz1.2⟩⟩)
    · rcases le_total (z 0) (1/4) with hz' | hz'
      · exact Or.inl (Or.inl ⟨⟨by linarith, hz'⟩, ⟨hz1.1, hz1.2⟩⟩)
      · refine Or.inr ⟨?_, by simp only [Set.mem_setOf_eq]; linarith⟩
        rw [Metric.mem_closedBall, hB]
        refine le_trans (dist_toLp_le_of_abs_le ?_) hdist
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
  -- the three pieces, measured
  have hvolBox : volume Box = ENNReal.ofReal (1/4) := by
    rw [hBox, volume_box, show (1/4 : ℝ) - -(1/4) = 1/2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have htrans : ∀ (C : ℝ²) (S : Set ℝ²), NullMeasurableSet S volume →
      volume ((fun z : ℝ² => z - C) ⁻¹' S) = volume S := by
    intro C S hS
    exact (measurePreserving_of_isOrientationPreservingIsometry
      (Moser.CompactnessOutline.isOrientationPreservingIsometry_sub C)).measure_preimage hS
  have hmeasHm : NullMeasurableSet
      (Metric.closedBall (0 : ℝ²) (1/4) ∩ {z : ℝ² | z 0 ≤ 0}) volume :=
    ((Metric.isClosed_closedBall.inter (isClosed_coord_le 0)).measurableSet).nullMeasurableSet
  have hmeasHp : NullMeasurableSet
      (Metric.closedBall (0 : ℝ²) (1/4) ∩ {z : ℝ² | 0 ≤ z 0}) volume :=
    ((Metric.isClosed_closedBall.inter (isClosed_le_coord 0)).measurableSet).nullMeasurableSet
  have hvolL : volume L = ENNReal.ofReal (Real.pi / 32) := by
    have hpre : L = (fun z : ℝ² => z - A) ⁻¹'
        (Metric.closedBall (0 : ℝ²) (1/4) ∩ {z : ℝ² | z 0 ≤ 0}) := by
      ext z
      simp only [hL, Set.mem_inter_iff, Set.mem_preimage, Metric.mem_closedBall,
        dist_zero_right, Set.mem_setOf_eq, PiLp.sub_apply, hA0, ← dist_eq_norm]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    rw [hpre, htrans A _ hmeasHm, volume_halfDisc]
  have hvolR : volume R = ENNReal.ofReal (Real.pi / 32) := by
    have hpre : R = (fun z : ℝ² => z - B) ⁻¹'
        (Metric.closedBall (0 : ℝ²) (1/4) ∩ {z : ℝ² | 0 ≤ z 0}) := by
      ext z
      simp only [hR, Set.mem_inter_iff, Set.mem_preimage, Metric.mem_closedBall,
        dist_zero_right, Set.mem_setOf_eq, PiLp.sub_apply, hB0, ← dist_eq_norm]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    rw [hpre, htrans B _ hmeasHp, volume_halfDisc']
  calc volume stadiumCover
      ≤ volume (Box ∪ L ∪ R) := measure_mono hsub
    _ ≤ volume (Box ∪ L) + volume R := measure_union_le _ _
    _ ≤ volume Box + volume L + volume R := add_le_add (measure_union_le _ _) le_rfl
    _ = ENNReal.ofReal (1/4 + Real.pi/16) := by
        rw [hvolBox, hvolL, hvolR, ← ENNReal.ofReal_add (by norm_num) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The sharpened upper bound**: `M ≤ 1/4 + π/16 ≈ 0.4464`. -/
theorem moserCoverNumber_le_stadium :
    moserCoverNumber ≤ ENNReal.ofReal (1/4 + Real.pi/16) := by
  have h : ∀ s ∈ Worms, ∃ g : ℝ² → ℝ², IsOrientationPreservingIsometry g ∧
      g '' s ⊆ stadiumCover := fun _ hs => exists_placement_into_stadiumCover hs
  choose! g hgop hgsub using h
  have hPC : IsPlacementCover Worms stadiumCover :=
    ⟨g, fun s hs => hgop s hs,
      convexHull_min (Set.iUnion₂_subset fun s hs => hgsub s hs) convex_stadiumCover⟩
  refine le_trans ?_ volume_stadiumCover_le
  rw [moserCoverNumber, minimalCoverArea, minimalVolume]
  exact sInf_le ⟨stadiumCover, hPC, rfl⟩

/-! ## A `native_decide`-free lower bound

The bound above uses `native_decide` for the well-formedness and the shoelace
area of the explicit hexagon (as elsewhere in the development). The weaker bound
`M ≥ 1/8` below is checked entirely by the kernel: it uses the V worm, whose
hull is a triangle, and the integration-free triangle-area lemma
`ConvexPolygon.volume_triangle`.
-/

theorem oneEighth_le_moserCoverNumber : ENNReal.ofReal ((1 : ℝ)/8) ≤ moserCoverNumber := by
  set P0 : ℝ² := vPath 0 with hP0
  set P1 : ℝ² := vPath (1/2) with hP1
  set P2 : ℝ² := vPath 1 with hP2
  set T : Set ℝ² := convexHull ℝ ({P0, P1, P2} : Set ℝ²) with hT
  have hvolT : volume T = ENNReal.ofReal ((1 : ℝ)/8) := by
    rw [hT, ConvexPolygon.volume_triangle]
    have h0 : P0 0 = 0 := by rw [hP0, vPath_apply_zero]; norm_num
    have h0' : P0 1 = 0 := by rw [hP0, vPath_apply_one]; norm_num
    have h1 : P1 0 = 1/2 := by rw [hP1, vPath_apply_zero]; norm_num
    have h1' : P1 1 = 0 := by rw [hP1, vPath_apply_one]; norm_num
    have h2 : P2 0 = 1/2 := by rw [hP2, vPath_apply_zero]; norm_num
    have h2' : P2 1 = 1/2 := by rw [hP2, vPath_apply_one]; norm_num
    have hval : ConvexPolygon.rcross (P1 - P0) (P2 - P0) = 1/4 := by
      simp only [ConvexPolygon.rcross_def, PiLp.sub_apply, h0, h0', h1, h1', h2, h2']
      ring
    rw [hval, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]
    congr 1
    norm_num
  have hmeasT : MeasurableSet T :=
    (Set.Finite.isCompact_convexHull ℝ
      (((Set.finite_singleton P2).insert P1).insert P0)).isClosed.measurableSet
  have hmemV : ∀ u : ℝ, u ∈ Set.Icc (0:ℝ) 1 → vPath u ∈ vWorm := fun u hu => ⟨⟨u, hu⟩, rfl⟩
  rw [moserCoverNumber, minimalCoverArea, minimalVolume]
  refine le_sInf ?_
  rintro v ⟨X, ⟨g, hgop, hsub⟩, rfl⟩
  have hGop : IsOrientationPreservingIsometry (g vWorm) := hgop vWorm vWorm_mem_worms
  have hplaced : (g vWorm) '' T ⊆ X := by
    have hhull : convexHull ℝ ((g vWorm) '' vWorm) ⊆ X :=
      (convexHull_mono (Set.subset_biUnion_of_mem (u := fun s => g s '' s)
        vWorm_mem_worms)).trans hsub
    refine subset_trans (image_convexHull_subset hGop _) (subset_trans ?_ hhull)
    refine convexHull_mono ?_
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨_, hmemV 0 ⟨le_rfl, zero_le_one⟩, rfl⟩
    · exact ⟨_, hmemV (1/2) ⟨by norm_num, by norm_num⟩, rfl⟩
    · exact ⟨_, hmemV 1 ⟨zero_le_one, le_rfl⟩, rfl⟩
  calc ENNReal.ofReal ((1 : ℝ)/8) = volume T := hvolT.symm
    _ = volume ((g vWorm) '' T) :=
        (volume_image_of_isOrientationPreservingIsometry hGop hmeasT).symm
    _ ≤ volume X := measure_mono hplaced

/-! ## Summary -/

/-- **Two-sided unconditional bounds on the Moser cover number.** -/
theorem moserCoverNumber_bounds :
    ENNReal.ofReal ((3233 : ℝ) / 20808) ≤ moserCoverNumber ∧
      moserCoverNumber ≤ ENNReal.ofReal (1/4 + Real.pi/16) :=
  ⟨hexWormArea_le_moserCoverNumber, moserCoverNumber_le_stadium⟩

lemma moserCoverNumber_ne_top : moserCoverNumber ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top moserCoverNumber_le_stadium

/-- **The bounds in decimal form**: `0.15537 ≤ M ≤ 0.44635`. -/
theorem moserCoverNumber_toReal_bounds :
    0.15537 ≤ moserCoverNumber.toReal ∧ moserCoverNumber.toReal ≤ 0.44635 := by
  constructor
  · have h := ENNReal.toReal_mono moserCoverNumber_ne_top hexWormArea_le_moserCoverNumber
    rw [ENNReal.toReal_ofReal (by norm_num)] at h
    linarith [h]
  · have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top moserCoverNumber_le_stadium
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
    linarith

end Moser

end
