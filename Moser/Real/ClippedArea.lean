module

public import Mathlib
public import Moser.LowerBound
public import Moser.Geometry.AllowableAdditions

public section

/-!
# The clipped area is a lower bound

`ConvexPolygon.areaWeaklyRightOfVertexPair` computes, by Sutherland–Hodgman
clipping, the area of the part of a polygon lying weakly right of a directed
line through two of its vertices. This file proves the half of its specification
that the allowable-additions bound needs: the computed value never *exceeds* the
true area.

No correctness proof for the clipping algorithm is required. Every point the
clipping emits is visibly a point of the polygon lying weakly right of the line —
either a vertex that passed the side test, or a point of an edge that crosses the
line — and the area is measured through the run-time-verified hull
`ConvexPolygon.ofListChecked`, whose region is exactly the hull of those points.
-/

open MeasureTheory

namespace Moser

open ConvexPolygon

/-- The real Euclidean plane `ℝ²`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Casting the rational plane into the real plane -/

lemma toEuclidean_affine (a b : Point ℚ) (l : ℚ) :
    Point.toEuclidean (a + l • (b - a))
      = Point.toEuclidean a + (l : ℝ) • (Point.toEuclidean b - Point.toEuclidean a) := by
  ext i
  fin_cases i <;>
    · simp only [toEuclidean_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
      push_cast
      ring

lemma rcross_toEuclidean (u v w : Point ℚ) :
    rcross (Point.toEuclidean v - Point.toEuclidean u) (Point.toEuclidean w - Point.toEuclidean u)
      = ((Point.crossProduct (v - u) (w - u) : ℚ) : ℝ) := by
  simp only [rcross_def, PiLp.sub_apply, toEuclidean_apply, Point.crossProduct, Pi.sub_apply]
  push_cast
  ring

/-! ## Convexity of a closed half-plane -/

lemma convex_rcross_nonpos (d w : ℝ²) : Convex ℝ {z : ℝ² | rcross d (z - w) ≤ 0} := by
  intro x hx y hy s t hs ht hst
  have hexp : rcross d (s • x + t • y - w) = s * rcross d (x - w) + t * rcross d (y - w) := by
    have ht1 : t = 1 - s := by linarith
    subst ht1
    simp only [rcross_def, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [hexp]
  nlinarith [hx, hy, hs, ht]

/-! ## The clipped points lie in the polygon, weakly right of the line -/

/-- A vertex of a polygon casts into its real region. -/
lemma toEuclidean_mem_realHull_of_mem_vertex_list {poly : ConvexPolygon ℚ} {v : Point ℚ}
    (hv : v ∈ poly.vertex_list) : Point.toEuclidean v ∈ poly.realHull := by
  rw [ConvexPolygon.vertex_list, List.mem_map] at hv
  obtain ⟨k, -, rfl⟩ := hv
  rw [ConvexPolygon.realHull_eq]
  exact subset_convexHull ℝ _
    (show Point.toEuclidean (poly.vertices k)
      ∈ Set.range (fun i => Point.toEuclidean (poly.vertices i)) from ⟨k, rfl⟩)

/-- Every point emitted by the clipping lies in the real region of the polygon and
weakly right of the clipping line. -/
lemma mem_realHull_inter_of_mem_rightClippedChain {poly : ConvexPolygon ℚ}
    {i j : Fin poly.vertex_count} {z : Point ℚ} (hz : z ∈ rightClippedChain poly i j) :
    Point.toEuclidean z ∈ poly.realHull ∩
      {y : ℝ² | rcross (Point.toEuclidean (poly.vertices j) - Point.toEuclidean (poly.vertices i))
        (y - Point.toEuclidean (poly.vertices i)) ≤ 0} := by
  have hside : ∀ w : Point ℚ, sideOfVertexPair poly i j w ≤ 0 →
      rcross (Point.toEuclidean (poly.vertices j) - Point.toEuclidean (poly.vertices i))
        (Point.toEuclidean w - Point.toEuclidean (poly.vertices i)) ≤ 0 := by
    intro w hw
    rw [rcross_toEuclidean]
    rw [sideOfVertexPair_eq] at hw
    exact_mod_cast hw
  rcases mem_rightClippedChain_cases hz with ⟨hmem, hs⟩ | ⟨a, ha, b, hb, l, hl0, hl1, rfl, hs⟩
  · exact ⟨toEuclidean_mem_realHull_of_mem_vertex_list hmem, hside _ hs⟩
  · refine ⟨?_, hside _ hs⟩
    rw [toEuclidean_affine]
    have hA := toEuclidean_mem_realHull_of_mem_vertex_list ha
    have hB := toEuclidean_mem_realHull_of_mem_vertex_list hb
    have hcomb : Point.toEuclidean a + (l : ℝ) • (Point.toEuclidean b - Point.toEuclidean a)
        = (1 - (l : ℝ)) • Point.toEuclidean a + (l : ℝ) • Point.toEuclidean b := by
      module
    rw [hcomb]
    refine poly.convex_realHull hA hB (by
      have : (l : ℝ) ≤ 1 := by exact_mod_cast hl1
      linarith) (by exact_mod_cast hl0) (by ring)

/-! ## The clipped area is a lower bound -/

/-- **The computed clipped area never exceeds the true area.**
`areaWeaklyRightOfVertexPair` is a lower bound for the area of the part of the
polygon lying weakly right of the directed line `V_i → V_j`. -/
theorem areaWeaklyRightOfVertexPair_le (poly : ConvexPolygon ℚ) (i j : Fin poly.vertex_count)
    (hij : i ≠ j) :
    ENNReal.ofReal ((areaWeaklyRightOfVertexPair poly i j hij : ℚ) : ℝ)
      ≤ volume (poly.realHull ∩
          {y : ℝ² | rcross (Point.toEuclidean (poly.vertices j)
            - Point.toEuclidean (poly.vertices i))
              (y - Point.toEuclidean (poly.vertices i)) ≤ 0}) := by
  rcases hcase : ConvexPolygon.ofListChecked (rightClippedChain poly i j) with _ | q
  · rw [areaWeaklyRightOfVertexPair_of_none hij hcase]
    simp
  · rw [areaWeaklyRightOfVertexPair_of_some hij hcase, ← ConvexPolygon.volume_realHull q]
    refine measure_mono ?_
    rw [ConvexPolygon.realHull_eq]
    refine convexHull_min ?_ ((poly.convex_realHull).inter (convex_rcross_nonpos _ _))
    rintro _ ⟨k, rfl⟩
    exact mem_realHull_inter_of_mem_rightClippedChain
      (ConvexPolygon.vertices_mem_of_ofList (ConvexPolygon.ofListChecked_eq_some hcase).1 k)

/-! ## Two regions separated by a line -/

/-- Two convex subsets of `S` lying on opposite sides of a line contribute their
volumes additively to `S`: they meet only inside the line, which is null. -/
lemma volume_add_le_of_separated {S A B : Set ℝ²} {d w : ℝ²} (hd : d ≠ 0)
    (hBconv : Convex ℝ B) (hAS : A ⊆ S) (hBS : B ⊆ S)
    (hA : A ⊆ {z : ℝ² | rcross d (z - w) ≤ 0}) (hB : B ⊆ {z : ℝ² | 0 ≤ rcross d (z - w)}) :
    volume A + volume B ≤ volume S := by
  have hdisj : MeasureTheory.AEDisjoint volume A B := by
    refine measure_mono_null (fun z hz => ?_) (volume_line w d hd)
    obtain ⟨h1, h2⟩ := hz
    have e1 := hA h1
    have e2 := hB h2
    simp only [Set.mem_setOf_eq] at e1 e2 ⊢
    linarith
  calc volume A + volume B
      = volume (A ∪ B) := (measure_union₀ (hBconv.nullMeasurableSet (μ := volume)) hdisj).symm
    _ ≤ volume S := measure_mono (Set.union_subset hAS hBS)

/-! ## A point outside a growth half-space exceeds the threshold -/

/-- Casting the rational plane into the real plane is injective. -/
lemma toEuclidean_injective : Function.Injective Point.toEuclidean := by
  intro a b hab
  funext k
  have : Point.toEuclidean a k = Point.toEuclidean b k := by rw [hab]
  rw [toEuclidean_apply, toEuclidean_apply] at this
  exact Rat.cast_injective this

/-- **Threshold violated outside a growth half-space.**
If `p` lies strictly outside the growth half-space of the ordered vertex pair
`(V_i, V_j)`, then the area of the verified convex hull of `P ∪ {p}` strictly
exceeds the threshold: beyond the part of `P` weakly right of the line
`V_i → V_j` (of area at least `areaWeaklyRightOfVertexPair`) the hull also
contains the triangle `V_i V_j p`, whose area exceeds the remaining excess. -/
theorem areaThreshold_lt_area_of_outside_growthHalfspace {poly : ConvexPolygon ℚ} {threshold : ℚ}
    {i j : Fin poly.vertex_count} (hij : i ≠ j) {p : Point ℚ}
    (hp : (ConvexPolygon.growthHalfspace poly threshold i j hij).contains p = false)
    {hull : ConvexPolygon ℚ}
    (hhull : ConvexPolygon.ofListChecked (p :: poly.vertex_list) = some hull) :
    threshold < hull.area := by
  set AR : ℚ := ConvexPolygon.areaWeaklyRightOfVertexPair poly i j hij with hARdef
  set e : ℚ := max 0 (threshold - AR) with hedef
  set cr : ℚ := Point.crossProduct (poly.vertices j - poly.vertices i) (p - poly.vertices i)
    with hcrdef
  -- the half-space test, in closed form
  have hcross : 2 * e < cr := by
    by_contra hcon
    push Not at hcon
    rw [Bool.eq_false_iff] at hp
    exact hp ((ConvexPolygon.contains_growthHalfspace_iff poly threshold i j hij p).mpr hcon)
  have he0 : 0 ≤ e := le_max_left _ _
  have hcr0 : 0 < cr := by linarith
  -- the real region of the verified hull
  have hreal := ConvexPolygon.realHull_ofListChecked hhull
  set S : Set ℝ² := hull.realHull with hSdef
  have hSconv : Convex ℝ S := hull.convex_realHull
  have hmem : ∀ q : Point ℚ, q ∈ p :: poly.vertex_list → Point.toEuclidean q ∈ S := by
    intro q hq
    rw [hreal]
    exact subset_convexHull ℝ _ ⟨q, hq, rfl⟩
  have hvi : Point.toEuclidean (poly.vertices i) ∈ S :=
    hmem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  have hvj : Point.toEuclidean (poly.vertices j) ∈ S :=
    hmem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩))
  have hpS : Point.toEuclidean p ∈ S := hmem _ (List.mem_cons_self ..)
  -- the polygon's own region sits inside the hull
  have hpolyS : poly.realHull ⊆ S := by
    rw [ConvexPolygon.realHull_eq]
    refine convexHull_min ?_ hSconv
    rintro _ ⟨k, rfl⟩
    exact hmem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩))
  -- the separating line
  set d : ℝ² := Point.toEuclidean (poly.vertices j) - Point.toEuclidean (poly.vertices i) with hddef
  have hd : d ≠ 0 := by
    rw [hddef, sub_ne_zero]
    intro hcon
    exact hij (poly.nodup (toEuclidean_injective hcon)).symm
  set w : ℝ² := Point.toEuclidean (poly.vertices i) with hwdef
  set A : Set ℝ² := poly.realHull ∩ {z : ℝ² | rcross d (z - w) ≤ 0} with hAdef
  set B : Set ℝ² := convexHull ℝ ({w, Point.toEuclidean (poly.vertices j),
    Point.toEuclidean p} : Set ℝ²) with hBdef
  have hBsub : B ⊆ S := convexHull_min (by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    exacts [hvi, hvj, hpS]) hSconv
  have hBside : B ⊆ {z : ℝ² | 0 ≤ rcross d (z - w)} := by
    refine convexHull_subset_halfplane d w ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · rw [sub_self, rcross_zero_right]
    · rw [hddef, hwdef, rcross_toEuclidean]
      have : Point.crossProduct (poly.vertices j - poly.vertices i)
          (poly.vertices j - poly.vertices i) = 0 := by
        simp only [Point.crossProduct]; ring
      rw [this]
      norm_num
    · rw [hddef, hwdef, rcross_toEuclidean, ← hcrdef]
      exact_mod_cast hcr0.le
  -- additivity of the two pieces
  have hadd : volume A + volume B ≤ volume S :=
    volume_add_le_of_separated hd (convex_convexHull ℝ _) (fun z hz => hpolyS hz.1) hBsub
      (fun _ hz => hz.2) hBside
  -- the two pieces, measured
  have hAvol : ENNReal.ofReal ((AR : ℚ) : ℝ) ≤ volume A := by
    rw [hARdef, hAdef, hddef, hwdef]
    exact areaWeaklyRightOfVertexPair_le poly i j hij
  have hBvol : volume B = ENNReal.ofReal (((cr : ℚ) : ℝ) / 2) := by
    rw [hBdef, hwdef, volume_triangle, ← hddef]
    congr 1
    rw [hddef, hwdef, rcross_toEuclidean, ← hcrdef,
      abs_of_nonneg (by exact_mod_cast hcr0.le : (0:ℝ) ≤ ((cr : ℚ) : ℝ))]
  -- put the pieces together
  have hkey : ENNReal.ofReal (((AR : ℚ) : ℝ) + ((cr : ℚ) : ℝ) / 2) ≤ volume S := by
    refine le_trans (ENNReal.ofReal_add_le) ?_
    rw [← hBvol]
    exact le_trans (add_le_add hAvol le_rfl) hadd
  rw [ConvexPolygon.volume_realHull hull] at hkey
  have harea_pos : (0 : ℝ) < ((hull.area : ℚ) : ℝ) := by
    have h1 : ENNReal.ofReal (((cr : ℚ) : ℝ) / 2) ≤ volume S := by
      rw [← hBvol]; exact measure_mono hBsub
    rw [ConvexPolygon.volume_realHull hull] at h1
    have h2 : 0 < ENNReal.ofReal (((cr : ℚ) : ℝ) / 2) := by
      rw [ENNReal.ofReal_pos]
      have hc : (0 : ℝ) < ((cr : ℚ) : ℝ) := by exact_mod_cast hcr0
      linarith
    exact ENNReal.ofReal_pos.mp (lt_of_lt_of_le h2 h1)
  have hfinal : ((AR : ℚ) : ℝ) + ((cr : ℚ) : ℝ) / 2 ≤ ((hull.area : ℚ) : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff harea_pos.le).mp hkey
  have hthr : ((threshold : ℚ) : ℝ) ≤ ((AR : ℚ) : ℝ) + ((e : ℚ) : ℝ) := by
    have hle : threshold ≤ AR + e := by
      have hmax := le_max_right (0 : ℚ) (threshold - AR)
      rw [← hedef] at hmax
      linarith
    exact_mod_cast hle
  have hcr2 : ((e : ℚ) : ℝ) < ((cr : ℚ) : ℝ) / 2 := by
    have : 2 * e < cr := hcross
    have h2 : 2 * ((e : ℚ) : ℝ) < ((cr : ℚ) : ℝ) := by exact_mod_cast this
    linarith
  have : ((threshold : ℚ) : ℝ) < ((hull.area : ℚ) : ℝ) := by linarith
  exact_mod_cast this

/-- **Threshold violated outside the growth half-space intersection.**
If the verified growth half-space intersection is `q` and `p` lies outside `q`,
then the area of the verified convex hull of `P ∪ {p}` exceeds the threshold. -/
theorem areaThreshold_lt_area_of_outside_growthHalfspaceIntersection {poly : ConvexPolygon ℚ}
    {threshold : ℚ} {q : ConvexPolygon ℚ}
    (hq : ConvexPolygon.growthHalfspaceIntersectionChecked poly threshold = some q)
    {p : Point ℚ} (hp : q.contains p = false) {hull : ConvexPolygon ℚ}
    (hhull : ConvexPolygon.ofListChecked (p :: poly.vertex_list) = some hull) :
    threshold < hull.area := by
  obtain ⟨i, j, hij, hout⟩ := ConvexPolygon.exists_growthHalfspace_not_contains hq hp
  exact areaThreshold_lt_area_of_outside_growthHalfspace hij hout hhull

end Moser

end
