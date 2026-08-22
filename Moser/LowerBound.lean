module

public import Mathlib
public import Moser.Constants
public import Moser.Manipulation.Operations
public import Moser.Real.CompactnessOutline
meta import Mathlib
meta import Moser.Constants
meta import Moser.Geometry.Polygon
meta import Moser.Manipulation.Invariants
meta import Moser.Manipulation.Operations

public section

/-!
# The lower-bound spine

This file states the end-to-end argument ("the spine") by which the computational
working-set algorithm of `Moser.Manipulation` is intended to prove a new record
lower bound for Moser's worm problem:

  `areaThreshold = 0.232240 ≤ moserCoverNumber`,

one micro-unit above the best published lower bound `0.232239`.

The chain is:

1. **Bridge** (`ConvexPolygon.realHull`, `ConvexPolygon.volume_realHull`,
   `ConvexPolygon.realHull_subset_realHull`): interpret the rational polygons of the
   computational layer as subsets of the real Euclidean plane, with matching area
   and containment.
2. **Invariants** (`WorkingSet.ContainsInitialWorm`, `WorkingSet.Sound`): the formal
   statements of Invariants 2 and 3 of `Moser.Manipulation.Invariants`. `Sound s`
   says: every *pinned small cover* — a convex set of area at most `areaThreshold`
   containing the unshifted `InitialWorm` hull and covering every worm up to direct
   isometry — must contain (unshifted) some polygon of `s`.
3. **Preservation** (`WorkingSet.Sound.bigSetRemoval`, `.supersetRemoval`): the
   cleanup operations preserve soundness. The remaining case, `wormAdding`, is the
   mathematical crux of the whole development and is carried as an explicit
   hypothesis `WorkingSet.WormAddingSound`; see its docstring.
4. **Termination ⇒ bound** (`Moser.areaThreshold_le_moserCoverNumber_of_run`): if a
   sound working set becomes empty, no pinned small cover exists, and after
   un-pinning (`Moser.exists_pinnedSmallCover`) and passing from placement covers to
   convex covers (`Moser.le_moserCoverNumber_of_forall_convex_cover`) the record
   bound `areaThreshold ≤ moserCoverNumber` follows.

The record bound itself is not asserted anywhere: it awaits a certificate, i.e. a
proof of `∃ s, s.Sound ∧ s.polygons = []` obtained by iterating
`addWormAndCleanup` from `WorkingSet.initial`, at which point
`Moser.areaThreshold_le_moserCoverNumber_of_run` delivers it.

Deliberately **not** on this path: the planar Steiner formula and `approxAlgorithm`
in `Moser.Real.CompactnessOutline` (upper-bound/approximation track) and the
polygon-containment decision procedure (`containsCopyOf`).
-/

open MeasureTheory Moser.CompactnessOutline
open scoped ENNReal

/-- The real Euclidean plane `ℝ²`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Bridge: rational polygons in the real plane -/

/-- Cast a rational point of the computational layer to the real Euclidean plane. -/
noncomputable def Point.toEuclidean (p : Point ℚ) : ℝ² :=
  WithLp.toLp 2 ![(p 0 : ℝ), (p 1 : ℝ)]

namespace ConvexPolygon

/-- The real planar region of a rational convex polygon: the convex hull of its
vertices, cast into `ℝ²`. This is the semantics against which the computational
layer is judged. -/
noncomputable def realHull (poly : ConvexPolygon ℚ) : Set ℝ² :=
  convexHull ℝ (Set.range fun i => Point.toEuclidean (poly.vertices i))

/-- Unfolding lemma for `realHull`, usable from other modules. -/
lemma realHull_eq (poly : ConvexPolygon ℚ) :
    poly.realHull = convexHull ℝ (Set.range fun i => Point.toEuclidean (poly.vertices i)) := by
  simp [ConvexPolygon.realHull]

/-- The real region of a rational convex polygon is convex. -/
theorem convex_realHull (poly : ConvexPolygon ℚ) : Convex ℝ poly.realHull :=
  convex_convexHull ℝ _

/- The **area bridge** `volume_realHull` is stated and proved at the end of
this section, after the fan-decomposition machinery it rests on. -/

/-! ### Soundness of the half-space test with respect to `realHull`

`ConvexPolygon.contains` accepts `v` iff `v` is weakly to the left of every
directed edge of the (counterclockwise) polygon. The lemmas below show any such
point lies in the real convex hull of the vertices — the easy direction of
polyhedral duality, via fan triangulation from vertex `0` with explicit
barycentric coordinates on each triangle. -/

/-- Cross product of two vectors of the real plane. -/
def rcross (u v : ℝ²) : ℝ := u 0 * v 1 - u 1 * v 0

/-- Unfolding lemma for `rcross`, usable from other modules. -/
lemma rcross_def (u v : ℝ²) : rcross u v = u 0 * v 1 - u 1 * v 0 := by simp [rcross]

/-- Twice the signed area of a triangle is invariant under cyclic rotation of
its vertices. -/
lemma rcross_cycle (a b c : ℝ²) :
    rcross (b - a) (c - a) = rcross (c - b) (a - b) := by
  simp only [rcross, PiLp.sub_apply]
  ring

/-- Reversing the base edge negates the side of the test point. -/
lemma rcross_flip (a b v : ℝ²) :
    rcross (a - b) (v - b) = -rcross (b - a) (v - a) := by
  simp only [rcross, PiLp.sub_apply]
  ring

/-- **Barycentric triangle membership**: a point weakly to the left of all three
directed edges of a positively oriented triangle lies in the convex hull of its
vertices. The barycentric weights are the subtriangle areas over the total
area: nonnegative by the edge conditions, and reconstituting `v` by an
algebraic identity. -/
private lemma mem_convexHull_triangle {a b c v : ℝ²}
    (hD : 0 < rcross (b - a) (c - a))
    (h1 : 0 ≤ rcross (b - a) (v - a))
    (h2 : 0 ≤ rcross (c - b) (v - b))
    (h3 : 0 ≤ rcross (a - c) (v - c)) :
    v ∈ convexHull ℝ ({a, b, c} : Set ℝ²) := by
  have hD' : rcross (b - a) (c - a) ≠ 0 := ne_of_gt hD
  have hsum3 : rcross (c - b) (v - b) + rcross (a - c) (v - c) + rcross (b - a) (v - a)
      = rcross (b - a) (c - a) := by
    simp only [rcross, PiLp.sub_apply]
    ring
  have key := (convex_convexHull ℝ ({a, b, c} : Set ℝ²)).sum_mem
    (t := (Finset.univ : Finset (Fin 3)))
    (w := fun i => ![rcross (c - b) (v - b), rcross (a - c) (v - c),
      rcross (b - a) (v - a)] i / rcross (b - a) (c - a))
    (z := ![a, b, c])
    (fun i _ => by
      refine div_nonneg ?_ hD.le
      fin_cases i
      · exact h2
      · exact h3
      · exact h1)
    (by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [← add_div, ← add_div, hsum3, div_self hD'])
    (fun i _ => subset_convexHull ℝ _ (by fin_cases i <;> simp))
  have hv : (∑ i : Fin 3, (![rcross (c - b) (v - b), rcross (a - c) (v - c),
      rcross (b - a) (v - a)] i / rcross (b - a) (c - a)) • (![a, b, c] i)) = v := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ext j
    have hmul : rcross (c - b) (v - b) * a j + rcross (a - c) (v - c) * b j
        + rcross (b - a) (v - a) * c j = rcross (b - a) (c - a) * v j := by
      fin_cases j <;>
        · simp only [rcross, PiLp.sub_apply, Fin.zero_eta, Fin.mk_one]
          ring
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
      ← add_div, ← add_div, hmul, mul_div_cancel_left₀ _ hD']
  rwa [hv] at key

/-- **Fan-induction hull membership**: a point weakly to the left of every
directed edge of a vertex cycle `w 0, …, w (n-1)` whose fan triangles from
`w 0` are positively oriented lies in the convex hull of the vertices. -/
lemma mem_convexHull_fan (w : ℕ → ℝ²) (v : ℝ²) : ∀ n, 3 ≤ n →
    (∀ k, k + 1 < n → 0 ≤ rcross (w (k + 1) - w k) (v - w k)) →
    0 ≤ rcross (w 0 - w (n - 1)) (v - w (n - 1)) →
    (∀ k, 1 ≤ k → k + 2 ≤ n → 0 < rcross (w (k + 1) - w k) (w 0 - w k)) →
    v ∈ convexHull ℝ (w '' Set.Iio n) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
    intro hn hedge hclose hfan
    rcases eq_or_lt_of_le hn with heq | hlt
    · -- base case `n = 3`: a single triangle
      obtain rfl : m = 2 := by omega
      have hD : 0 < rcross (w 1 - w 0) (w 2 - w 0) := by
        have h := hfan 1 le_rfl (by norm_num)
        rwa [← rcross_cycle (w 0) (w 1) (w 2)] at h
      have hclose' : 0 ≤ rcross (w 0 - w 2) (v - w 2) := hclose
      have hmem := mem_convexHull_triangle hD (hedge 0 (by norm_num))
        (hedge 1 (by norm_num)) hclose'
      refine convexHull_mono ?_ hmem
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, Set.mem_Iio.mpr (by omega), rfl⟩
      · exact ⟨1, Set.mem_Iio.mpr (by omega), rfl⟩
      · exact ⟨2, Set.mem_Iio.mpr (by omega), rfl⟩
    · -- inductive step `n = m + 1 ≥ 4`
      have hm3 : 3 ≤ m := by omega
      by_cases hcase : 0 ≤ rcross (w 0 - w (m - 1)) (v - w (m - 1))
      · exact convexHull_mono (Set.image_mono (Set.Iio_subset_Iio (by omega)))
          (ih hm3 (fun k hk => hedge k (by omega)) hcase
            (fun k hk1 hk2 => hfan k hk1 (by omega)))
      · push Not at hcase
        have hm1 : m - 1 + 1 = m := by omega
        have hD : 0 < rcross (w (m - 1) - w 0) (w m - w 0) := by
          have h := hfan (m - 1) (by omega) (by omega)
          rw [hm1] at h
          rwa [← rcross_cycle (w 0) (w (m - 1)) (w m)] at h
        have h1 : 0 ≤ rcross (w (m - 1) - w 0) (v - w 0) := by
          have h := rcross_flip (w 0) (w (m - 1)) v
          linarith
        have h2 : 0 ≤ rcross (w m - w (m - 1)) (v - w (m - 1)) := by
          have h := hedge (m - 1) (by omega)
          rwa [hm1] at h
        have h3 : 0 ≤ rcross (w 0 - w m) (v - w m) := hclose
        have hmem := mem_convexHull_triangle hD h1 h2 h3
        refine convexHull_mono ?_ hmem
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨0, Set.mem_Iio.mpr (by omega), rfl⟩
        · exact ⟨m - 1, Set.mem_Iio.mpr (by omega), rfl⟩
        · exact ⟨m, Set.mem_Iio.mpr (by omega), rfl⟩

/-- The dot product against a `90°`-rotated vector is the cross product against
the original. -/
private lemma dotProduct_rotate90 (d x : Point ℚ) :
    Point.dotProduct (Point.rotate90Counterclockwise d) x = Point.crossProduct d x := by
  simp only [Point.dotProduct, Point.rotate90Counterclockwise, Point.crossProduct,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Casting the rational cross product of differences to the real plane. -/
private lemma rcross_toEuclidean (u u' x x' : Point ℚ) :
    rcross (Point.toEuclidean u - Point.toEuclidean u')
      (Point.toEuclidean x - Point.toEuclidean x')
      = ((Point.crossProduct (u - u') (x - x') : ℚ) : ℝ) := by
  simp only [rcross, Point.toEuclidean, PiLp.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Point.crossProduct, Pi.sub_apply]
  push_cast
  ring

/-- **Soundness of the half-space test.** Any rational point accepted by
`ConvexPolygon.contains` lies in the real convex hull of the polygon's
vertices. -/
theorem mem_realHull_of_contains {q : ConvexPolygon ℚ} {v : Point ℚ}
    (h : q.contains v = true) : Point.toEuclidean v ∈ q.realHull := by
  haveI := q.vertex_count_pos
  have hn3 : 3 ≤ q.vertex_count := q.three_le_vertex_count
  have hpos : 0 < q.vertex_count := by omega
  -- extract the Boolean test into per-edge rational inequalities
  obtain ⟨hs, hhs, hall⟩ : ∃ hs, q.toHalfSpaces = some hs ∧
      hs.all (fun hsp => hsp.contains v) = true := by
    unfold ConvexPolygon.contains at h
    rcases htH : q.toHalfSpaces with _ | hs
    · rw [htH] at h
      exact absurd h (by simp)
    · rw [htH] at h
      exact ⟨hs, rfl, h⟩
  rw [ConvexPolygon.toHalfSpaces, dif_neg (by omega)] at hhs
  replace hhs := Option.some.inj hhs
  have hedgeQ : ∀ i : Fin q.vertex_count,
      0 ≤ Point.crossProduct (q.vertices (i + ⟨1, by omega⟩) - q.vertices i)
        (v - q.vertices i) := by
    intro i
    have hcont := List.all_eq_true.mp hall _
      (hhs ▸ List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    simp only [ClosedHalfSpace.contains, Point.toWeaklyLeft, ge_iff_le,
      decide_eq_true_eq] at hcont
    rwa [dotProduct_rotate90] at hcont
  -- the cyclic vertex sequence, indexed by `ℕ`
  set wV : ℕ → Point ℚ := fun k => q.vertices ⟨k % q.vertex_count, Nat.mod_lt _ hpos⟩
    with hwV
  have hVk : ∀ (k : ℕ) (hk : k < q.vertex_count), wV k = q.vertices ⟨k, hk⟩ := by
    intro k hk
    simp only [hwV]
    exact congrArg q.vertices (Fin.ext (Nat.mod_eq_of_lt hk))
  have hedgeW : ∀ k, k < q.vertex_count →
      0 ≤ Point.crossProduct (wV (k + 1) - wV k) (v - wV k) := by
    intro k hk
    have hQ := hedgeQ ⟨k, hk⟩
    have h1 : wV (k + 1) = q.vertices (⟨k, hk⟩ + ⟨1, by omega⟩) := by
      simp only [hwV]
      exact congrArg q.vertices (Fin.ext (by rw [Fin.val_add]))
    rw [h1, hVk k hk]
    exact hQ
  have hfanW : ∀ k, 1 ≤ k → k + 2 ≤ q.vertex_count →
      0 < Point.crossProduct (wV (k + 1) - wV k) (wV 0 - wV k) := by
    intro k hk1 hk2
    have hccw := q.vertices_extremePoints ⟨k, by omega⟩ ⟨0, by omega⟩
      (Fin.ne_of_val_ne (show (0 : ℕ) ≠ k by omega))
      (by
        refine Fin.ne_of_val_ne ?_
        change (0 : ℕ) ≠ _
        rw [Fin.val_add, Fin.val_one',
          Nat.mod_eq_of_lt (show 1 < q.vertex_count by omega),
          Nat.mod_eq_of_lt (show k + 1 < q.vertex_count by omega)]
        omega)
    simp only [Point.ccw, Point.isStrictlyLeftOf, decide_eq_true_eq] at hccw
    have e1 : q.vertices (⟨k, by omega⟩ + 1) = wV (k + 1) := by
      simp only [hwV]
      refine congrArg q.vertices (Fin.ext ?_)
      rw [Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt (show 1 < q.vertex_count by omega)]
    have e2 : q.vertices ⟨k, by omega⟩ = wV k := (hVk k (by omega)).symm
    have e3 : q.vertices ⟨0, by omega⟩ = wV 0 := (hVk 0 (by omega)).symm
    rwa [e1, e2, e3] at hccw
  -- transfer to the real plane
  have hedgeR : ∀ k, k < q.vertex_count →
      0 ≤ rcross (Point.toEuclidean (wV (k + 1)) - Point.toEuclidean (wV k))
        (Point.toEuclidean v - Point.toEuclidean (wV k)) := by
    intro k hk
    rw [rcross_toEuclidean]
    exact_mod_cast hedgeW k hk
  have hfanR : ∀ k, 1 ≤ k → k + 2 ≤ q.vertex_count →
      0 < rcross (Point.toEuclidean (wV (k + 1)) - Point.toEuclidean (wV k))
        (Point.toEuclidean (wV 0) - Point.toEuclidean (wV k)) := by
    intro k hk1 hk2
    rw [rcross_toEuclidean]
    exact_mod_cast hfanW k hk1 hk2
  have hmem := mem_convexHull_fan (fun k => Point.toEuclidean (wV k))
    (Point.toEuclidean v) q.vertex_count hn3
    (fun k hk => hedgeR k (by omega))
    (by
      have h := hedgeR (q.vertex_count - 1) (by omega)
      have hN1 : q.vertex_count - 1 + 1 = q.vertex_count := by omega
      rw [hN1] at h
      have hwN : wV q.vertex_count = wV 0 := by
        simp only [hwV]
        exact congrArg q.vertices (Fin.ext
          (show q.vertex_count % q.vertex_count = 0 % q.vertex_count by simp))
      rwa [hwN] at h)
    hfanR
  have himg : (fun k => Point.toEuclidean (wV k)) '' Set.Iio q.vertex_count
      = Set.range (fun i => Point.toEuclidean (q.vertices i)) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k % q.vertex_count, Nat.mod_lt _ hpos⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, congrArg (fun j => Point.toEuclidean (q.vertices j))
        (Fin.ext (Nat.mod_eq_of_lt i.isLt))⟩
  rw [ConvexPolygon.realHull, ← himg]
  exact hmem

/-- **Containment bridge.** The Boolean vertex-containment test `isSubsetOf`
implies containment of the real regions: each vertex of `p` passes `q`'s
half-space test, hence lies in `q.realHull` (`mem_realHull_of_contains`), and
`p.realHull` is the hull of those vertices. -/
theorem realHull_subset_realHull {p q : ConvexPolygon ℚ}
    (h : p.isSubsetOf q = true) : p.realHull ⊆ q.realHull := by
  rw [ConvexPolygon.realHull]
  refine convexHull_min ?_ q.convex_realHull
  rintro x ⟨i, rfl⟩
  refine mem_realHull_of_contains ?_
  rw [ConvexPolygon.isSubsetOf, List.all_eq_true] at h
  exact h _ (by
    rw [ConvexPolygon.vertex_list]
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

/-! ### A verified convex hull

`convexHullPoints` is not proved correct (see `convexHullPoints_convex` in
`Moser.Geometry.Polygon`; the cyclic-chain invariant is not enough, by the
pentagram counterexample). Correctness can nevertheless be obtained *per call*
by checking, after the fact, that the polygon produced contains every input
point: together with the fact that the algorithm introduces no new points
(`mem_of_mem_convexHullPoints`) this pins the real region down exactly. -/

/-- **Correctness of the verified convex hull.** When `ofListChecked` succeeds,
the real region of the resulting polygon is exactly the convex hull of the input
points: it contains them because the run-time check verified it, and it is
contained in their hull because the algorithm returns only input points. -/
theorem realHull_ofListChecked {verts : List (Point ℚ)}
    {poly : ConvexPolygon ℚ} (h : ofListChecked verts = some poly) :
    poly.realHull = convexHull ℝ (Point.toEuclidean '' {p | p ∈ verts}) := by
  obtain ⟨hof, hcontains⟩ := ofListChecked_eq_some h
  refine Set.Subset.antisymm ?_ ?_
  · rw [ConvexPolygon.realHull]
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro _ ⟨i, rfl⟩
    exact subset_convexHull ℝ _
      ⟨poly.vertices i, vertices_mem_of_ofList hof i, rfl⟩
  · refine convexHull_min ?_ poly.convex_realHull
    rintro _ ⟨v, hv, rfl⟩
    exact mem_realHull_of_contains (hcontains v hv)

/-! ### Volume of a triangle

Toward the area bridge `volume_realHull`: the Lebesgue volume of the convex
hull of a triangle is half the absolute cross product of its edge vectors.
Proved without integration: the triangle is the affine image of the standard
simplex, and the standard simplex is half of the unit square — the square is
the union of the simplex and its point reflection, overlapping in a null
diagonal. -/

/-- The standard `2`-simplex `{x | 0 ≤ x₀, 0 ≤ x₁, x₀ + x₁ ≤ 1}`. -/
private def stdSimplex2 : Set ℝ² := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

/-- Coordinate evaluation on the real plane is measurable. -/
private lemma measurable_coord (i : Fin 2) : Measurable fun x : ℝ² => x i :=
  (measurable_pi_apply i).comp (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurable

private lemma measurableSet_stdSimplex2 : MeasurableSet stdSimplex2 := by
  unfold stdSimplex2
  rw [Set.setOf_and, Set.setOf_and]
  exact (measurableSet_le measurable_const (measurable_coord 0)).inter
    ((measurableSet_le measurable_const (measurable_coord 1)).inter
      (measurableSet_le ((measurable_coord 0).add (measurable_coord 1)) measurable_const))

private lemma convex_stdSimplex2 : Convex ℝ stdSimplex2 := by
  rintro x ⟨hx0, hx1, hxs⟩ y ⟨hy0, hy1, hys⟩ s t hs ht hst
  refine ⟨?_, ?_, ?_⟩ <;> simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  · nlinarith [mul_nonneg hs hx0, mul_nonneg ht hy0]
  · nlinarith [mul_nonneg hs hx1, mul_nonneg ht hy1]
  · nlinarith [mul_le_mul_of_nonneg_left hxs hs, mul_le_mul_of_nonneg_left hys ht]

/-- The unit square in the real plane has volume `1`, by transfer to the
product Lebesgue measure. -/
private lemma volume_unitSquare2 :
    volume {x : ℝ² | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1} = 1 := by
  have h : {x : ℝ² | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}
      = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.pi_univ_Icc, Set.mem_Icc, Pi.le_def,
      Fin.forall_fin_two]
    tauto
  rw [h, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).nullMeasurableSet,
    volume_pi_pi]
  simp [Real.volume_Icc]

/-- A point reflection of the plane preserves volume. -/
private lemma volume_reflect (e : ℝ²) {S : Set ℝ²} (hS : NullMeasurableSet S volume) :
    volume ((fun x => e - x) '' S) = volume S := by
  have hinv : ∀ x : ℝ², e - (e - x) = x := fun x => sub_sub_cancel e x
  rw [Set.image_eq_preimage_of_inverse hinv hinv]
  have hmp : MeasurePreserving (fun x : ℝ² => e - x) volume volume := by
    have hfun : (fun x : ℝ² => e - x) = (fun y : ℝ² => e + y) ∘ (fun x : ℝ² => -x) := by
      funext x
      simp [sub_eq_add_neg]
    rw [hfun]
    exact (measurePreserving_add_left volume e).comp (Measure.measurePreserving_neg volume)
  exact hmp.measure_preimage hS

/-- The diagonal line `x₀ + x₁ = 1` is a null set: it is a proper affine
subspace of the plane. -/
private lemma volume_diagLine2 : volume {x : ℝ² | x 0 + x 1 = 1} = 0 := by
  classical
  set f : ℝ² →ₗ[ℝ] ℝ := PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)
    + PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) with hf
  set A : AffineSubspace ℝ ℝ² :=
    AffineSubspace.mk' (WithLp.toLp 2 ![1, 0]) (LinearMap.ker f) with hA
  have hset : {x : ℝ² | x 0 + x 1 = 1} = (A : Set ℝ²) := by
    ext x
    simp only [Set.mem_setOf_eq, hA, SetLike.mem_coe, AffineSubspace.mem_mk',
      vsub_eq_sub, LinearMap.mem_ker, hf, LinearMap.add_apply, PiLp.projₗ_apply,
      PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> intro h <;> linarith
  have hne : A ≠ ⊤ := by
    intro htop
    have h0 : (0 : ℝ²) ∈ {x : ℝ² | x 0 + x 1 = 1} := by
      rw [hset, htop]
      simp
    norm_num [PiLp.zero_apply] at h0
  rw [hset]
  exact Measure.addHaar_affineSubspace volume A hne

/-- **The standard simplex has volume `1/2`**: it is half of the unit square,
the other half being its point reflection through the square's center, and the
two halves overlap in a null diagonal. -/
private lemma volume_stdSimplex2 : volume stdSimplex2 = 2⁻¹ := by
  classical
  set e : ℝ² := WithLp.toLp 2 ![1, 1] with he
  set S' : Set ℝ² := (fun x => e - x) '' stdSimplex2 with hS'
  have hS'eq : S' = {x : ℝ² | x 0 ≤ 1 ∧ x 1 ≤ 1 ∧ 1 ≤ x 0 + x 1} := by
    ext x
    simp only [hS', Set.mem_image, stdSimplex2, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨hy0, hy1, hys⟩, rfl⟩
      refine ⟨?_, ?_, ?_⟩ <;>
        simp only [he, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        linarith
    · rintro ⟨h0, h1, hsum⟩
      refine ⟨e - x, ⟨?_, ?_, ?_⟩, sub_sub_cancel e x⟩ <;>
        simp only [he, PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        linarith
  have hmeasS' : MeasurableSet S' := by
    rw [hS'eq, Set.setOf_and, Set.setOf_and]
    exact (measurableSet_le (measurable_coord 0) measurable_const).inter
      ((measurableSet_le (measurable_coord 1) measurable_const).inter
        (measurableSet_le measurable_const ((measurable_coord 0).add (measurable_coord 1))))
  have hunion : stdSimplex2 ∪ S' = {x : ℝ² | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1} := by
    rw [hS'eq]
    ext x
    simp only [Set.mem_union, stdSimplex2, Set.mem_setOf_eq, Set.mem_Icc, Fin.forall_fin_two]
    constructor
    · rintro (⟨h0, h1, hs⟩ | ⟨h0, h1, hs⟩) <;>
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · rintro ⟨⟨h00, h01⟩, h10, h11⟩
      rcases le_total (x 0 + x 1) 1 with h | h
      · exact Or.inl ⟨h00, h10, h⟩
      · exact Or.inr ⟨h01, h11, h⟩
  have hinter : stdSimplex2 ∩ S' ⊆ {x : ℝ² | x 0 + x 1 = 1} := by
    rw [hS'eq]
    rintro x ⟨⟨-, -, hs1⟩, -, -, hs2⟩
    exact le_antisymm hs1 hs2
  have hvolS' : volume S' = volume stdSimplex2 :=
    volume_reflect e measurableSet_stdSimplex2.nullMeasurableSet
  have hkey := measure_union_add_inter (μ := volume) stdSimplex2 hmeasS'
  rw [hunion, volume_unitSquare2, measure_mono_null hinter volume_diagLine2, add_zero,
    hvolS'] at hkey
  have h2 : (2 : ℝ≥0∞) * volume stdSimplex2 = 1 := by
    rw [two_mul]
    exact hkey.symm
  rw [← one_mul (volume stdSimplex2),
    ← ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_assoc, h2, mul_one]

/-- The linear shear sending the standard basis to the vectors `u`, `v`. -/
private noncomputable def shearMap (u v : ℝ²) : ℝ² →ₗ[ℝ] ℝ² :=
  (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)).smulRight u
    + (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2)).smulRight v

private lemma det_shearMap (u v : ℝ²) : LinearMap.det (shearMap u v) = rcross u v := by
  classical
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 2)), Matrix.det_fin_two]
  have e0 : shearMap u v (PiLp.basisFun 2 ℝ (Fin 2) 0) = u := by
    simp [shearMap, PiLp.basisFun_apply]
  have e1 : shearMap u v (PiLp.basisFun 2 ℝ (Fin 2) 1) = v := by
    simp [shearMap, PiLp.basisFun_apply]
  simp only [LinearMap.toMatrix_apply, PiLp.basisFun_repr, e0, e1, rcross]
  ring

/-- A triangle is the affine image of the standard simplex. -/
private lemma convexHull_triangle_eq_image (a b c : ℝ²) :
    convexHull ℝ ({a, b, c} : Set ℝ²)
      = (fun x : ℝ² => a + (x 0 • (b - a) + x 1 • (c - a))) '' stdSimplex2 := by
  have hcoe : ⇑(shearMap (b - a) (c - a)) = fun x : ℝ² => x 0 • (b - a) + x 1 • (c - a) := by
    funext x
    simp [shearMap]
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ ?_
    · rintro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · refine ⟨0, ⟨?_, ?_, ?_⟩, ?_⟩ <;> simp [PiLp.zero_apply]
      · refine ⟨WithLp.toLp 2 ![1, 0], ⟨?_, ?_, ?_⟩, ?_⟩ <;> simp
      · refine ⟨WithLp.toLp 2 ![0, 1], ⟨?_, ?_, ?_⟩, ?_⟩ <;> simp
    · have himg : (fun x : ℝ² => a + (x 0 • (b - a) + x 1 • (c - a))) '' stdSimplex2
          = (fun y => a + y) '' (⇑(shearMap (b - a) (c - a)) '' stdSimplex2) := by
        rw [Set.image_image, hcoe]
      rw [himg]
      exact (convex_stdSimplex2.linear_image (shearMap (b - a) (c - a))).translate a
  · rintro x ⟨y, ⟨hy0, hy1, hys⟩, rfl⟩
    have key := (convex_convexHull ℝ ({a, b, c} : Set ℝ²)).sum_mem
      (t := (Finset.univ : Finset (Fin 3)))
      (w := ![1 - y 0 - y 1, y 0, y 1])
      (z := ![a, b, c])
      (fun i _ => by
        fin_cases i
        · exact (by linarith : (0 : ℝ) ≤ 1 - y 0 - y 1)
        · exact hy0
        · exact hy1)
      (by
        rw [Fin.sum_univ_three]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
        ring)
      (fun i _ => subset_convexHull ℝ _ (by fin_cases i <;> simp))
    have hsum : (∑ i : Fin 3, (![1 - y 0 - y 1, y 0, y 1] : Fin 3 → ℝ) i • ![a, b, c] i)
        = a + (y 0 • (b - a) + y 1 • (c - a)) := by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      module
    rwa [hsum] at key

/-- **Volume of a triangle**: half the absolute cross product of its edge
vectors. -/
lemma volume_triangle (a b c : ℝ²) :
    volume (convexHull ℝ ({a, b, c} : Set ℝ²))
      = ENNReal.ofReal (|rcross (b - a) (c - a)| / 2) := by
  classical
  have hcompact : IsCompact (convexHull ℝ ({a, b, c} : Set ℝ²)) :=
    Set.Finite.isCompact_convexHull ℝ (((Set.finite_singleton c).insert b).insert a)
  have hmeas : MeasurableSet (convexHull ℝ ({a, b, c} : Set ℝ²)) :=
    hcompact.isClosed.measurableSet
  have hF : (fun x : ℝ² => a + (x 0 • (b - a) + x 1 • (c - a)))
      = (fun y => a + y) ∘ ⇑(shearMap (b - a) (c - a)) := by
    funext x
    simp [shearMap]
  calc volume (convexHull ℝ ({a, b, c} : Set ℝ²))
      = volume ((fun y => a + y) ⁻¹' convexHull ℝ ({a, b, c} : Set ℝ²)) :=
        ((measurePreserving_add_left volume a).measure_preimage
          hmeas.nullMeasurableSet).symm
    _ = volume (⇑(shearMap (b - a) (c - a)) '' stdSimplex2) := by
        rw [convexHull_triangle_eq_image a b c, hF, Set.image_comp,
          Set.preimage_image_eq _ (add_right_injective a)]
    _ = ENNReal.ofReal |LinearMap.det (shearMap (b - a) (c - a))| * volume stdSimplex2 := by
        rw [Measure.addHaar_image_linearMap]
    _ = ENNReal.ofReal (|rcross (b - a) (c - a)| / 2) := by
        rw [det_shearMap, volume_stdSimplex2, div_eq_mul_inv,
          ENNReal.ofReal_mul (abs_nonneg _),
          ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num

/-! ### Fan decomposition of a convex polygon

The hull of the vertex cycle is the union of the fan triangles from vertex
`0`, the fan triangles overlap only in null diagonal segments, and hence the
volume of the hull is the sum of the fan triangle volumes. The key geometric
input is *diagonal positivity* — every pair of distinct non-zero vertices is
positively oriented seen from `w 0` — which follows from the edge conditions
by transitivity of the angular order inside an open half-plane, itself an
instance of the Grassmann–Plücker relation. -/

/-- The Grassmann–Plücker relation for planar cross products. -/
private lemma rcross_pluecker (d u v t : ℝ²) :
    rcross d v * rcross u t = rcross d u * rcross v t + rcross d t * rcross u v := by
  simp only [rcross]
  ring

/-- Transitivity of the angular order about the origin, within the open
half-plane on the positive side of `d`. -/
private lemma rcross_trans {d u v t : ℝ²} (hdu : 0 < rcross d u) (hdv : 0 < rcross d v)
    (hdt : 0 < rcross d t) (huv : 0 < rcross u v) (hvt : 0 < rcross v t) :
    0 < rcross u t := by
  nlinarith [rcross_pluecker d u v t, mul_pos hdu hvt, mul_pos hdt huv]

/-- **Diagonal positivity.** If all vertices `w 2, …, w (n-1)` lie strictly to
the left of the ray `w 0 → w 1`, and consecutive fan triangles are positively
oriented, then every diagonal pair is positively oriented as seen from `w 0`. -/
private lemma fan_diag_pos (w : ℕ → ℝ²) (n : ℕ)
    (h01 : ∀ k, 2 ≤ k → k ≤ n - 1 → 0 < rcross (w 1 - w 0) (w k - w 0))
    (hcons : ∀ k, 1 ≤ k → k + 2 ≤ n → 0 < rcross (w k - w 0) (w (k + 1) - w 0)) :
    ∀ j i, 1 ≤ i → i < j → j ≤ n - 1 → 0 < rcross (w i - w 0) (w j - w 0) := by
  intro j
  induction j with
  | zero => omega
  | succ m ih =>
    intro i hi1 hij hj
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hij) with rfl | him
    · -- `j = i + 1`: the consecutive fan triangle
      exact hcons i hi1 (by omega)
    · -- `i < m`: chain through `m` by Plücker transitivity
      rcases eq_or_lt_of_le hi1 with rfl | hi2
      · exact h01 (m + 1) (by omega) hj
      · exact rcross_trans
          (h01 i (by omega) (by omega))
          (h01 m (by omega) (by omega))
          (h01 (m + 1) (by omega) hj)
          (ih i hi1 him (by omega))
          (hcons m (by omega) (by omega))

/-- A closed half-plane is convex, so it absorbs the convex hull of any set of
points it contains. -/
lemma convexHull_subset_halfplane {S : Set ℝ²} (d w₀ : ℝ²)
    (h : ∀ y ∈ S, 0 ≤ rcross d (y - w₀)) :
    convexHull ℝ S ⊆ {y : ℝ² | 0 ≤ rcross d (y - w₀)} := by
  refine convexHull_min h ?_
  intro x hx y hy s t hs ht hst
  have hexp : rcross d (s • x + t • y - w₀)
      = s * rcross d (x - w₀) + t * rcross d (y - w₀) := by
    have ht1 : t = 1 - s := by linarith
    subst ht1
    simp only [rcross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  change 0 ≤ rcross d (s • x + t • y - w₀)
  rw [hexp]
  exact add_nonneg (mul_nonneg hs hx) (mul_nonneg ht hy)

/-- The fan version of `mem_convexHull_fan`: a point weakly to the left of
every directed edge lies in the *union of the fan triangles*, not merely in
the hull. -/
private lemma mem_iUnion_fan (w : ℕ → ℝ²) (v : ℝ²) : ∀ n, 3 ≤ n →
    (∀ k, k + 1 < n → 0 ≤ rcross (w (k + 1) - w k) (v - w k)) →
    0 ≤ rcross (w 0 - w (n - 1)) (v - w (n - 1)) →
    (∀ k, 1 ≤ k → k + 2 ≤ n → 0 < rcross (w (k + 1) - w k) (w 0 - w k)) →
    v ∈ ⋃ k ∈ Finset.Ico 1 (n - 1), convexHull ℝ ({w 0, w k, w (k + 1)} : Set ℝ²) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
    intro hn hedge hclose hfan
    rcases eq_or_lt_of_le hn with heq | hlt
    · -- base case `n = 3`: the single triangle `k = 1`
      obtain rfl : m = 2 := by omega
      have hD : 0 < rcross (w 1 - w 0) (w 2 - w 0) := by
        have h := hfan 1 le_rfl (by norm_num)
        rwa [← rcross_cycle (w 0) (w 1) (w 2)] at h
      have hclose' : 0 ≤ rcross (w 0 - w 2) (v - w 2) := hclose
      have hmem := mem_convexHull_triangle hD (hedge 0 (by norm_num))
        (hedge 1 (by norm_num)) hclose'
      exact Set.mem_biUnion (by simp) hmem
    · -- inductive step `n = m + 1 ≥ 4`
      have hm3 : 3 ≤ m := by omega
      by_cases hcase : 0 ≤ rcross (w 0 - w (m - 1)) (v - w (m - 1))
      · have hsub := ih hm3 (fun k hk => hedge k (by omega)) hcase
          (fun k hk1 hk2 => hfan k hk1 (by omega))
        refine Set.mem_of_subset_of_mem (Set.biUnion_subset_biUnion_left ?_) hsub
        intro k hk
        simp only [Finset.coe_Ico, Set.mem_Ico] at hk ⊢
        omega
      · push Not at hcase
        have hm1 : m - 1 + 1 = m := by omega
        have hD : 0 < rcross (w (m - 1) - w 0) (w m - w 0) := by
          have h := hfan (m - 1) (by omega) (by omega)
          rw [hm1] at h
          rwa [← rcross_cycle (w 0) (w (m - 1)) (w m)] at h
        have h1 : 0 ≤ rcross (w (m - 1) - w 0) (v - w 0) := by
          have h := rcross_flip (w 0) (w (m - 1)) v
          linarith
        have h2 : 0 ≤ rcross (w m - w (m - 1)) (v - w (m - 1)) := by
          have h := hedge (m - 1) (by omega)
          rwa [hm1] at h
        have h3 : 0 ≤ rcross (w 0 - w m) (v - w m) := hclose
        have hmem := mem_convexHull_triangle hD h1 h2 h3
        have hmem' : v ∈ convexHull ℝ ({w 0, w (m - 1), w (m - 1 + 1)} : Set ℝ²) := by
          rwa [hm1]
        exact Set.mem_biUnion (by simp only [Finset.coe_Ico, Set.mem_Ico]; omega) hmem'

lemma rcross_zero_right (u : ℝ²) : rcross u 0 = 0 := by
  simp [rcross]

/-- Any line in the plane is a null set: it is a proper affine subspace. -/
lemma volume_line (w d : ℝ²) (hd : d ≠ 0) :
    volume {y : ℝ² | rcross d (y - w) = 0} = 0 := by
  classical
  set f : ℝ² →ₗ[ℝ] ℝ :=
    (-(d 1)) • PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (0 : Fin 2)
      + (d 0) • PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) (1 : Fin 2) with hf
  have hfy : ∀ y : ℝ², f y = rcross d y := by
    intro y
    simp only [hf, LinearMap.add_apply, LinearMap.smul_apply, PiLp.projₗ_apply,
      smul_eq_mul, rcross]
    ring
  have hdz : 0 < rcross d (WithLp.toLp 2 ![-(d 1), d 0]) := by
    have hcoord : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hd (PiLp.ext fun i => by fin_cases i <;> simp [hcon.1, hcon.2])
    have hval : rcross d (WithLp.toLp 2 ![-(d 1), d 0]) = d 0 * d 0 + d 1 * d 1 := by
      simp only [rcross, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [hval]
    rcases hcoord with h | h
    · nlinarith [mul_self_nonneg (d 1), mul_self_pos.mpr h]
    · nlinarith [mul_self_nonneg (d 0), mul_self_pos.mpr h]
  have hset : {y : ℝ² | rcross d (y - w) = 0}
      = (AffineSubspace.mk' w (LinearMap.ker f) : Set ℝ²) := by
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub,
      LinearMap.mem_ker, hfy]
  have hne : AffineSubspace.mk' w (LinearMap.ker f) ≠ ⊤ := by
    intro htop
    have hmem : w + WithLp.toLp 2 ![-(d 1), d 0]
        ∈ AffineSubspace.mk' w (LinearMap.ker f) := by
      rw [htop]
      exact AffineSubspace.mem_top ℝ ℝ² _
    rw [AffineSubspace.mem_mk'] at hmem
    have hzero : f (WithLp.toLp 2 ![-(d 1), d 0]) = 0 := by
      simpa [vsub_eq_sub, add_sub_cancel_left, LinearMap.mem_ker] using hmem
    rw [hfy] at hzero
    exact absurd hzero (ne_of_gt hdz)
  rw [hset]
  exact Measure.addHaar_affineSubspace volume _ hne

/-- **Fan additivity**: the volume of the hull of the vertex cycle is the sum
of the volumes of the fan triangles from vertex `0`. The triangles overlap
only in diagonal segments, which are null; diagonal positivity provides the
separating lines. -/
private lemma volume_convexHull_fan (w : ℕ → ℝ²) (n : ℕ) (hn : 3 ≤ n)
    (hVedge : ∀ k l, k + 1 < n → l < n → 0 ≤ rcross (w (k + 1) - w k) (w l - w k))
    (hVclose : ∀ l, l < n → 0 ≤ rcross (w 0 - w (n - 1)) (w l - w (n - 1)))
    (hfan : ∀ k, 1 ≤ k → k + 2 ≤ n → 0 < rcross (w (k + 1) - w k) (w 0 - w k))
    (h01 : ∀ k, 2 ≤ k → k ≤ n - 1 → 0 < rcross (w 1 - w 0) (w k - w 0)) :
    volume (convexHull ℝ (w '' Set.Iio n))
      = ∑ k ∈ Finset.Ico 1 (n - 1),
          ENNReal.ofReal (rcross (w k - w 0) (w (k + 1) - w 0) / 2) := by
  classical
  have hcons : ∀ k, 1 ≤ k → k + 2 ≤ n → 0 < rcross (w k - w 0) (w (k + 1) - w 0) := by
    intro k hk1 hk2
    have h := hfan k hk1 hk2
    rwa [← rcross_cycle (w 0) (w k) (w (k + 1))] at h
  have hdiag := fan_diag_pos w n h01 hcons
  -- the decomposition into fan triangles
  have hdecomp : convexHull ℝ (w '' Set.Iio n)
      = ⋃ k ∈ Finset.Ico 1 (n - 1), convexHull ℝ ({w 0, w k, w (k + 1)} : Set ℝ²) := by
    apply Set.Subset.antisymm
    · intro v hv
      have hedgev : ∀ k, k + 1 < n → 0 ≤ rcross (w (k + 1) - w k) (v - w k) := by
        intro k hk
        exact convexHull_subset_halfplane (w (k + 1) - w k) (w k)
          (by rintro y ⟨l, hl, rfl⟩; exact hVedge k l hk hl) hv
      have hclosev : 0 ≤ rcross (w 0 - w (n - 1)) (v - w (n - 1)) :=
        convexHull_subset_halfplane (w 0 - w (n - 1)) (w (n - 1))
          (by rintro y ⟨l, hl, rfl⟩; exact hVclose l hl) hv
      exact mem_iUnion_fan w v n hn hedgev hclosev hfan
    · refine Set.iUnion₂_subset fun k hk => ?_
      refine convexHull_mono ?_
      rintro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      simp only [Finset.mem_Ico] at hk
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, Set.mem_Iio.mpr (by omega), rfl⟩
      · exact ⟨k, Set.mem_Iio.mpr (by omega), rfl⟩
      · exact ⟨k + 1, Set.mem_Iio.mpr (by omega), rfl⟩
  -- pairwise null overlaps, separated by the diagonal through `w 0, w (k+1)`
  have key : ∀ k l, 1 ≤ k → k < l → l < n - 1 →
      volume (convexHull ℝ ({w 0, w k, w (k + 1)} : Set ℝ²)
        ∩ convexHull ℝ ({w 0, w l, w (l + 1)} : Set ℝ²)) = 0 := by
    intro k l hk1 hkl hl
    have hd0 : w (k + 1) - w 0 ≠ 0 := by
      intro h0
      have h := hcons k hk1 (by omega)
      rw [h0, rcross_zero_right] at h
      exact lt_irrefl _ h
    have hT1 : convexHull ℝ ({w 0, w k, w (k + 1)} : Set ℝ²)
        ⊆ {y : ℝ² | 0 ≤ rcross (w 0 - w (k + 1)) (y - w 0)} := by
      refine convexHull_subset_halfplane _ _ ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · rw [sub_self, rcross_zero_right]
      · have h := hcons k hk1 (by omega)
        have heq : rcross (w 0 - w (k + 1)) (w k - w 0)
            = rcross (w k - w 0) (w (k + 1) - w 0) := by
          simp only [rcross, PiLp.sub_apply]
          ring
        rw [heq]
        exact h.le
      · have heq : rcross (w 0 - w (k + 1)) (w (k + 1) - w 0) = 0 := by
          simp only [rcross, PiLp.sub_apply]
          ring
        exact le_of_eq heq.symm
    have hT2 : convexHull ℝ ({w 0, w l, w (l + 1)} : Set ℝ²)
        ⊆ {y : ℝ² | 0 ≤ rcross (w (k + 1) - w 0) (y - w 0)} := by
      refine convexHull_subset_halfplane _ _ ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · rw [sub_self, rcross_zero_right]
      · rcases eq_or_lt_of_le (show k + 1 ≤ l by omega) with heq | hlt
        · rw [← heq]
          have hz : rcross (w (k + 1) - w 0) (w (k + 1) - w 0) = 0 := by
            simp only [rcross, PiLp.sub_apply]
            ring
          exact le_of_eq hz.symm
        · exact (hdiag l (k + 1) (by omega) hlt (by omega)).le
      · exact (hdiag (l + 1) (k + 1) (by omega) (by omega) (by omega)).le
    refine measure_mono_null (fun y hy => ?_) (volume_line (w 0) (w (k + 1) - w 0) hd0)
    obtain ⟨hy1, hy2⟩ := hy
    have h1 : 0 ≤ rcross (w 0 - w (k + 1)) (y - w 0) := hT1 hy1
    have h2 : 0 ≤ rcross (w (k + 1) - w 0) (y - w 0) := hT2 hy2
    have hflip : rcross (w 0 - w (k + 1)) (y - w 0)
        = -rcross (w (k + 1) - w 0) (y - w 0) := by
      simp only [rcross, PiLp.sub_apply]
      ring
    rw [hflip] at h1
    simp only [Set.mem_setOf_eq]
    linarith
  have hpair : (↑(Finset.Ico 1 (n - 1)) : Set ℕ).Pairwise
      (Function.onFun (MeasureTheory.AEDisjoint volume)
        fun k => convexHull ℝ ({w 0, w k, w (k + 1)} : Set ℝ²)) := by
    intro k hk l hl hkl
    simp only [Finset.coe_Ico, Set.mem_Ico] at hk hl
    rcases lt_or_gt_of_ne hkl with h | h
    · exact key k l hk.1 h hl.2
    · exact MeasureTheory.AEDisjoint.symm (key l k hl.1 h hk.2)
  have hmeasT : ∀ k ∈ Finset.Ico 1 (n - 1),
      NullMeasurableSet (convexHull ℝ ({w 0, w k, w (k + 1)} : Set ℝ²)) volume := by
    intro k _
    exact ((Set.Finite.isCompact_convexHull ℝ
      (((Set.finite_singleton (w (k + 1))).insert (w k)).insert
        (w 0))).isClosed.measurableSet).nullMeasurableSet
  rw [hdecomp, measure_biUnion_finset₀ hpair hmeasT]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Ico] at hk
  rw [volume_triangle (w 0) (w k) (w (k + 1)), abs_of_pos (hcons k hk.1 (by omega))]

/-! ### The shoelace formula as an indexed sum

`shoelaceArea` folds over the consecutive pairs of the cyclically closed
vertex list; here we rewrite it as an indexed `Finset` sum and telescope the
cyclic sum into the fan sum from vertex `0`. -/

/-- The shoelace fold over consecutive pairs of a list, as an indexed sum. -/
private lemma foldl_shoelace_aux :
    ∀ (l : List (Point ℚ)) (c : ℚ),
    (List.zip l l.tail).foldl
        (fun acc pq => acc + (pq.1 0 * pq.2 1 - pq.2 0 * pq.1 1)) c
      = c + ∑ k ∈ Finset.range (l.length - 1),
          ((l.getD k ![0, 0]) 0 * (l.getD (k + 1) ![0, 0]) 1
            - (l.getD (k + 1) ![0, 0]) 0 * (l.getD k ![0, 0]) 1) := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    intro c
    cases t with
    | nil => simp
    | cons b t' =>
      simp only [List.tail_cons] at ih ⊢
      rw [List.zip_cons_cons, List.foldl_cons, ih]
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

/-- `shoelaceArea` as an indexed sum over the vertex list, with the closing
edge separated out. -/
private lemma shoelaceArea_eq_sum (l : List (Point ℚ)) (h3 : 3 ≤ l.length) :
    shoelaceArea l
      = |(∑ k ∈ Finset.range (l.length - 1),
            Point.crossProduct (l.getD k ![0, 0]) (l.getD (k + 1) ![0, 0]))
          + Point.crossProduct (l.getD (l.length - 1) ![0, 0]) (l.getD 0 ![0, 0])| / 2 := by
  simp only [shoelaceArea]
  rw [if_neg (by omega), foldl_shoelace_aux, zero_add]
  congr 1
  · congr 1
    have hlen : (l ++ [l.headD ![0, 0]]).length - 1 = l.length := by
      simp
    rw [hlen]
    have hsplit : l.length = (l.length - 1) + 1 := by omega
    rw [hsplit, Finset.sum_range_succ, ← hsplit]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_range] at hk
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
        Point.crossProduct]
      ring
    · rw [List.getD_append _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (le_refl l.length), Nat.sub_self]
      have hheadD : ([l.headD ![0, 0]].getD 0 ![0, 0]) = l.getD 0 ![0, 0] := by
        cases l with
        | nil => rfl
        | cons a t => rfl
      rw [hheadD, Point.crossProduct]
      ring

/-- Expansion of the based cross product. -/
private lemma crossProduct_sub_sub (a b c : Point ℚ) :
    Point.crossProduct (a - c) (b - c)
      = Point.crossProduct a b + Point.crossProduct c a - Point.crossProduct c b := by
  simp only [Point.crossProduct, Pi.sub_apply]
  ring

/-- **Telescoping**: the fan sum from vertex `0` equals the cyclic shoelace
sum. -/
private lemma fan_sum_eq_cyclic (v : ℕ → Point ℚ) (n : ℕ) (hn : 3 ≤ n) :
    (∑ k ∈ Finset.Ico 1 (n - 1), Point.crossProduct (v k - v 0) (v (k + 1) - v 0))
      = (∑ k ∈ Finset.range (n - 1), Point.crossProduct (v k) (v (k + 1)))
        + Point.crossProduct (v (n - 1)) (v 0) := by
  have hexp : (∑ k ∈ Finset.Ico 1 (n - 1),
        Point.crossProduct (v k - v 0) (v (k + 1) - v 0))
      = ∑ k ∈ Finset.Ico 1 (n - 1), (Point.crossProduct (v k) (v (k + 1))
          + (Point.crossProduct (v 0) (v k) - Point.crossProduct (v 0) (v (k + 1)))) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [crossProduct_sub_sub]
    ring
  rw [hexp, Finset.sum_add_distrib]
  have htel : (∑ k ∈ Finset.Ico 1 (n - 1),
        (Point.crossProduct (v 0) (v k) - Point.crossProduct (v 0) (v (k + 1))))
      = Point.crossProduct (v 0) (v 1) - Point.crossProduct (v 0) (v (n - 1)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h1 : ∀ i, 1 + i = i + 1 := fun i => by omega
    calc (∑ k ∈ Finset.range (n - 1 - 1),
            (Point.crossProduct (v 0) (v (1 + k))
              - Point.crossProduct (v 0) (v (1 + k + 1))))
        = Point.crossProduct (v 0) (v (1 + 0))
            - Point.crossProduct (v 0) (v (1 + (n - 1 - 1))) := by
          exact Finset.sum_range_sub' (fun k => Point.crossProduct (v 0) (v (1 + k))) _
      _ = Point.crossProduct (v 0) (v 1) - Point.crossProduct (v 0) (v (n - 1)) := by
          rw [show 1 + 0 = 1 by omega, show 1 + (n - 1 - 1) = n - 1 by omega]
  rw [htel]
  have hfirst : (∑ k ∈ Finset.range (n - 1), Point.crossProduct (v k) (v (k + 1)))
      = Point.crossProduct (v 0) (v 1)
        + ∑ k ∈ Finset.Ico 1 (n - 1), Point.crossProduct (v k) (v (k + 1)) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  rw [hfirst]
  have hanti : Point.crossProduct (v (n - 1)) (v 0)
      = -Point.crossProduct (v 0) (v (n - 1)) := by
    simp only [Point.crossProduct]
    ring
  rw [hanti]
  ring

/-- **Area bridge.** The Lebesgue area of the real region of a rational convex
polygon is its (rational, shoelace) `area`: the real hull decomposes into the
fan triangles from vertex `0` (`volume_convexHull_fan`), whose volumes sum to
the fan cross-product sum, which telescopes into the shoelace formula
(`fan_sum_eq_cyclic`, `shoelaceArea_eq_sum`). -/
theorem volume_realHull (poly : ConvexPolygon ℚ) :
    volume poly.realHull = ENNReal.ofReal (poly.area : ℝ) := by
  classical
  haveI := poly.vertex_count_pos
  have hn3 : 3 ≤ poly.vertex_count := poly.three_le_vertex_count
  have hpos : 0 < poly.vertex_count := by omega
  set wV : ℕ → Point ℚ :=
    fun k => poly.vertices ⟨k % poly.vertex_count, Nat.mod_lt _ hpos⟩ with hwV
  have hVk : ∀ (k : ℕ) (hk : k < poly.vertex_count), wV k = poly.vertices ⟨k, hk⟩ := by
    intro k hk
    simp only [hwV]
    exact congrArg poly.vertices (Fin.ext (Nat.mod_eq_of_lt hk))
  have hwn0 : wV poly.vertex_count = wV 0 := by
    simp only [hwV]
    exact congrArg poly.vertices (Fin.ext
      (show poly.vertex_count % poly.vertex_count = 0 % poly.vertex_count by simp))
  -- the strict counterclockwise conditions, in cyclic `ℕ`-indexed form
  have hccwQ : ∀ k l : ℕ, k < poly.vertex_count → l < poly.vertex_count →
      l ≠ k → l ≠ (k + 1) % poly.vertex_count →
      0 < Point.crossProduct (wV (k + 1) - wV k) (wV l - wV k) := by
    intro k l hk hl hlk hlk1
    have hccw := poly.vertices_extremePoints ⟨k, hk⟩ ⟨l, hl⟩
      (Fin.ne_of_val_ne (show l ≠ k from hlk))
      (by
        refine Fin.ne_of_val_ne ?_
        change l ≠ _
        rw [Fin.val_add, Fin.val_one',
          Nat.mod_eq_of_lt (show 1 < poly.vertex_count by omega)]
        exact hlk1)
    simp only [Point.ccw, Point.isStrictlyLeftOf, decide_eq_true_eq] at hccw
    have e1 : poly.vertices (⟨k, hk⟩ + 1) = wV (k + 1) := by
      simp only [hwV]
      refine congrArg poly.vertices (Fin.ext ?_)
      rw [Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt (show 1 < poly.vertex_count by omega)]
    have e2 : poly.vertices ⟨k, hk⟩ = wV k := (hVk k hk).symm
    have e3 : poly.vertices ⟨l, hl⟩ = wV l := (hVk l hl).symm
    rwa [e1, e2, e3] at hccw
  have hcross0 : ∀ d : Point ℚ, Point.crossProduct d 0 = 0 := by
    intro d
    simp [Point.crossProduct]
  have hcrossSelf : ∀ d : Point ℚ, Point.crossProduct d d = 0 := by
    intro d
    simp only [Point.crossProduct]
    ring
  -- the four hypotheses of the fan decomposition, over `ℚ`
  have hVedgeQ : ∀ k l, k + 1 < poly.vertex_count → l < poly.vertex_count →
      0 ≤ Point.crossProduct (wV (k + 1) - wV k) (wV l - wV k) := by
    intro k l hk hl
    rcases eq_or_ne l k with rfl | hlk
    · simp [hcross0]
    rcases eq_or_ne l (k + 1) with rfl | hlk1
    · simp [hcrossSelf]
    · exact (hccwQ k l (by omega) hl hlk (by rwa [Nat.mod_eq_of_lt (by omega)])).le
  have hVcloseQ : ∀ l, l < poly.vertex_count →
      0 ≤ Point.crossProduct (wV 0 - wV (poly.vertex_count - 1))
        (wV l - wV (poly.vertex_count - 1)) := by
    intro l hl
    have hkey := hccwQ (poly.vertex_count - 1) l (by omega) hl
    rw [show poly.vertex_count - 1 + 1 = poly.vertex_count by omega, Nat.mod_self,
      hwn0] at hkey
    rcases eq_or_ne l (poly.vertex_count - 1) with rfl | hlk
    · simp [hcross0]
    rcases eq_or_ne l 0 with rfl | hl0
    · simp [hcrossSelf]
    · exact (hkey hlk hl0).le
  have hfanQ : ∀ k, 1 ≤ k → k + 2 ≤ poly.vertex_count →
      0 < Point.crossProduct (wV (k + 1) - wV k) (wV 0 - wV k) := by
    intro k hk1 hk2
    exact hccwQ k 0 (by omega) (by omega) (by omega)
      (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
  have h01Q : ∀ k, 2 ≤ k → k ≤ poly.vertex_count - 1 →
      0 < Point.crossProduct (wV 1 - wV 0) (wV k - wV 0) := by
    intro k hk2 hk
    have h := hccwQ 0 k (by omega) (by omega) (by omega)
      (by rw [Nat.mod_eq_of_lt (by omega)]; omega)
    simpa using h
  have hconsQ : ∀ k, 1 ≤ k → k + 2 ≤ poly.vertex_count →
      0 < Point.crossProduct (wV k - wV 0) (wV (k + 1) - wV 0) := by
    intro k hk1 hk2
    have h := hfanQ k hk1 hk2
    have hcyc : Point.crossProduct (wV k - wV 0) (wV (k + 1) - wV 0)
        = Point.crossProduct (wV (k + 1) - wV k) (wV 0 - wV k) := by
      simp only [Point.crossProduct, Pi.sub_apply]
      ring
    rwa [hcyc]
  -- transfer to the real plane
  have hVedgeR : ∀ k l, k + 1 < poly.vertex_count → l < poly.vertex_count →
      0 ≤ rcross (Point.toEuclidean (wV (k + 1)) - Point.toEuclidean (wV k))
        (Point.toEuclidean (wV l) - Point.toEuclidean (wV k)) := by
    intro k l hk hl
    rw [rcross_toEuclidean]
    exact_mod_cast hVedgeQ k l hk hl
  have hVcloseR : ∀ l, l < poly.vertex_count →
      0 ≤ rcross (Point.toEuclidean (wV 0)
          - Point.toEuclidean (wV (poly.vertex_count - 1)))
        (Point.toEuclidean (wV l)
          - Point.toEuclidean (wV (poly.vertex_count - 1))) := by
    intro l hl
    rw [rcross_toEuclidean]
    exact_mod_cast hVcloseQ l hl
  have hfanR : ∀ k, 1 ≤ k → k + 2 ≤ poly.vertex_count →
      0 < rcross (Point.toEuclidean (wV (k + 1)) - Point.toEuclidean (wV k))
        (Point.toEuclidean (wV 0) - Point.toEuclidean (wV k)) := by
    intro k h1 h2
    rw [rcross_toEuclidean]
    exact_mod_cast hfanQ k h1 h2
  have h01R : ∀ k, 2 ≤ k → k ≤ poly.vertex_count - 1 →
      0 < rcross (Point.toEuclidean (wV 1) - Point.toEuclidean (wV 0))
        (Point.toEuclidean (wV k) - Point.toEuclidean (wV 0)) := by
    intro k h1 h2
    rw [rcross_toEuclidean]
    exact_mod_cast h01Q k h1 h2
  -- apply the fan decomposition
  have himg : (fun k => Point.toEuclidean (wV k)) '' Set.Iio poly.vertex_count
      = Set.range (fun i => Point.toEuclidean (poly.vertices i)) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k % poly.vertex_count, Nat.mod_lt _ hpos⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, congrArg (fun j => Point.toEuclidean (poly.vertices j))
        (Fin.ext (Nat.mod_eq_of_lt i.isLt))⟩
  have hvol := volume_convexHull_fan (fun k => Point.toEuclidean (wV k))
    poly.vertex_count hn3 hVedgeR hVcloseR hfanR h01R
  rw [ConvexPolygon.realHull, ← himg, hvol]
  -- identify the vertex list entries with `wV`
  have hlen : poly.vertex_list.length = poly.vertex_count := by
    simp [ConvexPolygon.vertex_list]
  have hgetD : ∀ k, k < poly.vertex_count →
      poly.vertex_list.getD k ![0, 0] = wV k := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by omega), hVk k hk]
    simp [ConvexPolygon.vertex_list]
  -- the rational area as the fan sum
  have hareaQ : poly.area
      = (∑ k ∈ Finset.Ico 1 (poly.vertex_count - 1),
          Point.crossProduct (wV k - wV 0) (wV (k + 1) - wV 0)) / 2 := by
    rw [ConvexPolygon.area, shoelaceArea_eq_sum poly.vertex_list (by omega), hlen]
    have hcyc : (∑ k ∈ Finset.range (poly.vertex_count - 1),
          Point.crossProduct (poly.vertex_list.getD k ![0, 0])
            (poly.vertex_list.getD (k + 1) ![0, 0]))
          + Point.crossProduct
              (poly.vertex_list.getD (poly.vertex_count - 1) ![0, 0])
              (poly.vertex_list.getD 0 ![0, 0])
        = (∑ k ∈ Finset.range (poly.vertex_count - 1),
            Point.crossProduct (wV k) (wV (k + 1)))
          + Point.crossProduct (wV (poly.vertex_count - 1)) (wV 0) := by
      congr 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_range] at hk
        rw [hgetD k (by omega), hgetD (k + 1) (by omega)]
      · rw [hgetD _ (by omega), hgetD 0 (by omega)]
    rw [hcyc, ← fan_sum_eq_cyclic wV poly.vertex_count hn3,
      abs_of_nonneg (Finset.sum_nonneg fun k hk => by
        simp only [Finset.mem_Ico] at hk
        exact (hconsQ k hk.1 (by omega)).le)]
  -- assemble
  have hLHS : (∑ k ∈ Finset.Ico 1 (poly.vertex_count - 1),
        ENNReal.ofReal (rcross
          (Point.toEuclidean (wV k) - Point.toEuclidean (wV 0))
          (Point.toEuclidean (wV (k + 1)) - Point.toEuclidean (wV 0)) / 2))
      = ∑ k ∈ Finset.Ico 1 (poly.vertex_count - 1),
          ENNReal.ofReal
            (((Point.crossProduct (wV k - wV 0) (wV (k + 1) - wV 0) : ℚ) : ℝ) / 2) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rcross_toEuclidean]
  rw [hLHS, ← ENNReal.ofReal_sum_of_nonneg (fun k hk => by
    simp only [Finset.mem_Ico] at hk
    have h := hconsQ k hk.1 (by omega)
    have : (0 : ℝ) ≤ ((Point.crossProduct (wV k - wV 0) (wV (k + 1) - wV 0) : ℚ) : ℝ) := by
      exact_mod_cast h.le
    linarith)]
  congr 1
  rw [← Finset.sum_div, hareaQ]
  push_cast
  ring

/-- `poly` is the convex hull of a genuine worm: some `1`-Lipschitz curve
`[0,1] → ℝ²` whose range has convex hull exactly `poly.realHull`. This is the
hypothesis under which adjoining `poly` to the working set (`wormAdding`) is
sound: every worm cover must cover such a curve, hence — being convex — contain
an isometric copy of `poly.realHull`. -/
def IsWormHull (poly : ConvexPolygon ℚ) : Prop :=
  ∃ w ∈ Worms, convexHull ℝ w = poly.realHull

end ConvexPolygon

namespace Moser

/-- `InitialWorm` (the isoceles right triangle with legs `1/2`) is the convex hull
of a genuine worm: the L-shaped unit-length path `(0,1/2) → (0,0) → (1/2,0)`,
parametrized by arc length. -/
theorem initialWorm_isWormHull : InitialWorm.IsWormHull := by
  -- The three vertices of `InitialWorm` in the real plane.
  set A : ℝ² := WithLp.toLp 2 ![0, 1 / 2] with hA
  set O : ℝ² := WithLp.toLp 2 ![0, 0] with hO
  set B : ℝ² := WithLp.toLp 2 ![1 / 2, 0] with hB
  -- The L-shaped path by arc length: down the `y`-axis, then out the `x`-axis.
  set f : Set.Icc (0 : ℝ) 1 → ℝ² :=
    fun t => WithLp.toLp 2 ![max 0 (t.1 - 1 / 2), max 0 (1 / 2 - t.1)] with hfdef
  -- The coordinatewise square estimate behind the Lipschitz bound: at most one
  -- coordinate varies on each side of the corner, and the mixed case gains a
  -- nonnegative cross term.
  have hcoord : ∀ s t : ℝ,
      (max 0 (s - 1 / 2) - max 0 (t - 1 / 2)) ^ 2
        + (max 0 (1 / 2 - s) - max 0 (1 / 2 - t)) ^ 2 ≤ (s - t) ^ 2 := by
    intro s t
    rcases le_total s (1 / 2 : ℝ) with hs | hs <;> rcases le_total t (1 / 2 : ℝ) with ht | ht
    · rw [max_eq_left (show s - 1 / 2 ≤ (0 : ℝ) by linarith),
        max_eq_left (show t - 1 / 2 ≤ (0 : ℝ) by linarith),
        max_eq_right (show (0 : ℝ) ≤ 1 / 2 - s by linarith),
        max_eq_right (show (0 : ℝ) ≤ 1 / 2 - t by linarith)]
      nlinarith
    · rw [max_eq_left (show s - 1 / 2 ≤ (0 : ℝ) by linarith),
        max_eq_right (show (0 : ℝ) ≤ t - 1 / 2 by linarith),
        max_eq_right (show (0 : ℝ) ≤ 1 / 2 - s by linarith),
        max_eq_left (show 1 / 2 - t ≤ (0 : ℝ) by linarith)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ t - 1 / 2 by linarith)
        (show (0 : ℝ) ≤ 1 / 2 - s by linarith)]
    · rw [max_eq_right (show (0 : ℝ) ≤ s - 1 / 2 by linarith),
        max_eq_left (show t - 1 / 2 ≤ (0 : ℝ) by linarith),
        max_eq_left (show 1 / 2 - s ≤ (0 : ℝ) by linarith),
        max_eq_right (show (0 : ℝ) ≤ 1 / 2 - t by linarith)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ s - 1 / 2 by linarith)
        (show (0 : ℝ) ≤ 1 / 2 - t by linarith)]
    · rw [max_eq_right (show (0 : ℝ) ≤ s - 1 / 2 by linarith),
        max_eq_right (show (0 : ℝ) ≤ t - 1 / 2 by linarith),
        max_eq_left (show 1 / 2 - s ≤ (0 : ℝ) by linarith),
        max_eq_left (show 1 / 2 - t ≤ (0 : ℝ) by linarith)]
      nlinarith
  have hlip : LipschitzWith 1 f := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    rw [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq, EuclideanSpace.dist_eq,
      Fin.sum_univ_two,
      show |s.1 - t.1| = Real.sqrt ((s.1 - t.1) ^ 2) from (Real.sqrt_sq_eq_abs _).symm]
    refine Real.sqrt_le_sqrt ?_
    simp only [hfdef, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.dist_eq, sq_abs]
    exact hcoord s.1 t.1
  -- Explicit values of the path on each leg.
  have hfle : ∀ t : Set.Icc (0 : ℝ) 1, t.1 ≤ 1 / 2 →
      f t = WithLp.toLp 2 ![(0 : ℝ), 1 / 2 - t.1] := by
    intro t ht
    simp only [hfdef]
    refine congrArg _ (funext fun i => ?_)
    fin_cases i
    · exact max_eq_left (by linarith)
    · exact max_eq_right (by linarith)
  have hfge : ∀ t : Set.Icc (0 : ℝ) 1, 1 / 2 ≤ t.1 →
      f t = WithLp.toLp 2 ![t.1 - 1 / 2, (0 : ℝ)] := by
    intro t ht
    simp only [hfdef]
    refine congrArg _ (funext fun i => ?_)
    fin_cases i
    · exact max_eq_right (by linarith)
    · exact max_eq_left (by linarith)
  -- The range of the path is the union of the two legs.
  have hrange : Set.range f = segment ℝ A O ∪ segment ℝ O B := by
    ext x
    simp only [Set.mem_range, Set.mem_union, segment, Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, rfl⟩
      rcases le_total t.1 (1 / 2 : ℝ) with ht | ht
      · refine Or.inl ⟨1 - 2 * t.1, 2 * t.1, by linarith, by linarith [t.2.1],
          by ring, ?_⟩
        rw [hfle t ht]
        simp only [hA, hO, ← WithLp.toLp_smul, ← WithLp.toLp_add]
        refine congrArg _ (funext fun i => ?_)
        fin_cases i <;> simp <;> ring
      · refine Or.inr ⟨2 - 2 * t.1, 2 * t.1 - 1, by linarith [t.2.2], by linarith,
          by ring, ?_⟩
        rw [hfge t ht]
        simp only [hB, hO, ← WithLp.toLp_smul, ← WithLp.toLp_add]
        refine congrArg _ (funext fun i => ?_)
        fin_cases i <;> simp <;> ring
    · rintro (⟨u, v, hu, hv, huv, rfl⟩ | ⟨u, v, hu, hv, huv, rfl⟩)
      · refine ⟨⟨v / 2, by constructor <;> linarith⟩, ?_⟩
        rw [hfle _ (show v / 2 ≤ (1 : ℝ) / 2 by linarith)]
        simp only [hA, hO, ← WithLp.toLp_smul, ← WithLp.toLp_add]
        refine congrArg _ (funext fun i => ?_)
        fin_cases i <;> simp <;> linarith
      · refine ⟨⟨1 / 2 + v / 2, by constructor <;> linarith⟩, ?_⟩
        rw [hfge _ (show (1 : ℝ) / 2 ≤ 1 / 2 + v / 2 by linarith)]
        simp only [hB, hO, ← WithLp.toLp_smul, ← WithLp.toLp_add]
        refine congrArg _ (funext fun i => ?_)
        fin_cases i <;> simp <;> linarith
  refine ⟨Set.range f, ⟨f, hlip, rfl⟩, ?_⟩
  -- The hull of the two legs is the hull of the three vertices.
  rw [hrange, ← convexHull_pair (𝕜 := ℝ) A O, ← convexHull_pair (𝕜 := ℝ) O B,
    convexHull_convexHull_union_left, convexHull_convexHull_union_right,
    show ({A, O} : Set ℝ²) ∪ {O, B} = {A, O, B} by
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto]
  unfold ConvexPolygon.realHull
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl | rfl)
    · refine ⟨⟨2, by decide⟩, ?_⟩
      rw [hA]
      change Point.toEuclidean ![0, 1 / 2] = _
      norm_num [Point.toEuclidean]
    · refine ⟨⟨0, by decide⟩, ?_⟩
      rw [hO]
      change Point.toEuclidean ![0, 0] = _
      norm_num [Point.toEuclidean]
    · refine ⟨⟨1, by decide⟩, ?_⟩
      rw [hB]
      change Point.toEuclidean ![1 / 2, 0] = _
      norm_num [Point.toEuclidean]
  · rintro ⟨i, rfl⟩
    fin_cases i
    · refine Or.inr (Or.inl ?_)
      rw [hO]
      change Point.toEuclidean ![0, 0] = _
      norm_num [Point.toEuclidean]
    · refine Or.inr (Or.inr ?_)
      rw [hB]
      change Point.toEuclidean ![1 / 2, 0] = _
      norm_num [Point.toEuclidean]
    · refine Or.inl ?_
      rw [hA]
      change Point.toEuclidean ![0, 1 / 2] = _
      norm_num [Point.toEuclidean]

/-! ## Points outside `LocationRange` exceed the area threshold

`LocationRange` is the hexagon of points that may be added to `InitialWorm`
without pushing the area of the convex hull above `areaThreshold`. The theorem
below is its defining property, proved in the real plane: for each of the six
directed edges of the hexagon, a point beyond that edge spans, together with one
or two triangles of `InitialWorm`, an area exceeding the threshold. -/

section OutsideLocationRange

open ConvexPolygon

lemma toEuclidean_apply (q : Point ℚ) (i : Fin 2) :
    Point.toEuclidean q i = ((q i : ℚ) : ℝ) := by
  fin_cases i <;> simp [Point.toEuclidean]

/-- A triangle spanned by three points of a convex set bounds its volume. -/
lemma volume_triangle_le {S : Set ℝ²} (hS : Convex ℝ S) {a b c : ℝ²}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    ENNReal.ofReal (|rcross (b - a) (c - a)| / 2) ≤ volume S := by
  rw [← volume_triangle]
  refine measure_mono (convexHull_min ?_ hS)
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl <;> assumption

/-- Two triangles of a convex set separated by a line bound its volume
additively: they meet only inside the line, which is null. -/
lemma volume_two_triangles_le {S : Set ℝ²} (hS : Convex ℝ S)
    {a b c a' b' c' d w : ℝ²} (hd : d ≠ 0)
    (h1 : ∀ z ∈ ({a, b, c} : Set ℝ²), 0 ≤ rcross d (z - w))
    (h2 : ∀ z ∈ ({a', b', c'} : Set ℝ²), rcross d (z - w) ≤ 0)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (ha' : a' ∈ S) (hb' : b' ∈ S) (hc' : c' ∈ S) :
    ENNReal.ofReal (|rcross (b - a) (c - a)| / 2)
        + ENNReal.ofReal (|rcross (b' - a') (c' - a')| / 2) ≤ volume S := by
  have hneg : ∀ u v : ℝ², rcross (-u) v = -rcross u v := by
    intro u v; simp only [rcross, PiLp.neg_apply]; ring
  have hT1 : convexHull ℝ ({a, b, c} : Set ℝ²) ⊆ {z : ℝ² | 0 ≤ rcross d (z - w)} :=
    convexHull_subset_halfplane d w h1
  have hT2 : convexHull ℝ ({a', b', c'} : Set ℝ²) ⊆ {z : ℝ² | rcross d (z - w) ≤ 0} := by
    have := convexHull_subset_halfplane (-d) w (by
      intro z hz; rw [hneg]; linarith [h2 z hz])
    intro z hz
    have hz' := this hz
    simp only [Set.mem_setOf_eq, hneg] at hz' ⊢
    linarith
  have hdisj : MeasureTheory.AEDisjoint volume (convexHull ℝ ({a, b, c} : Set ℝ²))
      (convexHull ℝ ({a', b', c'} : Set ℝ²)) := by
    refine measure_mono_null (fun z hz => ?_) (volume_line w d hd)
    obtain ⟨hz1, hz2⟩ := hz
    have e1 := hT1 hz1
    have e2 := hT2 hz2
    simp only [Set.mem_setOf_eq] at e1 e2 ⊢
    linarith
  have hmeas2 : NullMeasurableSet (convexHull ℝ ({a', b', c'} : Set ℝ²)) volume :=
    ((Set.Finite.isCompact_convexHull ℝ
      (((Set.finite_singleton c').insert b').insert a')).isClosed.measurableSet).nullMeasurableSet
  have hsub : convexHull ℝ ({a, b, c} : Set ℝ²) ∪ convexHull ℝ ({a', b', c'} : Set ℝ²) ⊆ S := by
    refine Set.union_subset (convexHull_min ?_ hS) (convexHull_min ?_ hS) <;>
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl <;> assumption
  calc ENNReal.ofReal (|rcross (b - a) (c - a)| / 2)
        + ENNReal.ofReal (|rcross (b' - a') (c' - a')| / 2)
      = volume (convexHull ℝ ({a, b, c} : Set ℝ²))
          + volume (convexHull ℝ ({a', b', c'} : Set ℝ²)) := by
        rw [volume_triangle, volume_triangle]
    _ = volume (convexHull ℝ ({a, b, c} : Set ℝ²) ∪ convexHull ℝ ({a', b', c'} : Set ℝ²)) :=
        (measure_union₀ hmeas2 hdisj).symm
    _ ≤ volume S := measure_mono hsub

private lemma initialWorm_vertex_list :
    InitialWorm.vertex_list = [![0, 0], ![1 / 2, 0], ![0, 1 / 2]] := rfl

/-- **Defining property of `LocationRange`.** If `p` lies outside the hexagon
`LocationRange`, then the area of the convex hull of `p` together with the
vertices of `InitialWorm` strictly exceeds `areaThreshold`. -/
theorem lt_volume_convexHull_insert_initialWorm {p : Point ℚ}
    (hp : LocationRange.contains p = false) :
    ENNReal.ofReal ((areaThreshold : ℚ) : ℝ)
      < volume (convexHull ℝ
          (Point.toEuclidean '' {q : Point ℚ | q ∈ p :: InitialWorm.vertex_list})) := by
  set x : ℝ := ((p 0 : ℚ) : ℝ) with hxdef
  set y : ℝ := ((p 1 : ℚ) : ℝ) with hydef
  set S : Set ℝ² :=
    convexHull ℝ (Point.toEuclidean '' {q : Point ℚ | q ∈ p :: InitialWorm.vertex_list}) with hSdef
  have hconv : Convex ℝ S := convex_convexHull ℝ _
  have hmemG : ∀ q : Point ℚ, q ∈ p :: InitialWorm.vertex_list → Point.toEuclidean q ∈ S :=
    fun q hq => subset_convexHull ℝ _ ⟨q, hq, rfl⟩
  set O : ℝ² := Point.toEuclidean ![0, 0] with hOdef
  set V1 : ℝ² := Point.toEuclidean ![1 / 2, 0] with hV1def
  set V2 : ℝ² := Point.toEuclidean ![0, 1 / 2] with hV2def
  set P : ℝ² := Point.toEuclidean p with hPdef
  have hP : P ∈ S := hmemG p (by simp)
  have hO : O ∈ S := hmemG _ (by simp [initialWorm_vertex_list])
  have hV1 : V1 ∈ S := hmemG _ (by simp [initialWorm_vertex_list])
  have hV2 : V2 ∈ S := hmemG _ (by simp [initialWorm_vertex_list])
  have hO0 : O 0 = 0 := by rw [hOdef, toEuclidean_apply]; norm_num
  have hO1 : O 1 = 0 := by rw [hOdef, toEuclidean_apply]; norm_num
  have hV10 : V1 0 = 1 / 2 := by rw [hV1def, toEuclidean_apply]; norm_num
  have hV11 : V1 1 = 0 := by rw [hV1def, toEuclidean_apply]; norm_num
  have hV20 : V2 0 = 0 := by rw [hV2def, toEuclidean_apply]; norm_num
  have hV21 : V2 1 = 1 / 2 := by rw [hV2def, toEuclidean_apply]; norm_num
  have hP0 : P 0 = x := by rw [hPdef, toEuclidean_apply]
  have hP1 : P 1 = y := by rw [hPdef, toEuclidean_apply]
  -- numerical constants
  have hthr : ((areaThreshold : ℚ) : ℝ) = 232240 / 1000000 := by
    rw [areaThreshold]; norm_num
  have hoff : ((offset : ℚ) : ℝ) = 928960 / 1000000 := by
    rw [offset, areaThreshold]; norm_num
  have hnar : ((narrowOffset : ℚ) : ℝ) = 428960 / 1000000 := by
    rw [narrowOffset, offset, areaThreshold]; norm_num
  -- from `contains p = false`, one of the six half-space tests fails
  have hdisj : offset < p 0 ∨ offset < p 0 + p 1 ∨ offset < p 1 ∨
      p 0 < -narrowOffset ∨ p 0 + p 1 < -narrowOffset ∨ p 1 < -narrowOffset := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcon
    rw [Bool.eq_false_iff] at hp
    exact hp ((locationRange_contains_iff p).mpr ⟨c1, c2, c3, c4, c5, c6⟩)
  -- conclude from a real lower bound on the area
  have hfinal : ∀ A : ℝ, ((areaThreshold : ℚ) : ℝ) < A → ENNReal.ofReal A ≤ volume S →
      ENNReal.ofReal ((areaThreshold : ℚ) : ℝ) < volume S := by
    intro A hA hle
    refine lt_of_lt_of_le ?_ hle
    exact (ENNReal.ofReal_lt_ofReal_iff (by rw [hthr] at hA; linarith)).mpr hA
  rcases hdisj with hA | hB | hC | hD | hE | hF
  · -- `x > offset`: the triangle `O, P, V₂` already has area `x/4`
    have hx : 928960 / 1000000 < x := by rw [hxdef, ← hoff]; exact_mod_cast hA
    refine hfinal (x / 4) (by rw [hthr]; linarith) ?_
    have hval : rcross (P - O) (V2 - O) = x / 2 := by
      simp only [rcross, PiLp.sub_apply, hO0, hO1, hV20, hV21, hP0, hP1]; ring
    have hbound := volume_triangle_le hconv hO hP hV2
    rw [hval, abs_of_nonneg (by linarith : (0:ℝ) ≤ x / 2)] at hbound
    calc ENNReal.ofReal (x / 4) = ENNReal.ofReal (x / 2 / 2) := by congr 1; ring
      _ ≤ volume S := hbound
  · -- `x + y > offset`: `InitialWorm` plus the triangle beyond its hypotenuse
    have hxy : 928960 / 1000000 < x + y := by
      rw [hxdef, hydef, ← hoff]; exact_mod_cast hB
    refine hfinal ((x + y) / 4) (by rw [hthr]; linarith) ?_
    have hval1 : rcross (V1 - O) (V2 - O) = 1 / 4 := by
      simp only [rcross, PiLp.sub_apply, hO0, hO1, hV10, hV11, hV20, hV21]; ring
    have hval2 : rcross (V2 - V1) (P - V1) = 1 / 4 - (x + y) / 2 := by
      simp only [rcross, PiLp.sub_apply, hV10, hV11, hV20, hV21, hP0, hP1]; ring
    have hsep1 : ∀ z ∈ ({O, V1, V2} : Set ℝ²), 0 ≤ rcross (V2 - V1) (z - V1) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;>
        · simp only [rcross, PiLp.sub_apply, hO0, hO1, hV10, hV11, hV20, hV21]; norm_num
    have hsep2 : ∀ z ∈ ({V1, V2, P} : Set ℝ²), rcross (V2 - V1) (z - V1) ≤ 0 := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;>
        · simp only [rcross, PiLp.sub_apply, hV10, hV11, hV20, hV21, hP0, hP1]
          norm_num
          try linarith
    have hdne : V2 - V1 ≠ 0 := by
      intro hzero
      have h0 : (V2 - V1) 0 = 0 := by rw [hzero]; simp
      rw [PiLp.sub_apply, hV20, hV10] at h0
      norm_num at h0
    have hbound := volume_two_triangles_le hconv hdne hsep1 hsep2 hO hV1 hV2 hV1 hV2 hP
    rw [hval1, hval2, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/4),
      abs_of_nonpos (by linarith : (1:ℝ)/4 - (x + y)/2 ≤ 0)] at hbound
    refine le_trans (le_of_eq ?_) hbound
    rw [← ENNReal.ofReal_add (by norm_num) (by linarith)]
    congr 1
    ring
  · -- `y > offset`
    have hy : 928960 / 1000000 < y := by rw [hydef, ← hoff]; exact_mod_cast hC
    refine hfinal (y / 4) (by rw [hthr]; linarith) ?_
    have hval : rcross (V1 - O) (P - O) = y / 2 := by
      simp only [rcross, PiLp.sub_apply, hO0, hO1, hV10, hV11, hP0, hP1]; ring
    have hbound := volume_triangle_le hconv hO hV1 hP
    rw [hval, abs_of_nonneg (by linarith : (0:ℝ) ≤ y / 2)] at hbound
    calc ENNReal.ofReal (y / 4) = ENNReal.ofReal (y / 2 / 2) := by congr 1; ring
      _ ≤ volume S := hbound
  · -- `x < -narrowOffset`: `InitialWorm` plus the triangle to the left of the `y`-axis
    have hx : x < -(428960 / 1000000) := by rw [hxdef, ← hnar]; exact_mod_cast hD
    refine hfinal (1 / 8 + (-x) / 4) (by rw [hthr]; linarith) ?_
    have hval1 : rcross (V1 - O) (V2 - O) = 1 / 4 := by
      simp only [rcross, PiLp.sub_apply, hO0, hO1, hV10, hV11, hV20, hV21]; ring
    have hval2 : rcross (V2 - O) (P - O) = -(x / 2) := by
      simp only [rcross, PiLp.sub_apply, hO0, hO1, hV20, hV21, hP0, hP1]; ring
    have hsep1 : ∀ z ∈ ({O, V2, P} : Set ℝ²), 0 ≤ rcross (V2 - O) (z - O) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;>
        · simp only [rcross, PiLp.sub_apply, hO0, hO1, hV20, hV21, hP0, hP1]
          norm_num
          try linarith
    have hsep2 : ∀ z ∈ ({O, V1, V2} : Set ℝ²), rcross (V2 - O) (z - O) ≤ 0 := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;>
        · simp only [rcross, PiLp.sub_apply, hO0, hO1, hV10, hV11, hV20, hV21]; norm_num
    have hdne : V2 - O ≠ 0 := by
      intro hzero
      have h0 : (V2 - O) 1 = 0 := by rw [hzero]; simp
      rw [PiLp.sub_apply, hV21, hO1] at h0
      norm_num at h0
    have hbound := volume_two_triangles_le hconv hdne hsep1 hsep2 hO hV2 hP hO hV1 hV2
    rw [hval1, hval2, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/4),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ -(x / 2))] at hbound
    refine le_trans (le_of_eq ?_) hbound
    rw [← ENNReal.ofReal_add (by linarith) (by norm_num)]
    congr 1
    ring
  · -- `x + y < -narrowOffset`: the triangle `V₁, V₂, P` alone
    have hxy : x + y < -(428960 / 1000000) := by
      rw [hxdef, hydef, ← hnar]; exact_mod_cast hE
    refine hfinal (1 / 8 - (x + y) / 4) (by rw [hthr]; linarith) ?_
    have hval : rcross (V2 - V1) (P - V1) = 1 / 4 - (x + y) / 2 := by
      simp only [rcross, PiLp.sub_apply, hV10, hV11, hV20, hV21, hP0, hP1]; ring
    have hbound := volume_triangle_le hconv hV1 hV2 hP
    rw [hval, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 / 4 - (x + y) / 2)] at hbound
    refine le_trans (le_of_eq ?_) hbound
    congr 1
    ring
  · -- `y < -narrowOffset`: `InitialWorm` plus the triangle below the `x`-axis
    have hy : y < -(428960 / 1000000) := by rw [hydef, ← hnar]; exact_mod_cast hF
    refine hfinal (1 / 8 + (-y) / 4) (by rw [hthr]; linarith) ?_
    have hval1 : rcross (V1 - O) (V2 - O) = 1 / 4 := by
      simp only [rcross, PiLp.sub_apply, hO0, hO1, hV10, hV11, hV20, hV21]; ring
    have hval2 : rcross (V1 - O) (P - O) = y / 2 := by
      simp only [rcross, PiLp.sub_apply, hO0, hO1, hV10, hV11, hP0, hP1]; ring
    have hsep1 : ∀ z ∈ ({O, V1, V2} : Set ℝ²), 0 ≤ rcross (V1 - O) (z - O) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;>
        · simp only [rcross, PiLp.sub_apply, hO0, hO1, hV10, hV11, hV20, hV21]; norm_num
    have hsep2 : ∀ z ∈ ({O, V1, P} : Set ℝ²), rcross (V1 - O) (z - O) ≤ 0 := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;>
        · simp only [rcross, PiLp.sub_apply, hO0, hO1, hV10, hV11, hP0, hP1]
          norm_num
          try linarith
    have hdne : V1 - O ≠ 0 := by
      intro hzero
      have h0 : (V1 - O) 0 = 0 := by rw [hzero]; simp
      rw [PiLp.sub_apply, hV10, hO0] at h0
      norm_num at h0
    have hbound := volume_two_triangles_le hconv hdne hsep1 hsep2 hO hV1 hV2 hO hV1 hP
    rw [hval1, hval2, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/4),
      abs_of_nonpos (by linarith : y / 2 ≤ 0)] at hbound
    refine le_trans (le_of_eq ?_) hbound
    rw [← ENNReal.ofReal_add (by norm_num) (by linarith)]
    congr 1
    ring

/-- **The area threshold is exceeded, in the computational layer.** If `p` lies
outside `LocationRange` and the *verified* hull of `p` together with the vertices
of `InitialWorm` is `hull`, then `hull.area` exceeds `areaThreshold`.

The verified hull `ofListChecked` is essential: `convexHullPoints` alone is not
proved to compute the convex hull (see `convexHullPoints_convex`), so the
shoelace area of its output carries no information without the run-time check. -/
theorem areaThreshold_lt_area_of_ofListChecked {p : Point ℚ}
    (hp : LocationRange.contains p = false) {hull : ConvexPolygon ℚ}
    (h : ConvexPolygon.ofListChecked (p :: InitialWorm.vertex_list) = some hull) :
    areaThreshold < hull.area := by
  have hreal := ConvexPolygon.realHull_ofListChecked h
  have hvol := ConvexPolygon.volume_realHull hull
  have hlt := lt_volume_convexHull_insert_initialWorm hp
  rw [← hreal, hvol] at hlt
  have h2 : ((areaThreshold : ℚ) : ℝ) < ((hull.area : ℚ) : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num [areaThreshold])).mp hlt
  exact_mod_cast h2

end OutsideLocationRange

/-! ## Pinned small covers and the working-set invariants -/

/-- A **pinned small cover**: a convex set that covers every worm up to
orientation-preserving isometry, contains the *unshifted* `InitialWorm` region
(the pinning normalization of `Moser.Constants`), and has area at most
`areaThreshold`. The working-set algorithm's purpose is to show no such set
exists. -/
structure IsPinnedSmallCover (K : Set ℝ²) : Prop where
  /-- The cover is convex. -/
  convex : Convex ℝ K
  /-- The cover contains an isometric copy of every worm. -/
  covers : ∀ w ∈ Worms, CoversByIsometry K w
  /-- The cover contains the unshifted `InitialWorm` region. -/
  pinned : InitialWorm.realHull ⊆ K
  /-- The cover has area at most `areaThreshold`. -/
  small : volume K ≤ ENNReal.ofReal (areaThreshold : ℝ)

namespace WorkingSet

/-- **Invariant 2** of `Moser.Manipulation.Invariants`: every polygon of the
working set contains the unshifted `InitialWorm`. -/
def ContainsInitialWorm (s : WorkingSet) : Prop :=
  ∀ p ∈ s.polygons, InitialWorm.isSubsetOf p = true

/-- **Invariant 3** of `Moser.Manipulation.Invariants` — the soundness invariant.
Every pinned small cover contains, unshifted, the real region of some polygon of
the working set. Consequently an *empty* sound working set refutes the existence
of pinned small covers (`Moser.no_pinnedSmallCover_of_sound_of_empty`). -/
def Sound (s : WorkingSet) : Prop :=
  ∀ K : Set ℝ², IsPinnedSmallCover K → ∃ p ∈ s.polygons, p.realHull ⊆ K

/-- The initial working set satisfies Invariant 2. -/
theorem initial_containsInitialWorm : initial.ContainsInitialWorm := by
  intro p hp
  simp only [initial, List.mem_singleton] at hp
  subst hp
  native_decide

/-- The initial working set `[InitialWorm]` is sound: a pinned small cover
contains `InitialWorm.realHull` by definition of pinning. -/
theorem initial_sound : initial.Sound := by
  intro K hK
  exact ⟨InitialWorm, List.mem_singleton.mpr rfl, hK.pinned⟩

/-- `bigSetRemoval` preserves Invariant 2: it only removes polygons. -/
theorem ContainsInitialWorm.bigSetRemoval {s : WorkingSet} (hs : s.ContainsInitialWorm) :
    s.bigSetRemoval.ContainsInitialWorm := fun p hp => hs p (List.mem_filter.mp hp).1

/-- Every polygon retained by the `supersetRemoval` fold comes from the
accumulator or from the pending list. -/
private theorem mem_of_mem_foldl_supersetRemovalStep {q : ConvexPolygon ℚ}
    (l : List (ConvexPolygon ℚ)) : ∀ kept, q ∈ l.foldl supersetRemovalStep kept →
      q ∈ kept ∨ q ∈ l := by
  induction l with
  | nil => exact fun kept h => Or.inl (by simpa using h)
  | cons a l ih =>
    intro kept h
    rw [List.foldl_cons] at h
    rcases ih _ h with hq | hq
    · unfold supersetRemovalStep at hq
      split_ifs at hq with hc
      · exact Or.inl hq
      · rw [List.mem_append] at hq
        rcases hq with hq | hq
        · exact Or.inl (List.mem_filter.mp hq).1
        · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hq)))
    · exact Or.inr (List.mem_cons_of_mem a hq)

/-- `supersetRemoval` preserves Invariant 2: its output polygons all come from
the input. -/
theorem ContainsInitialWorm.supersetRemoval {s : WorkingSet} (hs : s.ContainsInitialWorm) :
    s.supersetRemoval.ContainsInitialWorm := by
  intro p hp
  rcases mem_of_mem_foldl_supersetRemovalStep s.polygons [] hp with h | h
  · simp at h
  · exact hs p h

/-- The composite cleanup pass preserves Invariant 2. -/
theorem ContainsInitialWorm.cleanup {s : WorkingSet} (hs : s.ContainsInitialWorm) :
    s.cleanup.ContainsInitialWorm := hs.bigSetRemoval.supersetRemoval

/-- `bigSetRemoval` preserves soundness: a polygon whose rational area exceeds
`areaThreshold` cannot fit inside a small cover, by the area bridge, so removing
such polygons never removes the witness. -/
theorem Sound.bigSetRemoval {s : WorkingSet} (hs : s.Sound) : s.bigSetRemoval.Sound := by
  intro K hK
  obtain ⟨p, hp, hpK⟩ := hs K hK
  refine ⟨p, List.mem_filter.mpr ⟨hp, ?_⟩, hpK⟩
  have hvol : volume p.realHull ≤ ENNReal.ofReal (areaThreshold : ℝ) :=
    le_trans (measure_mono hpK) hK.small
  rw [p.volume_realHull] at hvol
  have harea : (p.area : ℝ) ≤ (areaThreshold : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (by norm_num [areaThreshold])).mp hvol
  simpa using (by exact_mod_cast harea : p.area ≤ areaThreshold)

/-- The fold invariant behind `Sound.supersetRemoval`: each
`supersetRemovalStep` preserves the existence, among the retained and pending
polygons together, of a witness whose real region lies inside `K`. When the
step drops a polygon it is because a polygon contained in it (by `isSubsetOf`,
hence with smaller real region via the containment bridge
`ConvexPolygon.realHull_subset_realHull`) is retained in its stead. -/
private theorem exists_realHull_subset_foldl_supersetRemovalStep
    {K : Set ℝ²} (l kept : List (ConvexPolygon ℚ))
    (h : ∃ q ∈ kept ++ l, q.realHull ⊆ K) :
    ∃ q ∈ l.foldl supersetRemovalStep kept, q.realHull ⊆ K := by
  induction l generalizing kept with
  | nil => simpa using h
  | cons a l ih =>
    rw [List.foldl_cons]
    apply ih
    obtain ⟨q, hq, hqK⟩ := h
    rw [List.mem_append, List.mem_cons] at hq
    unfold supersetRemovalStep
    split_ifs with hc
    · -- some retained polygon is contained in `a`; `a` is dropped
      obtain ⟨q0, hq0, hq0a⟩ := List.any_eq_true.mp hc
      rcases hq with hq | rfl | hq
      · exact ⟨q, List.mem_append_left _ hq, hqK⟩
      · exact ⟨q0, List.mem_append_left _ hq0,
          (ConvexPolygon.realHull_subset_realHull hq0a).trans hqK⟩
      · exact ⟨q, List.mem_append_right _ hq, hqK⟩
    · -- `a` is retained; retained polygons containing `a` are dropped
      have haMem : a ∈ (kept.filter fun q => !a.isSubsetOf q) ++ [a] :=
        List.mem_append_right _ (List.mem_singleton.mpr rfl)
      rcases hq with hq | rfl | hq
      · by_cases haq : a.isSubsetOf q = true
        · exact ⟨a, List.mem_append_left _ haMem,
            (ConvexPolygon.realHull_subset_realHull haq).trans hqK⟩
        · refine ⟨q, List.mem_append_left _ (List.mem_append_left _ ?_), hqK⟩
          exact List.mem_filter.mpr ⟨hq, by simp [haq]⟩
      · exact ⟨q, List.mem_append_left _ haMem, hqK⟩
      · exact ⟨q, List.mem_append_right _ hq, hqK⟩

/-- `supersetRemoval` preserves soundness: whenever the step drops a witness
polygon, a polygon contained in it — hence itself inside the cover, by the
containment bridge `ConvexPolygon.realHull_subset_realHull` — is retained in
its stead (`exists_realHull_subset_foldl_supersetRemovalStep`). -/
theorem Sound.supersetRemoval {s : WorkingSet} (hs : s.Sound) : s.supersetRemoval.Sound := by
  intro K hK
  obtain ⟨p, hp, hpK⟩ := hs K hK
  exact exists_realHull_subset_foldl_supersetRemovalStep s.polygons []
    ⟨p, by simpa using hp, hpK⟩

/-- **`wormAdding` preserves soundness — the mathematical crux of the development.**

This is stated as a *hypothesis* rather than proved, and every result that needs
it carries it explicitly, so that the gap is visible in the statements rather
than hidden.

Intended argument: a pinned small cover `K` contains the real region of some
`p ∈ s.polygons` (by `hs`). Since `hw : w.IsWormHull`, `K` also covers a worm whose
hull is `w.realHull`, so by convexity `K` contains `g '' w.realHull` for some real
direct isometry `g`. Because `K` is pinned and small, `g` is confined to a compact
range of placements (the `LocationRange`/`distanceCutoff` reasoning of
`Moser.Constants`, whose defining property is now proved as
`Moser.lt_volume_convexHull_insert_initialWorm`). The discretization
`discretizeIsometries epsilon` must then contain a rational isometry close enough
to `g` that the `shrink epsilon`-shrunken copy of `w`, placed by it, lies inside
`g '' w.realHull ⊆ K`. Then `hull(p ∪ placed shrunken w) ⊆ K`, and that hull is an
element of `wormReplacement p w epsilon`.

**Warning — unverified quantitative claims.** The truth of this statement depends
on properties of the current implementations that have NOT been checked:
1. `discretizeIsometries epsilon` must cover the full confined range of rotations
   *and translations* at resolution matched to the `shrink` margin (cf. the TODO in
   `wormReplacement`).
2. The `shrink`-margin vs. grid-resolution accounting must work out; for worms with
   degenerate (lower-dimensional) hulls, e.g. segments, shrinking provides no
   margin and the argument fails — `w` may need a full-dimensional hull hypothesis.
3. `wormReplacement` silently drops candidates where `ConvexPolygon.ofList` returns
   `none`; soundness requires the needed candidate to survive.
Do not invest in proving this before validating the search computationally; expect
the statement to need additional hypotheses (or the implementation to need fixes)
discovered during that validation. -/
def WormAddingSound : Prop :=
  ∀ {s : WorkingSet}, s.Sound → ∀ {w : ConvexPolygon ℚ}, w.IsWormHull →
    ∀ {epsilon : ℚ} (heps : 0 < epsilon), (s.wormAdding w epsilon heps).Sound

/-- The composite cleanup pass preserves soundness. -/
theorem Sound.cleanup {s : WorkingSet} (hs : s.Sound) : s.cleanup.Sound :=
  hs.bigSetRemoval.supersetRemoval

/-- The main loop step `addWormAndCleanup` preserves soundness, given the crux
hypothesis `WormAddingSound`. -/
theorem Sound.addWormAndCleanup (hwa : WormAddingSound) {s : WorkingSet} (hs : s.Sound)
    {w : ConvexPolygon ℚ} (hw : w.IsWormHull) {epsilon : ℚ} (heps : 0 < epsilon) :
    (s.addWormAndCleanup w epsilon heps).Sound :=
  (hwa hs hw heps).cleanup

end WorkingSet

/-! ## From an empty sound working set to the lower bound -/

/-- An empty sound working set refutes every pinned small cover. -/
theorem no_pinnedSmallCover_of_sound_of_empty {s : WorkingSet} (hs : s.Sound)
    (he : s.polygons = []) (K : Set ℝ²) : ¬ IsPinnedSmallCover K := by
  intro hK
  obtain ⟨p, hp, -⟩ := hs K hK
  rw [he] at hp
  simp at hp

/-- Orientation-preserving isometries are closed under composition: determinants
multiply and translations accumulate. -/
private lemma isOrientationPreservingIsometry_comp {g₁ g₂ : ℝ² → ℝ²}
    (h₁ : IsOrientationPreservingIsometry g₁) (h₂ : IsOrientationPreservingIsometry g₂) :
    IsOrientationPreservingIsometry (g₁ ∘ g₂) := by
  obtain ⟨e₁, v₁, hdet₁, rfl⟩ := h₁
  obtain ⟨e₂, v₂, hdet₂, rfl⟩ := h₂
  refine ⟨e₂.trans e₁, e₁ v₂ + v₁, ?_, ?_⟩
  · rw [show (e₂.trans e₁).toLinearEquiv = e₁.toLinearEquiv * e₂.toLinearEquiv from rfl,
      map_mul, hdet₁, hdet₂, one_mul]
  · funext x
    simp [add_assoc]

/-- **Un-pinning.** Any convex set of area at most `areaThreshold` covering all
worms can be moved by a direct isometry to a pinned small cover: it covers the
L-shaped worm of `Moser.initialWorm_isWormHull`, and the placed copy `g '' K`
of the cover over that worm is pinned, while remaining convex, covering (via
composition with the inverse placement), and of the same volume (direct
isometries preserve Lebesgue measure, and convex sets are null-measurable). -/
theorem exists_pinnedSmallCover {K : Set ℝ²} (hconv : Convex ℝ K)
    (hcov : ∀ w ∈ Worms, CoversByIsometry K w)
    (hsmall : volume K ≤ ENNReal.ofReal (areaThreshold : ℝ)) :
    ∃ K' : Set ℝ², IsPinnedSmallCover K' := by
  obtain ⟨w₀, hw₀, hhull⟩ := initialWorm_isWormHull
  obtain ⟨g, hg, hsub⟩ := hcov w₀ hw₀
  obtain ⟨g', hg', hleft, hright⟩ := hg.exists_symm
  -- The placed copy of the cover over the L-shaped worm is convex ...
  have hgK_convex : Convex ℝ (g '' K) := by
    obtain ⟨e, v, -, heq⟩ := hg
    rw [heq, show (fun x => e x + v) '' K = (fun y => v + y) '' (⇑e '' K) by
      rw [Set.image_image]; simp [add_comm]]
    exact (hconv.linear_image (e.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²)).translate v
  -- ... has the same volume as the cover ...
  have hvol : volume (g '' K) = volume K := by
    rw [Set.image_eq_preimage_of_inverse hleft hright]
    obtain ⟨e', v', -, heq'⟩ := hg'
    have hmp : MeasurePreserving g' (volume : Measure ℝ²) volume := by
      rw [heq']
      exact (measurePreserving_add_right volume v').comp e'.measurePreserving
    exact hmp.measure_preimage (hconv.nullMeasurableSet (μ := volume))
  -- ... and still covers every worm, via the inverse placement.
  have hcovers : ∀ w ∈ Worms, CoversByIsometry (g '' K) w := by
    intro w hw
    obtain ⟨h, hh, hwsub⟩ := hcov w hw
    refine ⟨h ∘ g', isOrientationPreservingIsometry_comp hh hg', fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hwsub hx
    exact ⟨g y, Set.mem_image_of_mem g hy, by simp only [Function.comp_apply, hleft y]⟩
  refine ⟨g '' K, hgK_convex, hcovers, ?_, hvol.le.trans hsmall⟩
  rw [← hhull]
  exact convexHull_min hsub hgK_convex

/-- A volume bound valid for every *convex* cover of all worms is a lower bound on
`moserCoverNumber`: the convex hull demanded by a placement cover is itself a
convex cover of no larger volume — it covers each worm via the inverse of that
worm's placement (`IsOrientationPreservingIsometry.exists_symm`). -/
theorem le_moserCoverNumber_of_forall_convex_cover {t : ℝ≥0∞}
    (h : ∀ K : Set ℝ², Convex ℝ K → (∀ w ∈ Worms, CoversByIsometry K w) →
      t ≤ volume K) :
    t ≤ moserCoverNumber := by
  rw [moserCoverNumber, minimalCoverArea, minimalVolume]
  refine le_sInf ?_
  rintro v ⟨X, ⟨g, hgop, hsub⟩, rfl⟩
  set H := convexHull ℝ (⋃ s ∈ Worms, g s '' s) with hH
  have hcov : ∀ w ∈ Worms, CoversByIsometry H w := by
    intro w hw
    obtain ⟨g', hg'op, hleft, _⟩ := (hgop w hw).exists_symm
    refine ⟨g', hg'op, fun x hx => ⟨g w x, ?_, hleft x⟩⟩
    exact subset_convexHull ℝ _ (Set.mem_biUnion hw ⟨x, hx, rfl⟩)
  exact le_trans (h H (convex_convexHull ℝ _) hcov) (measure_mono hsub)

/-- **Termination of the search implies the record bound.** If some sound working
set is empty — the certificate the computational search is meant to produce — then
`areaThreshold ≤ moserCoverNumber`. -/
theorem areaThreshold_le_moserCoverNumber_of_run
    (h : ∃ s : WorkingSet, s.Sound ∧ s.polygons = []) :
    ENNReal.ofReal (areaThreshold : ℝ) ≤ moserCoverNumber := by
  obtain ⟨s, hs, he⟩ := h
  refine le_moserCoverNumber_of_forall_convex_cover (fun K hconv hcov => ?_)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨K', hK'⟩ := exists_pinnedSmallCover hconv hcov hlt.le
  exact no_pinnedSmallCover_of_sound_of_empty hs he K' hK'

/-!
## The target

**A new record lower bound for Moser's worm problem** — that the minimal area of
a convex set covering every unit worm up to orientation-preserving isometry is at
least `areaThreshold = 0.232240`, beating the published lower bound `0.232239` —
is *not* asserted here, because it is not proved: it would be a new mathematical
result. What is proved is the reduction
`areaThreshold_le_moserCoverNumber_of_run`, which turns it into a finite,
checkable certificate:

> exhibit a sound working set with no polygons, i.e. `∃ s, s.Sound ∧ s.polygons = []`,
> by iterating `WorkingSet.addWormAndCleanup` from `WorkingSet.initial` using
> `WorkingSet.initial_sound` and the preservation lemmas.

Producing that certificate needs two things that are open: the crux hypothesis
`WorkingSet.WormAddingSound` (see its docstring — it should be validated
computationally before anyone tries to prove it), and an actual terminating run
of the search.
-/

end Moser

end
