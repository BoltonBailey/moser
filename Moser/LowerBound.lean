import Mathlib
import Moser.Constants
import Moser.Manipulation.Operations
import Moser.Real.CompactnessOutline

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
3. **Preservation** (`WorkingSet.Sound.bigSetRemoval`, `.supersetRemoval`,
   `.wormAdding`): the working-set operations preserve soundness. The `wormAdding`
   case is the mathematical crux of the whole development; see its docstring.
4. **Termination ⇒ bound** (`Moser.areaThreshold_le_moserCoverNumber_of_run`): if a
   sound working set becomes empty, no pinned small cover exists, and after
   un-pinning (`Moser.exists_pinnedSmallCover`) and passing from placement covers to
   convex covers (`Moser.le_moserCoverNumber_of_forall_convex_cover`) the record
   bound `areaThreshold ≤ moserCoverNumber` follows.

The final target is `Moser.areaThreshold_le_moserCoverNumber`, which awaits a
certificate: a concrete terminating run of the algorithm, i.e. a proof of
`∃ s, s.Sound ∧ s.polygons = []` obtained by iterating `addWormAndCleanup` from
`WorkingSet.initial`.

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

/-- The real region of a rational convex polygon is convex. -/
theorem convex_realHull (poly : ConvexPolygon ℚ) : Convex ℝ poly.realHull :=
  convex_convexHull ℝ _

/-- **Area bridge.** The Lebesgue area of the real region of a rational convex
polygon is its (rational, shoelace) `area`.

Leaf `sorry` of the spine. Routine but substantial: relate `shoelaceArea` on the
counterclockwise vertex list to the Lebesgue measure of the convex hull, e.g. by
triangulating from a vertex and using the measure of a triangle. -/
theorem volume_realHull (poly : ConvexPolygon ℚ) :
    volume poly.realHull = ENNReal.ofReal (poly.area : ℝ) := by
  sorry

/-- **Containment bridge.** The Boolean vertex-containment test `isSubsetOf`
implies containment of the real regions.

Leaf `sorry` of the spine. Requires soundness of `ConvexPolygon.contains`
(via `toHalfSpaces`) with respect to `realHull` membership. -/
theorem realHull_subset_realHull {p q : ConvexPolygon ℚ}
    (h : p.isSubsetOf q = true) : p.realHull ⊆ q.realHull := by
  sorry

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
      Matrix.head_cons, Real.dist_eq, sq_abs]
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

Intended argument: a pinned small cover `K` contains the real region of some
`p ∈ s.polygons` (by `hs`). Since `hw : w.IsWormHull`, `K` also covers a worm whose
hull is `w.realHull`, so by convexity `K` contains `g '' w.realHull` for some real
direct isometry `g`. Because `K` is pinned and small, `g` is confined to a compact
range of placements (the `LocationRange`/`distanceCutoff` reasoning of
`Moser.Constants`). The discretization `discretizeIsometries epsilon` must then
contain a rational isometry close enough to `g` that the `shrink epsilon`-shrunken
copy of `w`, placed by it, lies inside `g '' w.realHull ⊆ K`. Then
`hull(p ∪ placed shrunken w) ⊆ K`, and that hull is an element of
`wormReplacement p w epsilon`.

**Warning — unverified quantitative claims.** This statement's truth depends on
properties of the current implementations that have NOT been checked:
1. `discretizeIsometries epsilon` must cover the full confined range of rotations
   *and translations* at resolution matched to the `shrink` margin (cf. the TODO in
   `wormReplacement`).
2. The `shrink`-margin vs. grid-resolution accounting must work out; for worms with
   degenerate (lower-dimensional) hulls, e.g. segments, shrinking provides no
   margin and the argument fails — `w` may need a full-dimensional hull hypothesis.
3. `wormReplacement` silently drops candidates where `ConvexPolygon.ofList` returns
   `none`; soundness requires the needed candidate to survive.
Do not invest in proving this lemma before validating the search computationally;
expect the statement to need additional hypotheses (or the implementation to need
fixes) discovered during that validation. -/
theorem Sound.wormAdding {s : WorkingSet} (hs : s.Sound) {w : ConvexPolygon ℚ}
    (hw : w.IsWormHull) {epsilon : ℚ} (heps : 0 < epsilon) :
    (s.wormAdding w epsilon heps).Sound := by
  sorry

/-- The composite cleanup pass preserves soundness. -/
theorem Sound.cleanup {s : WorkingSet} (hs : s.Sound) : s.cleanup.Sound :=
  hs.bigSetRemoval.supersetRemoval

/-- The main loop step `addWormAndCleanup` preserves soundness. -/
theorem Sound.addWormAndCleanup {s : WorkingSet} (hs : s.Sound) {w : ConvexPolygon ℚ}
    (hw : w.IsWormHull) {epsilon : ℚ} (heps : 0 < epsilon) :
    (s.addWormAndCleanup w epsilon heps).Sound :=
  (hs.wormAdding hw heps).cleanup

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

/-- **Target theorem: a new record lower bound for Moser's worm problem.**
The minimal area of a convex set covering every unit worm up to
orientation-preserving isometry is at least `areaThreshold = 0.232240`, beating
the best published lower bound `0.232239`.

Awaits a certificate run: exhibit a sound working set with no polygons (iterate
`WorkingSet.addWormAndCleanup` from `WorkingSet.initial`, using
`WorkingSet.initial_sound` and the preservation lemmas) and apply
`areaThreshold_le_moserCoverNumber_of_run`. -/
theorem areaThreshold_le_moserCoverNumber :
    ENNReal.ofReal (areaThreshold : ℝ) ≤ moserCoverNumber := by
  sorry

end Moser
