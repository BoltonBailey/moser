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
of a genuine worm: the L-shaped unit-length path `(0,1/2) → (0,0) → (1/2,0)`.

Leaf `sorry` of the spine. Routine: parametrize the path by arc length (it is
`1`-Lipschitz) and compute the hull of its range. -/
theorem initialWorm_isWormHull : InitialWorm.IsWormHull := by
  sorry

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

/-- `supersetRemoval` preserves soundness: if the witness polygon `p` is removed
because some strictly smaller polygon `q ⊆ p` is present, then a minimal such `q`
survives the filter and is itself contained in the cover (via the containment
bridge `ConvexPolygon.realHull_subset_realHull`).

Leaf `sorry` of the spine. Needs a finite minimal-element argument for the
`isSubsetOf` preorder, plus transitivity of `isSubsetOf` (or arguing directly with
`realHull` containment). -/
theorem Sound.supersetRemoval {s : WorkingSet} (hs : s.Sound) : s.supersetRemoval.Sound := by
  sorry

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

/-- **Un-pinning.** Any convex set of area at most `areaThreshold` covering all
worms can be moved by a direct isometry to a pinned small cover: it covers the
L-shaped worm of `Moser.initialWorm_isWormHull`, and moving that copy onto the
standard `InitialWorm` position preserves convexity, coverage, and volume.

Leaf `sorry` of the spine. Needs `initialWorm_isWormHull`, volume-invariance of
direct isometries, and closure of coverage under composing with an isometry (cf.
`IsOrientationPreservingIsometry.exists_symm` in `CompactnessOutline`, currently
`private`). -/
theorem exists_pinnedSmallCover {K : Set ℝ²} (hconv : Convex ℝ K)
    (hcov : ∀ w ∈ Worms, CoversByIsometry K w)
    (hsmall : volume K ≤ ENNReal.ofReal (areaThreshold : ℝ)) :
    ∃ K' : Set ℝ², IsPinnedSmallCover K' := by
  sorry

/-- A volume bound valid for every *convex* cover of all worms is a lower bound on
`moserCoverNumber`: the convex hull demanded by a placement cover is itself a
convex cover of no larger volume.

Leaf `sorry` of the spine. Routine: `le_sInf`, then for a placement cover `X` take
`H = convexHull ℝ (⋃ s ∈ Worms, g s '' s) ⊆ X`; `H` covers each worm via the
inverse placement (needs `IsOrientationPreservingIsometry.exists_symm`, currently
`private` in `CompactnessOutline`). -/
theorem le_moserCoverNumber_of_forall_convex_cover {t : ℝ≥0∞}
    (h : ∀ K : Set ℝ², Convex ℝ K → (∀ w ∈ Worms, CoversByIsometry K w) →
      t ≤ volume K) :
    t ≤ moserCoverNumber := by
  sorry

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
