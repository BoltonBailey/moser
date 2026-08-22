module

public import Moser.Real.Certificate
meta import Mathlib
meta import Moser.Geometry.Polygon
meta import Moser.Geometry.PolygonArea
meta import Moser.Real.Certificate

public section

/-!
# Compressing the certificate to ten sets

`Moser.certList` has 96 sets. Merging is sound in one direction: if a cover must
contain *one* of a group of sets, it must contain any common subset of the group
— in particular their intersection (`IsCoverCertificate.refine`).

The 96 sets are hulls of the pinned worm hull `H` together with one of 96 far
points spread around a circle, so consecutive sets overlap heavily and their
intersection is still large. Grouping them into ten contiguous arcs and taking
intersections therefore costs almost nothing:

| certificate | sets | bound |
| --- | --- | --- |
| the hexagonal worm alone | 1 | `3233/20808 ≈ 0.15537` |
| `groupList` (this file) | **10** | `817/5000 = 0.1634` |
| `certList` | 96 | `41/250 = 0.164` |

The arcs are deliberately unbalanced — the sets with the largest area merge 30
at a time, the smallest ones stay in groups of one or two — because that is what
maximises the least area of an intersection. The partition below is optimal: no
grouping of the 96 sets into ten contiguous arcs has a larger minimum area.
-/

open MeasureTheory
open scoped ENNReal

namespace Moser

open Moser.CompactnessOutline ConvexPolygon

/-- The real Euclidean plane `ℝ²`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## The ten merged sets -/

/-- The vertex lists of the ten merged sets. -/
def groupPts : ℕ → List (Point ℚ)
  | 0 => [![(1/400000 : ℚ), (27/10000000 : ℚ)], ![(66667/400000 : ℚ), (27/10000000 : ℚ)], ![(98039/312500 : ℚ), (784333/10000000 : ℚ)], ![(1960777/5000000 : ℚ), (1127453/5000000 : ℚ)], ![(1073561/2500000 : ℚ), (4501727/10000000 : ℚ)], ![(98039/312500 : ℚ), (539213/1000000 : ℚ)], ![(66667/400000 : ℚ), (1544109/2500000 : ℚ)]]
  | 1 => [![(3/1250000 : ℚ), (27/10000000 : ℚ)], ![(833337/5000000 : ℚ), (27/10000000 : ℚ)], ![(98039/312500 : ℚ), (784333/10000000 : ℚ)], ![(1960777/5000000 : ℚ), (2254907/10000000 : ℚ)], ![(1960777/5000000 : ℚ), (3921557/10000000 : ℚ)], ![(753211/2500000 : ℚ), (796761/1250000 : ℚ)], ![(833337/5000000 : ℚ), (1544109/2500000 : ℚ)]]
  | 2 => [![(3/1250000 : ℚ), (31/10000000 : ℚ)], ![(833337/5000000 : ℚ), (31/10000000 : ℚ)], ![(98039/312500 : ℚ), (784337/10000000 : ℚ)], ![(1960777/5000000 : ℚ), (2254911/10000000 : ℚ)], ![(1960777/5000000 : ℚ), (3921561/10000000 : ℚ)], ![(98039/312500 : ℚ), (2696067/5000000 : ℚ)], ![(1139233/5000000 : ℚ), (1389031/2000000 : ℚ)], ![(833337/5000000 : ℚ), (154411/250000 : ℚ)]]
  | 3 => [![(1/400000 : ℚ), (27/10000000 : ℚ)], ![(66667/400000 : ℚ), (27/10000000 : ℚ)], ![(98039/312500 : ℚ), (784333/10000000 : ℚ)], ![(1960777/5000000 : ℚ), (2254907/10000000 : ℚ)], ![(1960777/5000000 : ℚ), (3921557/10000000 : ℚ)], ![(98039/312500 : ℚ), (539213/1000000 : ℚ)], ![(1867789/10000000 : ℚ), (55903/78125 : ℚ)]]
  | 4 => [![(23/10000000 : ℚ), (3/1000000 : ℚ)], ![(1666673/10000000 : ℚ), (3/1000000 : ℚ)], ![(1568623/5000000 : ℚ), (156867/2000000 : ℚ)], ![(245097/625000 : ℚ), (2254909/10000000 : ℚ)], ![(245097/625000 : ℚ), (3921559/10000000 : ℚ)], ![(1568623/5000000 : ℚ), (1348033/2500000 : ℚ)], ![(1666673/10000000 : ℚ), (3088219/5000000 : ℚ)], ![(606687/5000000 : ℚ), (1368403/2500000 : ℚ)]]
  | 5 => [![(-265359/10000000 : ℚ), (42503/5000000 : ℚ)], ![(21/10000000 : ℚ), (23/10000000 : ℚ)], ![(1666671/10000000 : ℚ), (23/10000000 : ℚ)], ![(627449/2000000 : ℚ), (784329/10000000 : ℚ)], ![(78431/200000 : ℚ), (1127451/5000000 : ℚ)], ![(78431/200000 : ℚ), (245097/625000 : ℚ)], ![(627449/2000000 : ℚ), (2696063/5000000 : ℚ)], ![(1666671/10000000 : ℚ), (386027/625000 : ℚ)]]
  | 6 => [![(-29873/1000000 : ℚ), (-464979/5000000 : ℚ)], ![(833337/5000000 : ℚ), (1/400000 : ℚ)], ![(98039/312500 : ℚ), (784331/10000000 : ℚ)], ![(3921553/10000000 : ℚ), (281863/1250000 : ℚ)], ![(3921553/10000000 : ℚ), (1960777/5000000 : ℚ)], ![(98039/312500 : ℚ), (42126/78125 : ℚ)], ![(833337/5000000 : ℚ), (6176433/10000000 : ℚ)]]
  | 7 => [![(11/5000000 : ℚ), (1/400000 : ℚ)], ![(60773/2000000 : ℚ), (-873789/10000000 : ℚ)], ![(1568623/5000000 : ℚ), (784331/10000000 : ℚ)], ![(245097/625000 : ℚ), (281863/1250000 : ℚ)], ![(245097/625000 : ℚ), (1960777/5000000 : ℚ)], ![(1568623/5000000 : ℚ), (42126/78125 : ℚ)], ![(104167/625000 : ℚ), (3088217/5000000 : ℚ)]]
  | 8 => [![(1/400000 : ℚ), (1/400000 : ℚ)], ![(433847/2500000 : ℚ), (-6431/125000 : ℚ)], ![(98039/312500 : ℚ), (784331/10000000 : ℚ)], ![(1960777/5000000 : ℚ), (450981/2000000 : ℚ)], ![(1960777/5000000 : ℚ), (784311/2000000 : ℚ)], ![(98039/312500 : ℚ), (42126/78125 : ℚ)], ![(66667/400000 : ℚ), (3088217/5000000 : ℚ)]]
  | 9 => [![(3/1250000 : ℚ), (27/10000000 : ℚ)], ![(833337/5000000 : ℚ), (27/10000000 : ℚ)], ![(2079671/5000000 : ℚ), (624619/5000000 : ℚ)], ![(3921553/10000000 : ℚ), (3921557/10000000 : ℚ)], ![(3137247/10000000 : ℚ), (539213/1000000 : ℚ)], ![(833337/5000000 : ℚ), (1544109/2500000 : ℚ)]]
  | _ => []

/-- Which of the ten groups the `i`-th of the 96 sets belongs to: the arcs are
`[0,16), [16,23), [23,25), [25,26), [26,56), [56,63), [63,64), [64,67),
[67,80), [80,96)`. -/
def groupOf (i : ℕ) : ℕ :=
  if i < 16 then 0 else if i < 23 then 1 else if i < 25 then 2 else if i < 26 then 3
  else if i < 56 then 4 else if i < 63 then 5 else if i < 64 then 6 else if i < 67 then 7
  else if i < 80 then 8 else 9

/-- The `g`-th merged polygon: the verified hull of `groupPts g`. -/
def groupPolygon (g : ℕ) : Option (ConvexPolygon ℚ) :=
  ConvexPolygon.ofListChecked (groupPts g)

/-- The `g`-th merged set. -/
noncomputable def groupSet (g : ℕ) : Set ℝ² :=
  convexHull ℝ (Point.toEuclidean '' {p : Point ℚ | p ∈ groupPts g})

/-- **The compressed certificate**: ten convex sets. -/
noncomputable def groupList : List (Set ℝ²) := (List.range 10).map groupSet

lemma groupList_length : groupList.length = 10 := by simp [groupList]

/-! ## The two computations

Both are decidable statements about rational polygons.
-/

/-- Each merged set is contained in every one of the 96 sets of its group. -/
lemma group_subset_check : ∀ i ∈ Finset.range 96,
    ((groupPolygon (groupOf i)).bind fun P =>
      (certPolygon i).map fun q => P.isSubsetOf q).getD false = true := by
  native_decide

/-- Each merged set has area at least `817/5000 = 0.1634`. -/
lemma group_area_check : ∀ g ∈ Finset.range 10,
    ((groupPolygon g).map fun P => decide ((817 / 5000 : ℚ) ≤ P.area)).getD false = true := by
  native_decide

/-! ## The certificate -/

/-- The merged set of a group sits inside each of the 96 sets it merges. -/
lemma groupSet_subset_certSet {i : ℕ} (hi : i < 96) : groupSet (groupOf i) ⊆ certSet i := by
  have hchk := group_subset_check i (Finset.mem_range.mpr hi)
  rcases hg : groupPolygon (groupOf i) with _ | P
  · rw [hg] at hchk; simp at hchk
  rcases hc : certPolygon i with _ | q
  · rw [hg, hc] at hchk; simp at hchk
  rw [hg, hc] at hchk
  simp only [Option.bind_some, Option.map_some, Option.getD_some] at hchk
  have hP : P.realHull = groupSet (groupOf i) := ConvexPolygon.realHull_ofListChecked hg
  have hq : q.realHull = certSet i := certPolygon_realHull hc
  rw [← hP, ← hq]
  exact ConvexPolygon.realHull_subset_realHull hchk

/-- **The ten sets form a cover certificate.** -/
theorem isCoverCertificate_groupList : IsCoverCertificate groupList := by
  refine isCoverCertificate_certList.refine ?_
  intro K hK
  rw [certList_eq, List.mem_map] at hK
  obtain ⟨i, hi, rfl⟩ := hK
  have hi96 : i < 96 := List.mem_range.mp hi
  refine ⟨groupSet (groupOf i), ?_, groupSet_subset_certSet hi96⟩
  rw [groupList, List.mem_map]
  refine ⟨groupOf i, List.mem_range.mpr ?_, rfl⟩
  unfold groupOf
  split_ifs <;> omega

lemma groupSet_measurable (g : ℕ) : MeasurableSet (groupSet g) := by
  refine (Set.Finite.isCompact_convexHull ℝ (Set.Finite.image _ ?_)).isClosed.measurableSet
  exact List.finite_toSet _

lemma groupSet_volume {g : ℕ} (hg : g < 10) :
    ENNReal.ofReal ((817 : ℝ) / 5000) ≤ volume (groupSet g) := by
  have hchk := group_area_check g (Finset.mem_range.mpr hg)
  rcases hp : groupPolygon g with _ | P
  · rw [hp] at hchk; simp at hchk
  rw [hp] at hchk
  simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at hchk
  have hP : P.realHull = groupSet g := ConvexPolygon.realHull_ofListChecked hp
  have hvol := ConvexPolygon.volume_realHull P
  rw [hP] at hvol
  rw [hvol]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc2 : ((817 / 5000 : ℚ) : ℝ) ≤ ((P.area : ℚ) : ℝ) := by exact_mod_cast hchk
  push_cast at hc2
  linarith

/-- **The lower bound from ten sets**: `M ≥ 817/5000 = 0.1634`, within `0.4%` of
what the 96-set certificate gives. -/
theorem groupCertificate_le_moserCoverNumber :
    ENNReal.ofReal ((817 : ℝ) / 5000) ≤ moserCoverNumber := by
  refine le_moserCoverNumber_of_certificate isCoverCertificate_groupList ?_ ?_
  · intro K hK
    rw [groupList, List.mem_map] at hK
    obtain ⟨g, -, rfl⟩ := hK
    exact groupSet_measurable g
  · intro K hK
    rw [groupList, List.mem_map] at hK
    obtain ⟨g, hg, rfl⟩ := hK
    exact groupSet_volume (List.mem_range.mp hg)

end Moser

end
