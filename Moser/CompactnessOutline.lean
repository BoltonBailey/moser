import Mathlib

/-!
# Compactness outline for the Moser worm problem

This file formalizes the blueprint `compactness-outline`: worms as `1`-Lipschitz
curves `[0,1] → ℝ²`, their `ε`-thickenings, a finite grid `ε`-net, the Moser
cover number, and the lower/upper bounds together with the planar Steiner
formula bounding the gap between them.

We mirror the canonical formalization of worms used in `FormalConjectures`
(`MoserWorm`): a worm is represented by the *range* of a `1`-Lipschitz function
from `[0,1]` to the Euclidean plane, and an (orientation-preserving) isometry is
a linear isometry equivalence with determinant `1` followed by a translation.
-/

open MeasureTheory
open scoped ENNReal

namespace Moser.CompactnessOutline

/-- The real Euclidean plane `ℝ²`. -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Worms and thickenings -/

/-- **Worm** (`def:worm`).
A *worm* is a `1`-Lipschitz curve `f : [0,1] → ℝ²`. Following the canonical
Mathlib formalization, the set of worms is the set of *ranges* of `1`-Lipschitz
functions from `[0,1]` to `ℝ²`. -/
def Worms : Set (Set ℝ²) :=
  {s | ∃ f : (Set.Icc (0 : ℝ) 1) → ℝ², LipschitzWith 1 f ∧ Set.range f = s}

/-- **Pinned worm** (`def:pinnedWorm`).
A worm `f` is *pinned* if `f 0 = (0,0)`. The set of pinned worms is the set of
ranges of `1`-Lipschitz functions `[0,1] → ℝ²` whose value at `0` is the origin. -/
def PinnedWorms : Set (Set ℝ²) :=
  {s | ∃ f : (Set.Icc (0 : ℝ) 1) → ℝ²,
      LipschitzWith 1 f ∧ f ⟨0, Set.left_mem_Icc.2 zero_le_one⟩ = 0 ∧ Set.range f = s}

/-- **`ε`-thickening** (`def:thickening`).
For `A ⊆ ℝ²` and `ε ≥ 0`, the `ε`-thickening of `A` is the closed
`ε`-neighbourhood `{x | dist x A ≤ ε}`. This is exactly `Metric.cthickening`,
recorded here for reference; downstream declarations use `Metric.cthickening`
directly. -/
example (ε : ℝ) (A : Set ℝ²) : Set ℝ² := Metric.cthickening ε A

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

/-! ## A finite `ε`-net of polygonal worms -/

/-- **`ε`-net of worms** (`def:epsilonNet`).
Let `ε > 0`. A set `S` of worms is an *`ε`-net of worms* if the image of every
pinned worm is contained in the `ε`-thickening of (the image of) some element of
`S`. -/
def IsEpsilonNet (ε : ℝ) (S : Set (Set ℝ²)) : Prop :=
  ∀ s ∈ PinnedWorms, ∃ t ∈ S, s ⊆ Metric.cthickening ε t

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

/-- **A finite grid `ε`-net exists** (`thm:finiteEpsilonNet`).
For every `ε > 0` there exist `k : ℕ` and `δ > 0` such that the set `S_ε` of
`(k, δ)`-grid polygonal worms whose nodes lie within distance `1` of the origin
is finite and is an `ε`-net of worms. -/
theorem finiteEpsilonNet (ε : ℝ) (hε : 0 < ε) :
    ∃ (k : ℕ) (δ : ℝ), 0 < δ ∧
      (GridNetWorms k δ).Finite ∧ IsEpsilonNet ε (GridNetWorms k δ) := by
  sorry

/-! ## Bounds on the Moser number -/

/-- The set of *worm covers*: measurable sets `X` that cover every worm by an
orientation-preserving isometry (a determinant-`1` linear isometry equivalence
followed by a translation). -/
def WormCovers : Set (Set ℝ²) :=
  {X | MeasurableSet X ∧ ∀ w ∈ Worms, ∃ (e : ℝ² ≃ₗᵢ[ℝ] ℝ²) (v : ℝ²),
      e.toLinearEquiv.det = 1 ∧ w ⊆ (fun x => e x + v) '' X}

/-- **Moser cover number** (`def:moserNumber`).
The *Moser cover number* `M` is the infimum of `area C` over all convex
covers `C`. -/
noncomputable def moserCoverNumber : ℝ≥0∞ :=
  sInf {v | ∃ C ∈ WormCovers, Convex ℝ C ∧ volume C = v}

/-- The minimal area of a convex hull of placements of a set of worms `S`: the
infimum, over translation-rotations `(g_s)_{s ∈ S}`, of the area of the convex
hull of the union of the placed images. This is `area (K S)`. -/
noncomputable def minimalCoverArea (S : Set (Set ℝ²)) : ℝ≥0∞ :=
  sInf {v | ∃ (e : Set ℝ² → ℝ² ≃ₗᵢ[ℝ] ℝ²) (t : Set ℝ² → ℝ²),
      (∀ s ∈ S, (e s).toLinearEquiv.det = 1) ∧
      volume (convexHull ℝ (⋃ s ∈ S, (fun x => (e s) x + t s) '' s)) = v}

/-- **Minimal convex cover of a finite set of worms** (`def:minimalCover`).
`IsMinimalCover S K` states that `K = K S` is a convex set realizing the minimal
area `minimalCoverArea S`, obtained as the convex hull of placements of the
elements of `S` by translation-rotations. -/
def IsMinimalCover (S : Set (Set ℝ²)) (K : Set ℝ²) : Prop :=
  Convex ℝ K ∧
  (∃ (e : Set ℝ² → ℝ² ≃ₗᵢ[ℝ] ℝ²) (t : Set ℝ² → ℝ²),
      (∀ s ∈ S, (e s).toLinearEquiv.det = 1) ∧
      K = convexHull ℝ (⋃ s ∈ S, (fun x => (e s) x + t s) '' s)) ∧
  volume K = minimalCoverArea S

/-- The perimeter of a planar set `K`, defined as the `1`-dimensional Euclidean
Hausdorff measure (arc length) of its topological frontier. -/
noncomputable def perimeter (K : Set ℝ²) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure 1 (frontier K)).toReal

/-- **Lower bound on the Moser number** (`thm:lowerBound`).
For any finite set `S` of worms, `M ≥ area (K S)`. -/
theorem lowerBound (S : Set (Set ℝ²)) (hS : S.Finite) :
    minimalCoverArea S ≤ moserCoverNumber := by
  sorry

/-- **Upper bound on the Moser number** (`thm:upperBound`).
Let `ε > 0` and let `S_ε` be a finite `ε`-net of worms with minimal convex cover
`K`. Then `M ≤ area (K^ε)`, the area of the `ε`-thickening of `K`. -/
theorem upperBound (ε : ℝ) (hε : 0 < ε) (S : Set (Set ℝ²)) (hS : S.Finite)
    (hnet : IsEpsilonNet ε S) (K : Set ℝ²) (hK : IsMinimalCover S K) :
    moserCoverNumber ≤ volume (Metric.cthickening ε K) := by
  sorry

/-- **Steiner gap between the bounds** (`thm:steinerGap`).
Let `K` be a convex body in `ℝ²` with perimeter `L`. Then for every `ε ≥ 0`,
`area (K^ε) = area K + ε L + π ε²`. -/
theorem steinerGap (K : Set ℝ²) (hconv : Convex ℝ K) (hcomp : IsCompact K)
    (hne : K.Nonempty) (ε : ℝ) (hε : 0 ≤ ε) :
    (volume (Metric.cthickening ε K)).toReal
      = (volume K).toReal + ε * perimeter K + Real.pi * ε ^ 2 := by
  sorry

/-- **Approximating the Moser number** (`thm:approxAlgorithm`).
For any target accuracy `x > 0` there is an `ε`-net `S` and a minimal convex
cover `K` of it providing a lower bound `area (K S) ≤ M` and an upper bound
`M ≤ area (K^ε)` whose gap is at most `x`. -/
theorem approxAlgorithm (x : ℝ) (hx : 0 < x) :
    ∃ (ε : ℝ) (S : Set (Set ℝ²)) (K : Set ℝ²),
      0 < ε ∧ S.Finite ∧ IsEpsilonNet ε S ∧ IsMinimalCover S K ∧
      minimalCoverArea S ≤ moserCoverNumber ∧
      moserCoverNumber ≤ volume (Metric.cthickening ε K) ∧
      (volume (Metric.cthickening ε K)).toReal - (minimalCoverArea S).toReal ≤ x := by
  sorry

end Moser.CompactnessOutline
