module

public import Moser.Geometry.HalfSpaces

@[expose] public section

/-!
# Convex Polygons

This file defines convex polygons as ordered lists of vertices over an ordered
field `K`.
-/

open Fin.NatCast

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/--
A polygon represented by its vertices.

we require that all vertices are distinct, and that there are 3 or more vertices.

Operations that would return a degenerate polygon (fewer than 3 vertices) return none instead.

Note we do not extend mathlib's `Polygon`, because we want to bundle the vertex count.
-/
structure NondegenPolygon (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /--
  The number of vertices in the polygon. -/
  vertex_count : ℕ
  /-- vertex_count must be positive -/
  vertex_count_pos : NeZero vertex_count
  /--
  Vertex count must be at least 3
  -/
  three_le_vertex_count : 3 ≤ vertex_count
  /-- The vertices of the polygon, in counterclockwise order -/
  vertices : Fin vertex_count → Point K
  /-- All vertices are distinct -/
  nodup : Function.Injective vertices

instance [Repr K] : Repr (NondegenPolygon K) where
  reprPrec p _ :=
    repr (p.vertex_count, (List.finRange p.vertex_count).map p.vertices)

instance [DecidableEq K] : DecidableEq (NondegenPolygon K) := fun a b => by
  by_cases hn : a.vertex_count = b.vertex_count
  · cases a with | mk vc₁ vp₁ tl₁ v₁ nd₁ =>
    cases b with | mk vc₂ vp₂ tl₂ v₂ nd₂ =>
    cases hn
    by_cases hv : v₁ = v₂
    · cases hv
      exact isTrue rfl
    · exact isFalse (fun h => hv (by injection h))
  · exact isFalse (fun h => hn (by cases h; rfl))

instance (poly : NondegenPolygon K) : NeZero poly.vertex_count := poly.vertex_count_pos

/-- The open half-space strictly to the left of the directed edge from vertex `i` to
vertex `i+1`. -/
def NondegenPolygon.getStrictlyLeftHalfspace (ng : NondegenPolygon K) (i : Fin ng.vertex_count) :
    OpenHalfSpace K :=
  let p1 := ng.vertices i
  let p2 := ng.vertices (i + 1)
  Point.toStrictlyLeft p1 p2 (by
    intro ne
    have := ng.nodup ne
    have three_le := ng.three_le_vertex_count
    simp_all)



/--
The CCW polygon condition for an indexed family of vertices: for every edge
`vᵢ → vᵢ₊₁` and every other vertex `vⱼ` (i.e. `j ≠ i, i+1`, with arithmetic mod `n`),
the triple `(vᵢ, vᵢ₊₁, vⱼ)` is a strict counterclockwise turn — equivalently, `vⱼ`
lies strictly to the left of the directed edge from `vᵢ` to `vᵢ₊₁`.

This is the natural strict-convexity invariant for a polygon traversed
counterclockwise: every non-adjacent vertex lies strictly inside the open
half-space supporting each edge. Strictness rules out collinear triples, so the
listed vertices are exactly the extreme points of the convex hull.
-/
def IsCCWPolygon {n : ℕ} [NeZero n] (vertices : Fin n → Point K) : Prop :=
  ∀ i j : Fin n, j ≠ i → j ≠ i + 1 →
    Point.ccw (vertices i) (vertices (i + 1)) (vertices j) = true

instance {n : ℕ} [NeZero n] (vertices : Fin n → Point K) :
    Decidable (IsCCWPolygon vertices) :=
  inferInstanceAs (Decidable (∀ _ _ : Fin n, _ → _ → _))

/--
The cyclic CCW chain condition: every consecutive triple of vertices `(vᵢ, vᵢ₊₁, vᵢ₊₂)`
(with cyclic indexing) is a strict counterclockwise turn.

This is strictly weaker than `IsCCWPolygon`: it only constrains immediately consecutive
triples, not arbitrary "vᵢ, vᵢ₊₁, vⱼ" pairs. Equivalence to `IsCCWPolygon` for distinct
vertices is the content of `cyclicCCWChain_implies_IsCCWPolygon`.
-/
def IsCyclicCCWChain {n : ℕ} [NeZero n] (vertices : Fin n → Point K) : Prop :=
  ∀ i : Fin n,
    Point.ccw (vertices i) (vertices (i + 1)) (vertices (i + 2)) = true

instance {n : ℕ} [NeZero n] (vertices : Fin n → Point K) :
    Decidable (IsCyclicCCWChain vertices) :=
  inferInstanceAs (Decidable (∀ _ : Fin n, _))

/--
A convex polygon.

Convexity is enforced by `IsCCWPolygon vertices`: every edge `vᵢ → vᵢ₊₁` has all
other vertices strictly to its left.

The strictness enforces that there can be no collinear triples of vertices,
which in turn ensures that all vertices are extreme points of the convex hull.
-/
structure ConvexPolygon (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    extends NondegenPolygon K where
  /-- Every non-adjacent vertex lies strictly counterclockwise of every edge. -/
  vertices_extremePoints : IsCCWPolygon vertices

attribute [nolint unusedArguments] ConvexPolygon

instance [Repr K] : Repr (ConvexPolygon K) where
  reprPrec p _ := repr p.toNondegenPolygon

instance [DecidableEq K] : DecidableEq (ConvexPolygon K) := fun a b => by
  by_cases h : a.toNondegenPolygon = b.toNondegenPolygon
  · cases a with | mk tnd₁ vep₁ =>
    cases b with | mk tnd₂ vep₂ =>
    cases h
    exact isTrue rfl
  · exact isFalse (fun hab => h (by cases hab; rfl))


/--
The vertex list of a convex polygon, in counterclockwise order.
-/
def ConvexPolygon.vertex_list (poly : ConvexPolygon K) : List (Point K) :=
  List.finRange poly.vertex_count |>.map poly.vertices


/-- Graham scan helper: process remaining points to build upper/lower hull -/
def grahamScanStep (stack : List (Point K)) (p : Point K) : List (Point K) :=
  match stack with
  | [] => [p]
  | [q] => [p, q]
  | q :: r :: rest =>
    if Point.ccw r q p then p :: stack
    else grahamScanStep (r :: rest) p

/-- Lexicographic order on points: by `x`-coordinate, breaking ties with `y`. -/
def Point.lexLE (p q : Point K) : Bool :=
  decide (p 0 < q 0) || (decide (p 0 = q 0) && decide (p 1 ≤ q 1))

/-- Sort a list of points lexicographically by `(x, y)`, after first
    dropping duplicates. The dedup step makes the downstream Graham-scan
    invariants and uniqueness proofs go through cleanly. -/
def sortPointsLex [DecidableEq K] (points : List (Point K)) : List (Point K) :=
  points.dedup.mergeSort Point.lexLE

/--
Lower-hull pass of Andrew's monotone chain: fold `grahamScanStep` left over an
already-sorted list. Scanning left-to-right keeps only strict left turns, so the
result is the lower hull in **reverse** traversal order (the rightmost point is
at the head, the leftmost at the tail).
-/
def lowerHullScan (sorted : List (Point K)) : List (Point K) :=
  sorted.foldl grahamScanStep []

/--
Upper-hull pass of Andrew's monotone chain: scan the **reverse** of an
already-sorted list. The result is the upper hull in reverse traversal order
(the leftmost point is at the head, the rightmost at the tail).
-/
def upperHullScan (sorted : List (Point K)) : List (Point K) :=
  sorted.reverse.foldl grahamScanStep []

/--
Stitch the lower and upper hull scans into a single counterclockwise vertex list.

Each scan is reversed into traversal order, then `dropLast` removes the shared
endpoint where the lower and upper hulls meet, avoiding duplicates. For lists
with fewer than two distinct points the special cases short-circuit.

The upper part is filtered against the lower part to guarantee that the
concatenation has no duplicates, even in degenerate cases where the two hulls
might otherwise share an interior point.
-/
def convexHullFromSorted [DecidableEq K] : List (Point K) → List (Point K)
  | [] => []
  | [p] => [p]
  | sorted =>
    let lower := (lowerHullScan sorted).reverse.dropLast
    let upper := (upperHullScan sorted).reverse.dropLast
    lower ++ upper.filter (fun p => decide (p ∉ lower))

/--
Compute the convex hull of a list of points using a Graham-scan-like algorithm.
Should return a list of vertices such that:

- All points in the returned list are in the input list (no new points).
- The returned list has no duplicates.
- The returned list starts with the lowest x-coordinate point
  (lowest y-coordinate to tiebreak)
  and then goes  in counterclockwise order.
- All input points are in the convex hull defined by the returned vertices.
- The returned vertices are extreme points of the convex hull
  (no vertex is a convex combination of others).

Implementation: lex-sort the points, stitch the two monotone-chain scans
together via `convexHullFromSorted`, and then **validate** the result: a list of
three or more points is returned only if it really is a strictly convex
counterclockwise cycle (`IsCCWPolygon`), and `[]` is returned otherwise.
Consecutive duplicates in the sorted list are absorbed by `grahamScanStep`,
since `Point.ccw` is strict and returns `false` whenever two of its arguments
coincide.

Validation is what makes `convexHullPoints_convex` — the property every
downstream user needs — provable, at the cost of one `O(n²)` check that
`ConvexPolygon.ofList` was performing anyway. It leaves one open question, which
is the *completeness* of the monotone chain:

**TODO.** Validation should never reject: whenever the input has at least three
extreme points, `convexHullFromSorted` should produce a strictly convex cycle.
Proving that is the correctness statement of Andrew's monotone chain (the two
scans are `x`-monotone and meet at the extreme abscissae); the chain invariants
`lowerHullScan_reverse_isCCWChain` and `upperHullScan_reverse_isCCWChain` are the
starting point, but the seam and the deduplicating filter still need to be
analysed. Note that no *soundness* claim depends on it.
-/
def convexHullPoints [DecidableEq K] (points : List (Point K)) : List (Point K) :=
  let hull := convexHullFromSorted (sortPointsLex points)
  if h : 3 ≤ hull.length then
    haveI : NeZero hull.length := ⟨by omega⟩
    if IsCCWPolygon (n := hull.length) hull.get then hull else []
  else hull

/-- Each step of the Graham scan returns a sublist of the stack with the new point pushed. -/
lemma grahamScanStep_sublist (stack : List (Point K)) (p : Point K) :
    (grahamScanStep stack p).Sublist (p :: stack) := by
  match stack with
  | [] => simp [grahamScanStep]
  | [q] => simp [grahamScanStep]
  | q :: r :: rest =>
    unfold grahamScanStep
    split_ifs with h
    · exact List.Sublist.refl _
    · have ih := grahamScanStep_sublist (r :: rest) p
      refine ih.trans ?_
      exact (List.sublist_cons_self q (r :: rest)).cons_cons p
termination_by stack.length

/-- Folding `grahamScanStep` over a list yields a sublist of the reversed input prepended to
    the accumulator. -/
lemma foldl_grahamScanStep_sublist (l acc : List (Point K)) :
    (l.foldl grahamScanStep acc).Sublist (l.reverse ++ acc) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append]
    have step : (grahamScanStep acc x).Sublist (x :: acc) := grahamScanStep_sublist acc x
    have ih_inst := ih (grahamScanStep acc x)
    refine ih_inst.trans ?_
    exact List.Sublist.append_left step xs.reverse

/-- The lower-hull scan output is a sublist of the reversed input. -/
lemma lowerHullScan_sublist (sorted : List (Point K)) :
    (lowerHullScan sorted).Sublist sorted.reverse := by
  unfold lowerHullScan
  have := foldl_grahamScanStep_sublist sorted []
  simpa using this

/-- The upper-hull scan output is a sublist of the input. -/
lemma upperHullScan_sublist (sorted : List (Point K)) :
    (upperHullScan sorted).Sublist sorted := by
  unfold upperHullScan
  have h := foldl_grahamScanStep_sublist sorted.reverse []
  rw [List.reverse_reverse] at h
  simpa using h

/-- The lex-sorted (deduplicated) list has no duplicates. -/
lemma sortPointsLex_nodup [DecidableEq K] (points : List (Point K)) :
    (sortPointsLex points).Nodup := by
  unfold sortPointsLex
  have hperm : (points.dedup.mergeSort Point.lexLE).Perm points.dedup :=
    List.mergeSort_perm points.dedup Point.lexLE
  exact hperm.symm.nodup (List.nodup_dedup points)

/-- Stitching the two hull scans preserves no-duplicates. -/
lemma convexHullFromSorted_nodup [DecidableEq K] {sorted : List (Point K)} (h : sorted.Nodup) :
    (convexHullFromSorted sorted).Nodup := by
  match sorted, h with
  | [], _ => simp [convexHullFromSorted]
  | [p], _ => simp [convexHullFromSorted]
  | p :: q :: rest, h =>
    unfold convexHullFromSorted
    set L := p :: q :: rest with hL
    have hL_nodup : L.Nodup := h
    have hL_rev_nodup : L.reverse.Nodup := List.nodup_reverse.mpr hL_nodup
    have lower_sub_rev : (lowerHullScan L).Sublist L.reverse := lowerHullScan_sublist L
    have lower_rev_sub : (lowerHullScan L).reverse.Sublist L.reverse.reverse :=
      lower_sub_rev.reverse
    have lower_rev_sub' : (lowerHullScan L).reverse.Sublist L := by
      rw [List.reverse_reverse] at lower_rev_sub; exact lower_rev_sub
    have lower_dropLast_sub : (lowerHullScan L).reverse.dropLast.Sublist L :=
      (List.dropLast_sublist _).trans lower_rev_sub'
    have lower_nodup : ((lowerHullScan L).reverse.dropLast).Nodup :=
      lower_dropLast_sub.nodup hL_nodup
    have upper_sub : (upperHullScan L).Sublist L := upperHullScan_sublist L
    have upper_rev_sub : (upperHullScan L).reverse.Sublist L.reverse := upper_sub.reverse
    have upper_dropLast_sub : (upperHullScan L).reverse.dropLast.Sublist L.reverse :=
      (List.dropLast_sublist _).trans upper_rev_sub
    have upper_nodup : ((upperHullScan L).reverse.dropLast).Nodup :=
      upper_dropLast_sub.nodup hL_rev_nodup
    set lower := (lowerHullScan L).reverse.dropLast with hlower
    set upper := (upperHullScan L).reverse.dropLast with hupper
    have filt_nodup : (upper.filter (fun p => decide (p ∉ lower))).Nodup :=
      upper_nodup.filter _
    refine List.Nodup.append lower_nodup filt_nodup ?_
    intro x hx_lower hx_filt
    rw [List.mem_filter] at hx_filt
    obtain ⟨_, hx_not⟩ := hx_filt
    exact (of_decide_eq_true hx_not) hx_lower

/-- Every point of the lex-sorted list came from the input list. -/
lemma mem_of_mem_sortPointsLex [DecidableEq K] {points : List (Point K)} {x : Point K}
    (h : x ∈ sortPointsLex points) : x ∈ points := by
  rw [sortPointsLex] at h
  have hperm : (points.dedup.mergeSort Point.lexLE).Perm points.dedup :=
    List.mergeSort_perm points.dedup Point.lexLE
  exact List.mem_dedup.mp (hperm.mem_iff.mp h)

/-- The stitched hull output introduces no new points. -/
lemma mem_of_mem_convexHullFromSorted [DecidableEq K] {sorted : List (Point K)} {x : Point K}
    (h : x ∈ convexHullFromSorted sorted) : x ∈ sorted := by
  rcases sorted with _ | ⟨p, tl⟩
  · simp [convexHullFromSorted] at h
  rcases tl with _ | ⟨q, rest⟩
  · simpa [convexHullFromSorted] using h
  · set L := p :: q :: rest with hL
    have hlower : ∀ y ∈ (lowerHullScan L).reverse.dropLast, y ∈ L := by
      intro y hy
      have h1 : y ∈ (lowerHullScan L).reverse := List.dropLast_subset _ hy
      have h2 : y ∈ lowerHullScan L := List.mem_reverse.mp h1
      have h3 : y ∈ L.reverse := (lowerHullScan_sublist L).subset h2
      exact List.mem_reverse.mp h3
    have hupper : ∀ y ∈ (upperHullScan L).reverse.dropLast, y ∈ L := by
      intro y hy
      have h1 : y ∈ (upperHullScan L).reverse := List.dropLast_subset _ hy
      have h2 : y ∈ upperHullScan L := List.mem_reverse.mp h1
      exact (upperHullScan_sublist L).subset h2
    have hsplit : x ∈ (lowerHullScan L).reverse.dropLast ∨
        x ∈ (upperHullScan L).reverse.dropLast := by
      have h' : x ∈ (lowerHullScan L).reverse.dropLast ++
          ((upperHullScan L).reverse.dropLast.filter
            (fun p => decide (p ∉ (lowerHullScan L).reverse.dropLast))) := h
      rcases List.mem_append.mp h' with hx | hx
      · exact Or.inl hx
      · exact Or.inr (List.mem_of_mem_filter hx)
    rcases hsplit with hx | hx
    · exact hlower _ hx
    · exact hupper _ hx

/-- **The convex hull algorithm introduces no new points.** -/
lemma mem_of_mem_convexHullPoints [DecidableEq K] {points : List (Point K)} {x : Point K}
    (h : x ∈ convexHullPoints points) : x ∈ points := by
  rw [convexHullPoints] at h
  split_ifs at h with h3 hccw
  · exact mem_of_mem_sortPointsLex (mem_of_mem_convexHullFromSorted h)
  · simp at h
  · exact mem_of_mem_sortPointsLex (mem_of_mem_convexHullFromSorted h)

lemma convexHullPoints_nodup [DecidableEq K] (points : List (Point K)) :
    (convexHullPoints points).Nodup := by
  unfold convexHullPoints
  simp only
  split_ifs with h3 hccw
  · exact convexHullFromSorted_nodup (sortPointsLex_nodup points)
  · exact List.nodup_nil
  · exact convexHullFromSorted_nodup (sortPointsLex_nodup points)

/--
Predicate saying every consecutive triple in a list is a strict counterclockwise turn.

Reading the list head-to-tail as `p₀, p₁, p₂, …`, we require `ccw p₀ p₁ p₂ = true`,
i.e. `p₂` is strictly left of the directed segment `p₀ → p₁`. Equivalently, the polyline
formed by the list always turns counterclockwise at every interior vertex.

This is the natural invariant maintained by `grahamScanStep` when reading the stack in
arrival order.
-/
def IsCCWChain : List (Point K) → Prop
  | [] => True
  | [_] => True
  | [_, _] => True
  | p₀ :: p₁ :: p₂ :: rest =>
      Point.ccw p₀ p₁ p₂ = true ∧ IsCCWChain (p₁ :: p₂ :: rest)

/-- The chain invariant for the empty / singleton / pair lists is automatic. -/
@[simp] lemma IsCCWChain_nil : IsCCWChain ([] : List (Point K)) := trivial
@[simp] lemma IsCCWChain_singleton (p : Point K) : IsCCWChain [p] := trivial
@[simp] lemma IsCCWChain_pair (p q : Point K) : IsCCWChain [p, q] := trivial

/--
Indexing characterization of `IsCCWChain`: a list is a CCW chain iff every
position `i` with two successors satisfies `ccw L[i] L[i+1] L[i+2] = true`.
-/
lemma IsCCWChain_iff_get (L : List (Point K)) :
    IsCCWChain L ↔ ∀ (i : ℕ) (h : i + 2 < L.length),
      Point.ccw (L.get ⟨i, by omega⟩) (L.get ⟨i + 1, by omega⟩)
        (L.get ⟨i + 2, h⟩) = true := by
  induction L with
  | nil => simp [IsCCWChain]
  | cons p tail ih =>
    cases tail with
    | nil => simp [IsCCWChain]
    | cons q tail' =>
      cases tail' with
      | nil => simp [IsCCWChain]
      | cons r rest =>
        simp only [IsCCWChain]
        rw [ih]
        constructor
        · rintro ⟨h0, h_rest⟩ i hi
          match i, hi with
          | 0, _ => exact h0
          | k + 1, hk =>
            have hk' : k + 2 < (q :: r :: rest).length := by
              simp at hk ⊢; omega
            have := h_rest k hk'
            simpa using this
        · intro h
          refine ⟨?_, ?_⟩
          · have := h 0 (by simp)
            simpa using this
          · intro k hk
            have hk' : k + 1 + 2 < (p :: q :: r :: rest).length := by
              simp at hk ⊢; omega
            have := h (k + 1) hk'
            simpa using this

/--
Appending an element to a chain whose last two elements are `a, b`
preserves the chain when `ccw a b c = true`.
-/
lemma IsCCWChain_append_cons_cons :
    ∀ {L : List (Point K)} {a b c : Point K},
      IsCCWChain (L ++ [a, b]) → Point.ccw a b c = true →
      IsCCWChain (L ++ [a, b, c])
  | [], _, _, _, _, h_turn => ⟨h_turn, trivial⟩
  | [x], a, b, c, hL, h_turn => by
      -- IsCCWChain [x, a, b] = ⟨ccw x a b, IsCCWChain [a, b]⟩
      have h1 : Point.ccw x a b = true := hL.1
      -- IsCCWChain [x, a, b, c] = ⟨ccw x a b, IsCCWChain [a, b, c]⟩
      exact ⟨h1, h_turn, trivial⟩
  | [x, y], a, b, c, hL, h_turn => by
      -- IsCCWChain [x, y, a, b]
      obtain ⟨h1, h2, _⟩ := hL
      exact ⟨h1, h2, h_turn, trivial⟩
  | x :: y :: z :: rest, a, b, c, hL, h_turn => by
      -- (x :: y :: z :: rest) ++ [a, b] = x :: y :: (z :: rest ++ [a, b])
      -- IsCCWChain hypothesis gives ccw x y z' and IsCCWChain (y :: z' :: ...)
      have hL' : IsCCWChain (x :: y :: (z :: rest ++ [a, b])) := by
        simpa using hL
      have h1 : Point.ccw x y z = true := hL'.1
      have h2 : IsCCWChain (y :: (z :: rest ++ [a, b])) := hL'.2
      have h2' : IsCCWChain ((y :: z :: rest) ++ [a, b]) := by
        simpa using h2
      have ih := IsCCWChain_append_cons_cons h2' h_turn
      have ih' : IsCCWChain (y :: (z :: rest ++ [a, b, c])) := by
        simpa using ih
      change IsCCWChain (x :: y :: (z :: rest ++ [a, b, c]))
      exact ⟨h1, ih'⟩

/-- Dropping the last element of a CCW chain still gives a CCW chain. -/
lemma IsCCWChain.dropLast : ∀ {L : List (Point K)},
    IsCCWChain L → IsCCWChain L.dropLast
  | [], _ => trivial
  | [_], _ => trivial
  | [_, _], _ => trivial
  | [_, _, _], _ => trivial
  | a :: b :: c :: d :: rest, h => by
      obtain ⟨h1, h2⟩ := h
      have ih : IsCCWChain (b :: c :: d :: rest).dropLast :=
        IsCCWChain.dropLast h2
      simp only [List.dropLast_cons_cons] at ih ⊢
      exact ⟨h1, ih⟩

/--
If `acc.reverse` is a CCW chain, then so is `(grahamScanStep acc p).reverse`.

`grahamScanStep` pushes `p` only when it produces a strict left turn,
otherwise it pops and recurses, so the chain invariant is preserved.
-/
lemma grahamScanStep_chain (acc : List (Point K)) (p : Point K) :
    IsCCWChain acc.reverse → IsCCWChain (grahamScanStep acc p).reverse := by
  intro h
  match acc with
  | [] => simp [grahamScanStep]
  | [q] => simp [grahamScanStep]
  | q :: r :: rest =>
      unfold grahamScanStep
      split_ifs with h_ccw
      · -- keep branch: result is p :: q :: r :: rest
        -- (q :: r :: rest).reverse = rest.reverse ++ [r, q]
        -- (p :: q :: r :: rest).reverse = rest.reverse ++ [r, q, p]
        have h_rev_in : (q :: r :: rest).reverse = rest.reverse ++ [r, q] := by
          simp [List.reverse_cons]
        have h_rev_out : (p :: q :: r :: rest).reverse =
            rest.reverse ++ [r, q, p] := by
          simp [List.reverse_cons]
        rw [h_rev_in] at h
        rw [h_rev_out]
        exact IsCCWChain_append_cons_cons h h_ccw
      · -- pop branch: result is grahamScanStep (r :: rest) p
        -- We have h : IsCCWChain ((q :: r :: rest).reverse).
        -- Need: IsCCWChain ((r :: rest).reverse) for the IH.
        have h_eq : (q :: r :: rest).reverse =
            (r :: rest).reverse ++ [q] := by
          simp [List.reverse_cons]
        rw [h_eq] at h
        have h_drop : ((r :: rest).reverse ++ [q]).dropLast =
            (r :: rest).reverse := by
          simp
        have h_chain : IsCCWChain (r :: rest).reverse := by
          have := IsCCWChain.dropLast h
          rwa [h_drop] at this
        exact grahamScanStep_chain (r :: rest) p h_chain
  termination_by acc.length

/-- Folding `grahamScanStep` over a list preserves the CCW chain invariant. -/
lemma foldl_grahamScanStep_chain (l acc : List (Point K))
    (h : IsCCWChain acc.reverse) :
    IsCCWChain (l.foldl grahamScanStep acc).reverse := by
  induction l generalizing acc with
  | nil => simpa using h
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih _ (grahamScanStep_chain acc x h)

/--
Reading the stack output of `lowerHullScan` from tail to head (i.e. arrival order)
yields a CCW chain.

Because `grahamScanStep` only pushes a new point when the turn at the previous head
is counterclockwise, the reversed stack is a sequence of strict left turns.
-/
lemma lowerHullScan_reverse_isCCWChain (sorted : List (Point K)) :
    IsCCWChain (lowerHullScan sorted).reverse := by
  unfold lowerHullScan
  exact foldl_grahamScanStep_chain sorted [] (by simp)

/--
Reading the stack output of `upperHullScan` from tail to head yields a CCW chain.

Symmetric to `lowerHullScan_reverse_isCCWChain`: the upper hull is built by scanning
the reversed sorted list, so the resulting stack also has strict left turns.
-/
lemma upperHullScan_reverse_isCCWChain (sorted : List (Point K)) :
    IsCCWChain (upperHullScan sorted).reverse := by
  unfold upperHullScan
  exact foldl_grahamScanStep_chain sorted.reverse [] (by simp)

/--
Construct a ConvexPolygon from a list of points by removing duplicates
    and keeping only extreme points of the convex hull.
    returns none if there are fewer than 3 extreme points. -/
def ConvexPolygon.ofList [DecidableEq K] (verts : List (Point K)) : Option (ConvexPolygon K) :=
  let hull := convexHullPoints verts
  if h_three : 3 ≤ hull.length then
    haveI : NeZero hull.length := ⟨by omega⟩
    let nondegen : NondegenPolygon K :=
      { vertex_count := hull.length
        vertex_count_pos := ⟨by omega⟩
        three_le_vertex_count := h_three
        vertices := hull.get
        nodup := by
          have hnodup : hull.Nodup := convexHullPoints_nodup verts
          intro i j hij
          exact (List.Nodup.get_inj_iff hnodup).mp hij }
    if h_convex : IsCCWPolygon nondegen.vertices then
      some { toNondegenPolygon := nondegen, vertices_extremePoints := h_convex }
    else none
  else none

/--
Membership in the open half-space strictly to the left of an edge `vᵢ → vᵢ₊₁`
is exactly the strict counterclockwise predicate.

This unfolds the layered definitions (`getStrictlyLeftHalfspace`, `toStrictlyLeft`,
`OpenHalfSpace.contains`, `dotProduct`, `rotate90Counterclockwise`, `crossProduct`,
`isStrictlyLeftOf`, `ccw`) into a single clean equality, so downstream proofs can
work directly with `Point.ccw`.
-/
lemma getStrictlyLeftHalfspace_contains_eq_ccw
    (ng : NondegenPolygon K) (i : Fin ng.vertex_count) (v : Point K) :
    (NondegenPolygon.getStrictlyLeftHalfspace ng i).contains v =
      Point.ccw (ng.vertices i) (ng.vertices (i + 1)) v := by
  unfold NondegenPolygon.getStrictlyLeftHalfspace Point.toStrictlyLeft
  unfold OpenHalfSpace.contains Point.ccw Point.isStrictlyLeftOf
  unfold Point.dotProduct Point.crossProduct
    Point.rotate90Counterclockwise
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply]
  congr 1
  ring

/-! ### Consequences of validation

`convexHullPoints` validates its output, so the strict convexity of that output —
and the chain properties that follow from it — are available with no correctness
proof for the monotone chain itself. -/

/-- Transport `IsCCWPolygon` along an equality of lists. -/
lemma isCCWPolygon_of_eq {L M : List (Point K)} (h : L = M) [NeZero L.length] [NeZero M.length]
    (hM : IsCCWPolygon (n := M.length) M.get) : IsCCWPolygon (n := L.length) L.get := by
  subst h; exact hM

/--
**Algorithm-correctness statement for `convexHullPoints`**: when the hull has at
least three vertices, every other vertex lies strictly left of every directed
edge of the hull.

This holds *by construction*: `convexHullPoints` returns a list of three or more
points only after checking exactly this property (see the `TODO` in its
docstring for what is left open, namely that the check never rejects).
-/
lemma convexHullPoints_convex [DecidableEq K] (verts : List (Point K))
    (h_three : 3 ≤ (convexHullPoints verts).length) :
    haveI : NeZero (convexHullPoints verts).length := ⟨by omega⟩
    IsCCWPolygon (n := (convexHullPoints verts).length)
      (convexHullPoints verts).get := by
  haveI : NeZero (convexHullPoints verts).length := ⟨by omega⟩
  set hull := convexHullFromSorted (sortPointsLex verts) with hhull
  by_cases h3 : 3 ≤ hull.length
  · haveI : NeZero hull.length := ⟨by omega⟩
    by_cases hccw : IsCCWPolygon (n := hull.length) hull.get
    · have hEq : convexHullPoints verts = hull := by
        rw [convexHullPoints, dif_pos h3, if_pos hccw]
      exact isCCWPolygon_of_eq hEq hccw
    · exfalso
      have hEq : convexHullPoints verts = [] := by
        rw [convexHullPoints, dif_pos h3, if_neg hccw]
      rw [hEq] at h_three
      simp at h_three
  · exfalso
    have hEq : convexHullPoints verts = hull := by
      rw [convexHullPoints, dif_neg h3]
    rw [hEq] at h_three
    exact h3 h_three

/-- A strictly convex counterclockwise cycle is in particular a counterclockwise
chain: consecutive triples are strict left turns. -/
lemma isCCWChain_of_isCCWPolygon {L : List (Point K)} (h3 : 3 ≤ L.length)
    [NeZero L.length] (h : IsCCWPolygon (n := L.length) L.get) : IsCCWChain L := by
  rw [IsCCWChain_iff_get]
  intro i hi
  have hone : ((1 : Fin L.length) : ℕ) = 1 := by
    change 1 % L.length = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hstep : (⟨i, by omega⟩ : Fin L.length) + 1 = ⟨i + 1, by omega⟩ := by
    apply Fin.ext
    rw [Fin.val_add, hone]
    change (i + 1) % L.length = i + 1
    exact Nat.mod_eq_of_lt (by omega)
  have hne1 : (⟨i + 2, by omega⟩ : Fin L.length) ≠ ⟨i, by omega⟩ := by
    simp only [ne_eq, Fin.mk.injEq]
    omega
  have hne2 : (⟨i + 2, by omega⟩ : Fin L.length) ≠ (⟨i, by omega⟩ : Fin L.length) + 1 := by
    rw [hstep]
    simp only [ne_eq, Fin.mk.injEq]
    omega
  have hccw := h ⟨i, by omega⟩ ⟨i + 2, by omega⟩ hne1 hne2
  rwa [hstep] at hccw

/--
Linear (non-wrap-around) chain on the convex hull output: every `i` with
`i + 2 < length` gives `ccw H[i] H[i+1] H[i+2] = true`.
-/
lemma convexHullPoints_isCCWChain [DecidableEq K] (verts : List (Point K)) :
    IsCCWChain (convexHullPoints verts) := by
  by_cases h3 : 3 ≤ (convexHullPoints verts).length
  · haveI : NeZero (convexHullPoints verts).length := ⟨by omega⟩
    exact isCCWChain_of_isCCWPolygon h3 (convexHullPoints_convex verts h3)
  · -- lists of length at most two are chains outright
    rw [IsCCWChain_iff_get]
    intro i hi
    omega

/--
Wrap-around triple at the end of the convex hull list:
the last two elements together with the first form a strict left turn.
-/
lemma convexHullPoints_wrap_end [DecidableEq K] (verts : List (Point K))
    (h_three : 3 ≤ (convexHullPoints verts).length) :
    Point.ccw
      ((convexHullPoints verts).get
        ⟨(convexHullPoints verts).length - 2, by omega⟩)
      ((convexHullPoints verts).get
        ⟨(convexHullPoints verts).length - 1, by omega⟩)
      ((convexHullPoints verts).get ⟨0, by omega⟩) = true := by
  haveI : NeZero (convexHullPoints verts).length := ⟨by omega⟩
  have hone : ((1 : Fin (convexHullPoints verts).length) : ℕ) = 1 := by
    change 1 % (convexHullPoints verts).length = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hstep : (⟨(convexHullPoints verts).length - 2, by omega⟩ :
      Fin (convexHullPoints verts).length) + 1
      = ⟨(convexHullPoints verts).length - 1, by omega⟩ := by
    apply Fin.ext
    rw [Fin.val_add, hone]
    change ((convexHullPoints verts).length - 2 + 1) % (convexHullPoints verts).length
      = (convexHullPoints verts).length - 1
    have hlt : (convexHullPoints verts).length - 2 + 1 < (convexHullPoints verts).length := by
      omega
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hne1 : (⟨0, by omega⟩ : Fin (convexHullPoints verts).length)
      ≠ ⟨(convexHullPoints verts).length - 2, by omega⟩ := by
    simp only [ne_eq, Fin.mk.injEq]
    omega
  have hne2 : (⟨0, by omega⟩ : Fin (convexHullPoints verts).length)
      ≠ (⟨(convexHullPoints verts).length - 2, by omega⟩ :
          Fin (convexHullPoints verts).length) + 1 := by
    rw [hstep]
    simp only [ne_eq, Fin.mk.injEq]
    omega
  have hccw := convexHullPoints_convex verts h_three
    ⟨(convexHullPoints verts).length - 2, by omega⟩ ⟨0, by omega⟩ hne1 hne2
  rwa [hstep] at hccw

/--
Wrap-around triple at the start of the convex hull list:
the last element together with the first two forms a strict left turn.
-/
lemma convexHullPoints_wrap_start [DecidableEq K] (verts : List (Point K))
    (h_three : 3 ≤ (convexHullPoints verts).length) :
    Point.ccw
      ((convexHullPoints verts).get
        ⟨(convexHullPoints verts).length - 1, by omega⟩)
      ((convexHullPoints verts).get ⟨0, by omega⟩)
      ((convexHullPoints verts).get ⟨1, by omega⟩) = true := by
  haveI : NeZero (convexHullPoints verts).length := ⟨by omega⟩
  have hone : ((1 : Fin (convexHullPoints verts).length) : ℕ) = 1 := by
    change 1 % (convexHullPoints verts).length = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hstep : (⟨(convexHullPoints verts).length - 1, by omega⟩ :
      Fin (convexHullPoints verts).length) + 1 = ⟨0, by omega⟩ := by
    apply Fin.ext
    rw [Fin.val_add, hone]
    have hsucc : (convexHullPoints verts).length - 1 + 1 = (convexHullPoints verts).length := by
      omega
    rw [hsucc, Nat.mod_self]
  have hne1 : (⟨1, by omega⟩ : Fin (convexHullPoints verts).length)
      ≠ ⟨(convexHullPoints verts).length - 1, by omega⟩ := by
    simp only [ne_eq, Fin.mk.injEq]
    omega
  have hne2 : (⟨1, by omega⟩ : Fin (convexHullPoints verts).length)
      ≠ (⟨(convexHullPoints verts).length - 1, by omega⟩ :
          Fin (convexHullPoints verts).length) + 1 := by
    rw [hstep]
    simp only [ne_eq, Fin.mk.injEq]
    omega
  have hccw := convexHullPoints_convex verts h_three
    ⟨(convexHullPoints verts).length - 1, by omega⟩ ⟨1, by omega⟩ hne1 hne2
  rwa [hstep] at hccw

/--
The convex hull algorithm produces a list whose cyclic consecutive triples are all
strict counterclockwise turns. Built from the linear chain plus the two wrap-around
triples.
-/
lemma convexHullPoints_isCyclicCCWChain [DecidableEq K] (verts : List (Point K))
    (h_three : 3 ≤ (convexHullPoints verts).length) :
    haveI : NeZero (convexHullPoints verts).length := ⟨by omega⟩
    IsCyclicCCWChain (n := (convexHullPoints verts).length)
      (convexHullPoints verts).get := by
  haveI : NeZero (convexHullPoints verts).length := ⟨by omega⟩
  have h_chain_raw : IsCCWChain (convexHullPoints verts) :=
    convexHullPoints_isCCWChain verts
  rw [IsCCWChain_iff_get] at h_chain_raw
  -- Abbreviation for convenience; using `let`/`have` so omega still sees the length
  -- through `(convexHullPoints verts).length`.
  intro i
  -- Goal: ccw (H.get i) (H.get (i+1)) (H.get (i+2)) = true where
  -- H = convexHullPoints verts and i : Fin H.length.
  -- Three cases on i.val vs H.length:
  -- (a) i.val + 2 < length: linear chain at i.val.
  -- (b) i.val = length - 2: wrap_end.
  -- (c) i.val = length - 1: wrap_start.
  have h_one_val : ((1 : Fin (convexHullPoints verts).length) : ℕ) = 1 := by
    change 1 % (convexHullPoints verts).length = 1
    exact Nat.mod_eq_of_lt (by omega)
  have h_two_val : ((2 : Fin (convexHullPoints verts).length) : ℕ) = 2 := by
    change 2 % (convexHullPoints verts).length = 2
    exact Nat.mod_eq_of_lt (by omega)
  have hi_lt : i.val < (convexHullPoints verts).length := i.isLt
  rcases lt_or_ge (i.val + 2) (convexHullPoints verts).length with h_lt | h_ge
  · -- Linear case: pull through `IsCCWChain_iff_get`.
    have hchain := h_chain_raw i.val h_lt
    have hi1_val : (i + 1).val = i.val + 1 := by
      rw [Fin.val_add, h_one_val]
      exact Nat.mod_eq_of_lt (by omega)
    have hi2_val : (i + 2).val = i.val + 2 := by
      rw [Fin.val_add, h_two_val]
      exact Nat.mod_eq_of_lt (by omega)
    have e1 : i + 1 = ⟨i.val + 1, by omega⟩ := Fin.ext hi1_val
    have e2 : i + 2 = ⟨i.val + 2, by omega⟩ := Fin.ext hi2_val
    rw [e1, e2]
    -- Goal: ccw (H.get i) (H.get ⟨i.val+1, _⟩) (H.get ⟨i.val+2, _⟩) = true
    -- And `H.get i` is the same as `H.get ⟨i.val, _⟩` since `i = ⟨i.val, i.isLt⟩` defeq.
    exact hchain
  · -- Wrap-around: i.val + 2 ≥ length, and i.val < length, so i.val ∈ {length - 2, length - 1}.
    have h_or : i.val = (convexHullPoints verts).length - 2 ∨
                i.val = (convexHullPoints verts).length - 1 := by omega
    rcases h_or with h_eq | h_eq
    · -- Case i.val = length - 2: triple is (H[length-2], H[length-1], H[0]).
      have hi1_val : (i + 1).val = (convexHullPoints verts).length - 1 := by
        rw [Fin.val_add, h_one_val, h_eq, Nat.mod_eq_of_lt (by omega)]
        omega
      have hi2_val : (i + 2).val = 0 := by
        rw [Fin.val_add, h_two_val, h_eq]
        have h_sum : (convexHullPoints verts).length - 2 + 2 =
            (convexHullPoints verts).length := by omega
        rw [h_sum, Nat.mod_self]
      have h_we := convexHullPoints_wrap_end verts h_three
      have e1 : i + 1 =
          ⟨(convexHullPoints verts).length - 1, by omega⟩ := Fin.ext hi1_val
      have e2 : i + 2 = ⟨0, by omega⟩ := Fin.ext hi2_val
      rw [e1, e2]
      have h_get_i : (convexHullPoints verts).get i =
          (convexHullPoints verts).get
            ⟨(convexHullPoints verts).length - 2, by omega⟩ := by
        congr 1
        exact Fin.ext h_eq
      rw [h_get_i]
      exact h_we
    · -- Case i.val = length - 1: triple is (H[length-1], H[0], H[1]).
      have hi1_val : (i + 1).val = 0 := by
        rw [Fin.val_add, h_one_val, h_eq]
        have h_sum : (convexHullPoints verts).length - 1 + 1 =
            (convexHullPoints verts).length := by omega
        rw [h_sum, Nat.mod_self]
      have hi2_val : (i + 2).val = 1 := by
        rw [Fin.val_add, h_two_val, h_eq]
        have h_sum : (convexHullPoints verts).length - 1 + 2 =
            (convexHullPoints verts).length + 1 := by omega
        rw [h_sum, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      have h_ws := convexHullPoints_wrap_start verts h_three
      have e1 : i + 1 = ⟨0, by omega⟩ := Fin.ext hi1_val
      have e2 : i + 2 = ⟨1, by omega⟩ := Fin.ext hi2_val
      rw [e1, e2]
      have h_get_i : (convexHullPoints verts).get i =
          (convexHullPoints verts).get
            ⟨(convexHullPoints verts).length - 1, by omega⟩ := by
        congr 1
        exact Fin.ext h_eq
      rw [h_get_i]
      exact h_ws

/-!
### A cyclic CCW chain need not be convex

It is tempting to believe that a list of distinct points whose every *cyclic
consecutive* triple turns counterclockwise must be strictly convex. This is
false: a star polygon (winding number `2`) has the same local turning behaviour
as a convex polygon. The pentagram below is an explicit rational counterexample,
so the convexity of `convexHullPoints` cannot be obtained from the chain
invariants alone — it needs the geometry of the monotone-chain algorithm (that
the two scans are `x`-monotone and meet at the extreme abscissae).
-/

/-- A rational pentagram: five points, listed in star order, approximating the
vertices of a regular pentagram on the circle of radius `10`. -/
def pentagram : Fin 5 → Point ℚ
  | 0 => ![10, 0]
  | 1 => ![-8, 6]
  | 2 => ![3, -9]
  | 3 => ![3, 9]
  | 4 => ![-8, -6]

lemma pentagram_injective : Function.Injective pentagram := by
  intro i j h
  have h1 := congrFun h 1
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exfalso; norm_num [pentagram] at h1)

/-- Every cyclic consecutive triple of the pentagram is a strict left turn. -/
lemma pentagram_isCyclicCCWChain : IsCyclicCCWChain pentagram := by
  intro i
  fin_cases i
  · change Point.ccw (pentagram 0) (pentagram 1) (pentagram 2) = true
    norm_num [pentagram, Point.ccw, Point.isStrictlyLeftOf, Point.crossProduct]
  · change Point.ccw (pentagram 1) (pentagram 2) (pentagram 3) = true
    norm_num [pentagram, Point.ccw, Point.isStrictlyLeftOf, Point.crossProduct]
  · change Point.ccw (pentagram 2) (pentagram 3) (pentagram 4) = true
    norm_num [pentagram, Point.ccw, Point.isStrictlyLeftOf, Point.crossProduct]
  · change Point.ccw (pentagram 3) (pentagram 4) (pentagram 0) = true
    norm_num [pentagram, Point.ccw, Point.isStrictlyLeftOf, Point.crossProduct]
  · change Point.ccw (pentagram 4) (pentagram 0) (pentagram 1) = true
    norm_num [pentagram, Point.ccw, Point.isStrictlyLeftOf, Point.crossProduct]

/-- The pentagram is nevertheless not convex: `v₃` lies strictly right of the
directed edge `v₀ → v₁`. -/
lemma pentagram_not_isCCWPolygon : ¬ IsCCWPolygon pentagram := by
  intro h
  have h03 : Point.ccw (pentagram 0) (pentagram 1) (pentagram 3) = true :=
    h 0 3 (by decide) (by decide)
  norm_num [pentagram, Point.ccw, Point.isStrictlyLeftOf, Point.crossProduct] at h03

/-- **`IsCyclicCCWChain` does not imply `IsCCWPolygon`**, even for injective
vertex families with `n ≥ 3`. -/
theorem not_forall_isCyclicCCWChain_imp_isCCWPolygon :
    ¬ ∀ (n : ℕ) (_ : NeZero n) (_ : 3 ≤ n) (vertices : Fin n → Point ℚ),
        Function.Injective vertices → IsCyclicCCWChain vertices → IsCCWPolygon vertices :=
  fun h => pentagram_not_isCCWPolygon
    (h 5 ⟨by omega⟩ (by omega) pentagram pentagram_injective pentagram_isCyclicCCWChain)

/--
If the convex hull has fewer than three vertices, `ConvexPolygon.ofList` returns
`none`. Immediate from the outer `if` guard.

The converse does *not* hold in general: `ofList` also returns `none` when the
hull has ≥ 3 vertices but the `IsCCWPolygon` check fails. (The algorithm-
correctness direction would close that gap, but it depends on
`convexHullPoints_convex`, which now holds by construction, but the guard is
still needed because validation could in principle reject; see the `TODO` in the
docstring of `convexHullPoints`.)
-/
lemma ConvexPolygon.ofList_eq_none_of_length_lt_three [DecidableEq K] (verts : List (Point K))
    (h : (convexHullPoints verts).length < 3) :
    ConvexPolygon.ofList (K := K) verts = none := by
  unfold ConvexPolygon.ofList
  rw [dif_neg (by omega)]

/--
Returns a list of closed half-spaces corresponding to the edges of the convex polygon.
If there are fewer than 3 vertices, returns none.
-/
def ConvexPolygon.toHalfSpaces (poly : ConvexPolygon K) : Option (List (ClosedHalfSpace K)) :=
  if h : poly.vertex_count < 3 then none
  else
    let edges := List.finRange poly.vertex_count
    let halfSpaces := edges.map (fun i =>
      let p1 := poly.vertices i
      let p2 := poly.vertices (i + ⟨1, by omega⟩)
      Point.toWeaklyLeft p1 p2 (poly.nodup.ne (Fin.ext_iff.not.mpr (by
        simp only [Fin.val_add]
        have hi := i.isLt
        rcases Nat.lt_or_ge (i.val + 1) poly.vertex_count with h1 | h1
        · rw [Nat.mod_eq_of_lt h1]; omega
        · have : i.val + 1 = poly.vertex_count := by omega
          rw [this, Nat.mod_self]; omega))))
    some halfSpaces

/--
Given a collection of half-spaces, construct the convex polygon defined by their intersection.
This is determined by taking all intersections of the boundary lines of pairs of half-spaces,
and then filtering to those that satisfy all half-space constraints.
-/
def ConvexPolygon.ofHalfSpaces [DecidableEq K] (halfSpaces : List (ClosedHalfSpace K)) :
    Option (ConvexPolygon K) :=
  let potentialVertices := halfSpaces.flatMap (fun h1 =>
    halfSpaces.filterMap (fun h2 => ClosedHalfSpace.lineIntersection h1 h2))
  let vertices := potentialVertices.filter (fun v => halfSpaces.all (fun h => h.contains v))
  (ConvexPolygon.ofList vertices)

/-- Decide whether the point `p` lies in the convex polygon `poly`. -/
def ConvexPolygon.contains (poly : ConvexPolygon K) (p : Point K) : Bool :=
  match poly.toHalfSpaces with
  | none => false
  | some halfSpaces => halfSpaces.all (fun h => h.contains p)

/-- Convex hull of a list of points, with the hull property **verified** at run
time: `ofList` is run and its result accepted only if it contains every input
point. -/
def ConvexPolygon.ofListChecked [DecidableEq K] (verts : List (Point K)) :
    Option (ConvexPolygon K) :=
  match ConvexPolygon.ofList verts with
  | none => none
  | some poly => if verts.all (fun p => poly.contains p) then some poly else none

lemma ConvexPolygon.ofListChecked_eq_some [DecidableEq K] {verts : List (Point K)}
    {poly : ConvexPolygon K} (h : ConvexPolygon.ofListChecked verts = some poly) :
    ConvexPolygon.ofList verts = some poly ∧ ∀ p ∈ verts, poly.contains p = true := by
  unfold ConvexPolygon.ofListChecked at h
  rcases hof : ConvexPolygon.ofList verts with _ | poly'
  · rw [hof] at h; simp at h
  · rw [hof] at h
    dsimp only at h
    by_cases hchk : verts.all (fun p => poly'.contains p) = true
    · rw [if_pos hchk] at h
      obtain rfl := Option.some.inj h
      exact ⟨rfl, fun p hp => List.all_eq_true.mp hchk p hp⟩
    · rw [if_neg hchk] at h; simp at h

/-- The vertices produced by `ofList` are among the input points. -/
lemma ConvexPolygon.vertices_mem_of_ofList [DecidableEq K] {verts : List (Point K)}
    {poly : ConvexPolygon K} (h : ConvexPolygon.ofList verts = some poly)
    (i : Fin poly.vertex_count) :
    poly.vertices i ∈ verts := by
  unfold ConvexPolygon.ofList at h
  dsimp only at h
  split_ifs at h with h3 hc
  obtain rfl := Option.some.inj h
  exact mem_of_mem_convexHullPoints (List.get_mem _ _)

/-- Decide whether every vertex of `p` lies in `q`, witnessing `p ⊆ q` for convex polygons. -/
def ConvexPolygon.isSubsetOf (p q : ConvexPolygon K) : Bool :=
  p.vertex_list.all (fun v => q.contains v)

namespace ConvexPolygon

/-- Shrink a convex polygon by moving each edge inward
by at least `dist` (in the normal direction).
and at most `dist + tolerance` (to account for numerical issues).

Specialised to `ℚ` because the inward-shift step uses `findRationalWithSquareBetween`
(see `ClosedHalfSpace.moveInward`).
-/
def shrink (poly : ConvexPolygon ℚ) (dist : ℚ) (tolerance : ℚ)
    (hdist : 0 < dist) (htol : 0 < tolerance) :
    Option (ConvexPolygon ℚ) :=
  let halfSpaces := poly.toHalfSpaces
  match halfSpaces with
  | none => none
  | some hs =>
    let movedHalfSpaces := hs.map (fun h => h.moveInward dist tolerance hdist htol)
    (ConvexPolygon.ofHalfSpaces movedHalfSpaces)

end ConvexPolygon

end
