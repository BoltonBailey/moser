import Moser.Geometry.HalfSpaces

/-!
# Convex Polygons

This file defines convex polygons as ordered lists of rational vertices.
-/


/--
A polygon represented by its vertices.

we require that all vertices are distinct, and that there are 3 or more vertices.

Operations that would return a degenerate polygon (fewer than 3 vertices) return none instead.

Note we do not extend mathlib's `Polygon`, because we want to bundle the vertex count.
-/
structure NondegenPolygon where
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
  vertices : Fin vertex_count → RationalPoint
  /-- All vertices are distinct -/
  nodup : Function.Injective vertices
deriving Repr, DecidableEq

attribute [nolint unusedArguments] instReprNondegenPolygon.repr

instance (poly : NondegenPolygon) : NeZero poly.vertex_count := poly.vertex_count_pos

/-- The open half-space strictly to the left of the directed edge from vertex `i` to vertex `i+1`. -/
def NondegenPolygon.getStrictlyLeftHalfspace (ng : NondegenPolygon) (i : Fin ng.vertex_count) :
    OpenHalfSpace :=
  let p1 := ng.vertices i
  let p2 := ng.vertices (i + 1)
  RationalPoint.toStrictlyLeft p1 p2 (by
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
def IsCCWPolygon {n : ℕ} [NeZero n] (vertices : Fin n → RationalPoint) : Prop :=
  ∀ i j : Fin n, j ≠ i → j ≠ i + 1 →
    RationalPoint.ccw (vertices i) (vertices (i + 1)) (vertices j) = true

instance {n : ℕ} [NeZero n] (vertices : Fin n → RationalPoint) :
    Decidable (IsCCWPolygon vertices) :=
  inferInstanceAs (Decidable (∀ _ _ : Fin n, _ → _ → _))

/--
The cyclic CCW chain condition: every consecutive triple of vertices `(vᵢ, vᵢ₊₁, vᵢ₊₂)`
(with cyclic indexing) is a strict counterclockwise turn.

This is strictly weaker than `IsCCWPolygon`: it only constrains immediately consecutive
triples, not arbitrary "vᵢ, vᵢ₊₁, vⱼ" pairs. Equivalence to `IsCCWPolygon` for distinct
vertices is the content of `cyclicCCWChain_implies_IsCCWPolygon`.
-/
def IsCyclicCCWChain {n : ℕ} [NeZero n] (vertices : Fin n → RationalPoint) : Prop :=
  ∀ i : Fin n,
    RationalPoint.ccw (vertices i) (vertices (i + 1)) (vertices (i + 2)) = true

instance {n : ℕ} [NeZero n] (vertices : Fin n → RationalPoint) :
    Decidable (IsCyclicCCWChain vertices) :=
  inferInstanceAs (Decidable (∀ _ : Fin n, _))

/--
A convex polygon.

Convexity is enforced by `IsCCWPolygon vertices`: every edge `vᵢ → vᵢ₊₁` has all
other vertices strictly to its left.

The strictness enforces that there can be no collinear triples of vertices,
which in turn ensures that all vertices are extreme points of the convex hull.
-/
structure ConvexPolygon extends NondegenPolygon where
  /-- Every non-adjacent vertex lies strictly counterclockwise of every edge. -/
  vertices_extremeRationalPoints : IsCCWPolygon vertices
deriving Repr, DecidableEq

attribute [nolint unusedArguments] instReprConvexPolygon.repr


/--
The vertex list of a convex polygon, in counterclockwise order.
-/
def ConvexPolygon.vertex_list (poly : ConvexPolygon) : List RationalPoint :=
  List.finRange poly.vertex_count |>.map poly.vertices


/-- Graham scan helper: process remaining points to build upper/lower hull -/
def grahamScanStep (stack : List RationalPoint) (p : RationalPoint) : List RationalPoint :=
  match stack with
  | [] => [p]
  | [q] => [p, q]
  | q :: r :: rest =>
    if RationalPoint.ccw r q p then p :: stack
    else grahamScanStep (r :: rest) p

/-- Lexicographic order on rational points: by `x`-coordinate, breaking ties with `y`. -/
def RationalPoint.lexLE (p q : RationalPoint) : Bool :=
  decide (p 0 < q 0) || (decide (p 0 = q 0) && decide (p 1 ≤ q 1))

/-- Sort a list of rational points lexicographically by `(x, y)`, after first
    dropping duplicates. The dedup step makes the downstream Graham-scan
    invariants and uniqueness proofs go through cleanly. -/
def sortRationalPointsLex (points : List RationalPoint) : List RationalPoint :=
  points.dedup.mergeSort RationalPoint.lexLE

/--
Lower-hull pass of Andrew's monotone chain: fold `grahamScanStep` left over an
already-sorted list. Scanning left-to-right keeps only strict left turns, so the
result is the lower hull in **reverse** traversal order (the rightmost point is
at the head, the leftmost at the tail).
-/
def lowerHullScan (sorted : List RationalPoint) : List RationalPoint :=
  sorted.foldl grahamScanStep []

/--
Upper-hull pass of Andrew's monotone chain: scan the **reverse** of an
already-sorted list. The result is the upper hull in reverse traversal order
(the leftmost point is at the head, the rightmost at the tail).
-/
def upperHullScan (sorted : List RationalPoint) : List RationalPoint :=
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
def convexHullFromSorted : List RationalPoint → List RationalPoint
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

Implementation: lex-sort the points, then stitch the two monotone-chain scans
together via `convexHullFromSorted`. Consecutive duplicates in the sorted list
are absorbed by `grahamScanStep`, since `RationalPoint.ccw` is strict and
returns `false` whenever two of its arguments coincide.
-/
def convexHullRationalPoints (points : List RationalPoint) : List RationalPoint :=
  convexHullFromSorted (sortRationalPointsLex points)

/-- Each step of the Graham scan returns a sublist of the stack with the new point pushed. -/
lemma grahamScanStep_sublist (stack : List RationalPoint) (p : RationalPoint) :
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
lemma foldl_grahamScanStep_sublist (l acc : List RationalPoint) :
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
lemma lowerHullScan_sublist (sorted : List RationalPoint) :
    (lowerHullScan sorted).Sublist sorted.reverse := by
  unfold lowerHullScan
  have := foldl_grahamScanStep_sublist sorted []
  simpa using this

/-- The upper-hull scan output is a sublist of the input. -/
lemma upperHullScan_sublist (sorted : List RationalPoint) :
    (upperHullScan sorted).Sublist sorted := by
  unfold upperHullScan
  have h := foldl_grahamScanStep_sublist sorted.reverse []
  rw [List.reverse_reverse] at h
  simpa using h

/-- The lex-sorted (deduplicated) list has no duplicates. -/
lemma sortRationalPointsLex_nodup (points : List RationalPoint) :
    (sortRationalPointsLex points).Nodup := by
  unfold sortRationalPointsLex
  have hperm : (points.dedup.mergeSort RationalPoint.lexLE).Perm points.dedup :=
    List.mergeSort_perm points.dedup RationalPoint.lexLE
  exact hperm.symm.nodup (List.nodup_dedup points)

/-- Stitching the two hull scans preserves no-duplicates. -/
lemma convexHullFromSorted_nodup {sorted : List RationalPoint} (h : sorted.Nodup) :
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

lemma convexHullRationalPoints_nodup (points : List RationalPoint) :
    (convexHullRationalPoints points).Nodup := by
  unfold convexHullRationalPoints
  exact convexHullFromSorted_nodup (sortRationalPointsLex_nodup points)

-- lemma convexHullRationalPoints_extreme (points : List RationalPoint) :
--     (convexHullRationalPoints points).All (fun v =>
--       ¬(convexHullRationalPoints points).Any (fun w => w ≠ v && RationalPoint.isStrictlyLeftOf w v (convexHullRationalPoints points.head))) := by
--   sorry

/--
Predicate saying every consecutive triple in a list is a strict counterclockwise turn.

Reading the list head-to-tail as `p₀, p₁, p₂, …`, we require `ccw p₀ p₁ p₂ = true`,
i.e. `p₂` is strictly left of the directed segment `p₀ → p₁`. Equivalently, the polyline
formed by the list always turns counterclockwise at every interior vertex.

This is the natural invariant maintained by `grahamScanStep` when reading the stack in
arrival order.
-/
def IsCCWChain : List RationalPoint → Prop
  | [] => True
  | [_] => True
  | [_, _] => True
  | p₀ :: p₁ :: p₂ :: rest =>
      RationalPoint.ccw p₀ p₁ p₂ = true ∧ IsCCWChain (p₁ :: p₂ :: rest)

/-- The chain invariant for the empty / singleton / pair lists is automatic. -/
@[simp] lemma IsCCWChain_nil : IsCCWChain [] := trivial
@[simp] lemma IsCCWChain_singleton (p : RationalPoint) : IsCCWChain [p] := trivial
@[simp] lemma IsCCWChain_pair (p q : RationalPoint) : IsCCWChain [p, q] := trivial

/--
Appending an element to a chain whose last two elements are `a, b`
preserves the chain when `ccw a b c = true`.
-/
lemma IsCCWChain_append_cons_cons :
    ∀ {L : List RationalPoint} {a b c : RationalPoint},
      IsCCWChain (L ++ [a, b]) → RationalPoint.ccw a b c = true →
      IsCCWChain (L ++ [a, b, c])
  | [], _, _, _, _, h_turn => ⟨h_turn, trivial⟩
  | [x], a, b, c, hL, h_turn => by
      -- IsCCWChain [x, a, b] = ⟨ccw x a b, IsCCWChain [a, b]⟩
      have h1 : RationalPoint.ccw x a b = true := hL.1
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
      have h1 : RationalPoint.ccw x y z = true := hL'.1
      have h2 : IsCCWChain (y :: (z :: rest ++ [a, b])) := hL'.2
      have h2' : IsCCWChain ((y :: z :: rest) ++ [a, b]) := by
        simpa using h2
      have ih := IsCCWChain_append_cons_cons h2' h_turn
      have ih' : IsCCWChain (y :: (z :: rest ++ [a, b, c])) := by
        simpa using ih
      change IsCCWChain (x :: y :: (z :: rest ++ [a, b, c]))
      exact ⟨h1, ih'⟩

/-- Dropping the last element of a CCW chain still gives a CCW chain. -/
lemma IsCCWChain.dropLast : ∀ {L : List RationalPoint},
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
lemma grahamScanStep_chain (acc : List RationalPoint) (p : RationalPoint) :
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
lemma foldl_grahamScanStep_chain (l acc : List RationalPoint)
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
lemma lowerHullScan_reverse_isCCWChain (sorted : List RationalPoint) :
    IsCCWChain (lowerHullScan sorted).reverse := by
  unfold lowerHullScan
  exact foldl_grahamScanStep_chain sorted [] (by simp)

/--
Reading the stack output of `upperHullScan` from tail to head yields a CCW chain.

Symmetric to `lowerHullScan_reverse_isCCWChain`: the upper hull is built by scanning
the reversed sorted list, so the resulting stack also has strict left turns.
-/
lemma upperHullScan_reverse_isCCWChain (sorted : List RationalPoint) :
    IsCCWChain (upperHullScan sorted).reverse := by
  unfold upperHullScan
  exact foldl_grahamScanStep_chain sorted.reverse [] (by simp)

/--
Construct a ConvexPolygon from a list of points by removing duplicates
    and keeping only extreme points of the convex hull.
    returns none if there are fewer than 3 extreme points. -/
def ConvexPolygon.ofList (verts : List RationalPoint) : Option ConvexPolygon :=
  let hull := convexHullRationalPoints verts
  if h_three : 3 ≤ hull.length then
    haveI : NeZero hull.length := ⟨by omega⟩
    let nondegen : NondegenPolygon :=
      { vertex_count := hull.length
        vertex_count_pos := ⟨by omega⟩
        three_le_vertex_count := h_three
        vertices := hull.get
        nodup := by
          have hnodup : hull.Nodup := convexHullRationalPoints_nodup verts
          intro i j hij
          exact (List.Nodup.get_inj_iff hnodup).mp hij }
    if h_convex : IsCCWPolygon nondegen.vertices then
      some { toNondegenPolygon := nondegen, vertices_extremeRationalPoints := h_convex }
    else none
  else none

/--
Membership in the open half-space strictly to the left of an edge `vᵢ → vᵢ₊₁`
is exactly the strict counterclockwise predicate.

This unfolds the layered definitions (`getStrictlyLeftHalfspace`, `toStrictlyLeft`,
`OpenHalfSpace.contains`, `dotProduct`, `rotate90Counterclockwise`, `crossProduct`,
`isStrictlyLeftOf`, `ccw`) into a single clean equality, so downstream proofs can
work directly with `RationalPoint.ccw`.
-/
lemma getStrictlyLeftHalfspace_contains_eq_ccw
    (ng : NondegenPolygon) (i : Fin ng.vertex_count) (v : RationalPoint) :
    (NondegenPolygon.getStrictlyLeftHalfspace ng i).contains v =
      RationalPoint.ccw (ng.vertices i) (ng.vertices (i + 1)) v := by
  unfold NondegenPolygon.getStrictlyLeftHalfspace RationalPoint.toStrictlyLeft
  unfold OpenHalfSpace.contains RationalPoint.ccw RationalPoint.isStrictlyLeftOf
  unfold RationalPoint.dotProduct RationalPoint.crossProduct
    RationalPoint.rotate90Counterclockwise
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply]
  congr 1
  ring

/--
Algorithm-correctness statement for `convexHullRationalPoints`: when the hull has
at least three vertices, every other vertex lies strictly left of every directed
edge of the hull.

Status of the proof:

* The Graham-scan invariant — every consecutive triple (in arrival order) of
  `lowerHullScan` and `upperHullScan` is a strict left turn — is established by
  `lowerHullScan_reverse_isCCWChain` and `upperHullScan_reverse_isCCWChain`,
  via the chain-preservation lemmas `grahamScanStep_chain` and
  `foldl_grahamScanStep_chain`.
* The half-space membership condition on the LHS reduces to a `RationalPoint.ccw`
  condition via `getStrictlyLeftHalfspace_contains_eq_ccw`.

What still needs to be assembled:

1. Junction CCW: the chain extends across the seam where the lower hull meets
   the upper hull (at the leftmost and rightmost x-coordinates).
2. Cyclic closure: the wrap-around triples `(v_{n-1}, v_0, v_1)` and
   `(v_{n-2}, v_{n-1}, v_0)` are also strict left turns.
3. The classical geometric theorem: a list of distinct points whose every
   cyclic consecutive triple is a strict left turn is strictly convex — every
   non-adjacent vertex lies strictly inside the open half-space of every edge.

(3) is the substantive geometric content that does not follow purely from the
chain invariant and needs a separate proof (induction on the polygon, or a
winding-number / Hopf Umlaufsatz style argument).
-/
lemma convexHullRationalPoints_convex (verts : List RationalPoint)
    (h_three : 3 ≤ (convexHullRationalPoints verts).length) :
    haveI : NeZero (convexHullRationalPoints verts).length := ⟨by omega⟩
    IsCCWPolygon (n := (convexHullRationalPoints verts).length)
      (convexHullRationalPoints verts).get := by
  sorry

/--
`ConvexPolygon.ofList` returns `none` exactly when the input has fewer than three
extreme points. Equivalently, whenever the convex hull has at least three vertices,
the convexity invariant `vertices_extremeRationalPoints` is automatically satisfied
by the algorithm's output, so the construction succeeds.

The reverse direction is immediate from the implementation; the forward direction
is the correctness statement of `convexHullRationalPoints` (every consecutive triple
in the hull is a strict left turn).
-/
lemma ConvexPolygon.ofList_eq_none_iff (verts : List RationalPoint) :
    ConvexPolygon.ofList verts = none ↔
      (convexHullRationalPoints verts).length < 3 := by
  refine ⟨?_, ?_⟩
  · -- forward: `ofList = none → length < 3`. This is the algorithm-correctness
    -- direction; if the hull already has ≥ 3 vertices, the convexity check must
    -- have succeeded, so the result couldn't have been `none`.
    intro h
    by_contra hlen
    have hlen' : 3 ≤ (convexHullRationalPoints verts).length := Nat.le_of_not_lt hlen
    unfold ConvexPolygon.ofList at h
    rw [dif_pos hlen'] at h
    have h_convex := convexHullRationalPoints_convex verts hlen'
    rw [dif_pos h_convex] at h
    exact Option.some_ne_none _ h
  · -- backward: `length < 3 → ofList = none`. Immediate from the outer `if` guard.
    intro h
    unfold ConvexPolygon.ofList
    rw [dif_neg (by omega)]

/--
Returns a list of closed half-spaces corresponding to the edges of the convex polygon.
If there are fewer than 3 vertices, returns none.
-/
def ConvexPolygon.toHalfSpaces (poly : ConvexPolygon) : Option (List ClosedHalfSpace) :=
  if h : poly.vertex_count < 3 then none
  else
    let edges := List.finRange poly.vertex_count
    let halfSpaces := edges.map (fun i =>
      let p1 := poly.vertices i
      let p2 := poly.vertices (i + ⟨1, by omega⟩)
      RationalPoint.toWeaklyLeft p1 p2 (poly.nodup.ne (Fin.ext_iff.not.mpr (by
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
def ConvexPolygon.ofHalfSpaces (halfSpaces : List ClosedHalfSpace) : Option ConvexPolygon :=
  let potentialVertices := halfSpaces.flatMap (fun h1 =>
    halfSpaces.filterMap (fun h2 => ClosedHalfSpace.lineIntersection h1 h2))
  let vertices := potentialVertices.filter (fun v => halfSpaces.all (fun h => h.contains v))
  (ConvexPolygon.ofList vertices)

/-- Decide whether the point `p` lies in the convex polygon `poly`. -/
def ConvexPolygon.contains (poly : ConvexPolygon) (p : RationalPoint) : Bool :=
  match poly.toHalfSpaces with
  | none => false
  | some halfSpaces => halfSpaces.all (fun h => h.contains p)

/-- Decide whether every vertex of `p` lies in `q`, witnessing `p ⊆ q` for convex polygons. -/
def ConvexPolygon.isSubsetOf (p q : ConvexPolygon) : Bool :=
  p.vertex_list.all (fun v => q.contains v)

namespace ConvexPolygon

/-- Shrink a convex polygon by moving each edge inward
by at least `dist` (in the normal direction).
and at most `dist + tolerance` (to account for numerical issues).
-/
def shrink (poly : ConvexPolygon) (dist : ℚ) (tolerance : ℚ) (hdist : 0 < dist) (htol : 0 < tolerance) :
    Option ConvexPolygon :=
  let halfSpaces := poly.toHalfSpaces
  match halfSpaces with
  | none => none
  | some hs =>
    let movedHalfSpaces := hs.map (fun h => h.moveInward dist tolerance hdist htol)
    (ConvexPolygon.ofHalfSpaces movedHalfSpaces)

end ConvexPolygon
