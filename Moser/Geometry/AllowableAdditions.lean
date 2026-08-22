module

public import Moser.Geometry.HalfSpaces
public import Moser.Geometry.Polygon
public import Moser.Geometry.PolygonArea

public section

/-!
# Allowable Additions

Given a convex polygon `P`, an area threshold `A_*`, and a tolerance `τ > 0`,
this file describes the region of the plane such that adjoining a point in
that region to `P` and taking the convex hull keeps the resulting area below
`A_*`. The region is described as the intersection of a finite collection of
closed half-spaces, one for each ordered pair of (distinct) vertices of `P`.

For each ordered pair of vertices `(V_i, V_j)` we compute the *growable
distance* `d`: a number in `K`, within tolerance `τ` of the unique exact
value `d_*` for which `A_R + T(d_*) = A_*`, where

* `A_R` is the area of `P` weakly to the right of the directed line `V_i → V_j`,
* `T(d)` is the area of the triangle with base `V_i V_j` and height `d`.

Equivalently, the area of the convex hull of `P ∪ {p}` where `p` is at
left-distance `d_*` from the directed line `V_i V_j` equals `A_*`. The
*growth half-space* of `(V_i, V_j)` is the closed half-space of points at
signed left-distance at most `d` from the directed line: it is bounded by the
line parallel to `V_i V_j` at perpendicular distance `d` on its left, and lies
weakly to the right of that shifted line. The *growth half-space intersection*
is the intersection over all ordered pairs of distinct vertices.

Although `d_* = 2·(A_* − A_R)/|V_i V_j|` is irrational, the growth half-space
itself is exactly rational: `p` is at left-distance at most `d_*` iff
`crossProduct (V_j − V_i) (p − V_i) ≤ 2·(A_* − A_R)` (both sides are twice a
triangle area over the base `V_i V_j`). So `growthHalfspace` is exact and
tolerance-free; the tolerance only enters `growableDistance`, which converts
the constraint into an explicit distance and is kept for the blueprint spec.

The main lemma is that any point lying strictly outside the growth
half-space intersection produces a convex hull whose area exceeds `A_*`.
-/

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [DecidableEq K]

namespace ConvexPolygon

/-- The signed side of a point with respect to the directed line `V_i → V_j`:
positive strictly left, negative strictly right, zero on the line. -/
def sideOfVertexPair (poly : ConvexPolygon K) (i j : Fin poly.vertex_count) (p : Point K) : K :=
  Point.crossProduct (poly.vertices j - poly.vertices i) (p - poly.vertices i)

/--
Sutherland–Hodgman clip of the (counterclockwise, cyclic) vertex chain of `P`
against the closed half-plane weakly to the right of the directed line
`V_i → V_j`. For each directed edge `a → b` of `P` we emit `a` when `a` is weakly
right, and the intersection of `a b` with the line when the edge crosses it.
-/
def rightClippedChain (poly : ConvexPolygon K) (i j : Fin poly.vertex_count) : List (Point K) :=
  let pts := poly.vertex_list
  (pts.zip (pts.rotate 1)).flatMap fun ab =>
    let sa := sideOfVertexPair poly i j ab.1
    let sb := sideOfVertexPair poly i j ab.2
    (if sa ≤ 0 then [ab.1] else []) ++
    (if decide (sa ≤ 0) != decide (sb ≤ 0) then
      [ab.1 + (sa / (sa - sb)) • (ab.2 - ab.1)] else [])

/--
The area of the convex polygon `P` lying weakly to the right of the directed
line through vertices `V_i → V_j` (not necessarily adjacent).

Implementation: the hull of the Sutherland–Hodgman clip `rightClippedChain`,
built with the *verified* hull `ConvexPolygon.ofListChecked` and measured by the
shoelace formula; `0` when that hull is degenerate (in particular when `P` lies
weakly left of the line).

Using the verified hull is what makes this quantity usable in proofs: it is a
*lower bound* for the true area of the part of `P` weakly right of the line
(`Moser.areaWeaklyRightOfVertexPair_le`) without any correctness proof for the
clipping algorithm, since every point of the clipped chain demonstrably lies in
`P` and weakly right of the line.
-/
def areaWeaklyRightOfVertexPair
    (poly : ConvexPolygon K) (i j : Fin poly.vertex_count) (_hij : i ≠ j) : K :=
  match ConvexPolygon.ofListChecked (rightClippedChain poly i j) with
  | some q => q.area
  | none => 0

/-- Unfolding lemma for `sideOfVertexPair`, usable from other modules. -/
lemma sideOfVertexPair_eq (poly : ConvexPolygon K) (i j : Fin poly.vertex_count) (p : Point K) :
    sideOfVertexPair poly i j p =
      Point.crossProduct (poly.vertices j - poly.vertices i) (p - poly.vertices i) := by
  simp [sideOfVertexPair]

/-- The clipped area, when the verified hull of the clipped chain succeeds. -/
lemma areaWeaklyRightOfVertexPair_of_some {poly : ConvexPolygon K} {i j : Fin poly.vertex_count}
    (hij : i ≠ j) {q : ConvexPolygon K}
    (h : ConvexPolygon.ofListChecked (rightClippedChain poly i j) = some q) :
    areaWeaklyRightOfVertexPair poly i j hij = q.area := by
  rw [areaWeaklyRightOfVertexPair, h]

/-- The clipped area is `0` when the verified hull of the clipped chain is
degenerate. -/
lemma areaWeaklyRightOfVertexPair_of_none {poly : ConvexPolygon K} {i j : Fin poly.vertex_count}
    (hij : i ≠ j)
    (h : ConvexPolygon.ofListChecked (rightClippedChain poly i j) = none) :
    areaWeaklyRightOfVertexPair poly i j hij = 0 := by
  rw [areaWeaklyRightOfVertexPair, h]

/-! ## The points emitted by the clipping -/

/-- The interpolation parameter used by the clipping lies in `[0,1]`, and the
interpolated point lies exactly on the clipping line. -/
private lemma clip_param_bounds {sa sb : K} (h : (decide (sa ≤ 0) != decide (sb ≤ 0)) = true) :
    0 ≤ sa / (sa - sb) ∧ sa / (sa - sb) ≤ 1 ∧ sa + (sa / (sa - sb)) * (sb - sa) = 0 := by
  have hne : ¬ ((sa ≤ 0) ↔ (sb ≤ 0)) := by
    simp only [bne_iff_ne, ne_eq, decide_eq_decide] at h
    exact h
  rcases le_or_gt sa 0 with hA | hA
  · have hB : 0 < sb := by
      by_contra hcon
      exact hne ⟨fun _ => not_lt.mp hcon, fun _ => hA⟩
    have hden : sa - sb < 0 := by linarith
    have hdne : sa - sb ≠ 0 := ne_of_lt hden
    have key : sa / (sa - sb) = (-sa) / (sb - sa) := by
      rw [← neg_div_neg_eq]
      ring_nf
    refine ⟨?_, ?_, ?_⟩
    · rw [key]; exact div_nonneg (by linarith) (by linarith)
    · rw [key, div_le_one (by linarith)]; linarith
    · field_simp
      try ring
  · have hB : sb ≤ 0 := by
      by_contra hcon
      exact hne ⟨fun hx => absurd hx (not_le.mpr hA), fun hx => absurd hx hcon⟩
    have hden : 0 < sa - sb := by linarith
    have hdne : sa - sb ≠ 0 := ne_of_gt hden
    refine ⟨div_nonneg hA.le hden.le, ?_, ?_⟩
    · rw [div_le_one hden]; linarith
    · field_simp
      try ring

/-- Every point emitted by the clipping is either a vertex of the polygon that is
weakly right of the line, or a point on an edge between two vertices that lies
exactly on the line. -/
lemma mem_rightClippedChain_cases {poly : ConvexPolygon K} {i j : Fin poly.vertex_count}
    {z : Point K} (hz : z ∈ rightClippedChain poly i j) :
    (z ∈ poly.vertex_list ∧ sideOfVertexPair poly i j z ≤ 0) ∨
      (∃ a ∈ poly.vertex_list, ∃ b ∈ poly.vertex_list, ∃ l : K, 0 ≤ l ∧ l ≤ 1 ∧
        z = a + l • (b - a) ∧ sideOfVertexPair poly i j z ≤ 0) := by
  rw [rightClippedChain, List.mem_flatMap] at hz
  obtain ⟨ab, hab, hz⟩ := hz
  obtain ⟨ha, hb⟩ := List.of_mem_zip hab
  have hb' : ab.2 ∈ poly.vertex_list := List.mem_rotate.mp hb
  dsimp only at hz
  rcases List.mem_append.mp hz with h | h
  · split_ifs at h with hs
    · rw [List.mem_singleton] at h
      subst h
      exact Or.inl ⟨ha, hs⟩
    · simp at h
  · split_ifs at h with hcross
    · rw [List.mem_singleton] at h
      obtain ⟨hl0, hl1, hzero⟩ := clip_param_bounds hcross
      refine Or.inr ⟨ab.1, ha, ab.2, hb', _, hl0, hl1, h, ?_⟩
      -- the interpolated point lies on the line
      have haff : sideOfVertexPair poly i j
          (ab.1 + (sideOfVertexPair poly i j ab.1 /
            (sideOfVertexPair poly i j ab.1 - sideOfVertexPair poly i j ab.2)) • (ab.2 - ab.1))
          = sideOfVertexPair poly i j ab.1
            + (sideOfVertexPair poly i j ab.1 /
                (sideOfVertexPair poly i j ab.1 - sideOfVertexPair poly i j ab.2))
              * (sideOfVertexPair poly i j ab.2 - sideOfVertexPair poly i j ab.1) := by
        simp only [sideOfVertexPair, Point.crossProduct, Pi.add_apply, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul]
        ring
      rw [h, haff, hzero]
    · simp at h

/--
The growable distance to the left of the directed line `V_i → V_j` at
tolerance `τ`. This is a nonnegative element `d` such that
`A_R + T(d) ≥ A_*` (where `A_R` is the area of `P` weakly to the right of
the directed line `V_i V_j` and `T(d)` is the area of the triangle with
vertices `V_i, V_j` and a point at perpendicular distance `d` to the left of
the line), and such that `d` is within tolerance `τ` of the unique exact
value `d_*` for which equality `A_R + T(d_*) = A_*` holds.

Implementation: the exact value is `d_* = 2·(A_* − A_R)/L` with `L = |V_i V_j|`
irrational, so we return `2·(A_* − A_R)/L₋` for a rational lower approximation
`L₋ ≤ L` produced by `findRationalWithSquareBetween`, giving `d ≥ d_*` (so
`A_R + T(d) ≥ A_*` errs on the safe side). The approximation window shrinks
with `tolerance` (via the `ratio` factor below) so that the overshoot `d − d_*`
is within the tolerance. When `A_R ≥ A_*` we return `0`.

Specialised to `ℚ` because the lower approximation of the irrational edge
length uses `findRationalWithSquareBetween` (cf. `ClosedHalfSpace.moveInward`).
-/
def growableDistance
    (poly : ConvexPolygon ℚ) (areaThreshold tolerance : ℚ) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) : ℚ :=
  let lenSq := Point.lengthSq (poly.vertices j - poly.vertices i)
  have hlen : 0 < lenSq :=
    Point.lengthSq_pos_of_ne _
      (sub_ne_zero.mpr fun h => hij (poly.nodup h).symm)
  let excess := areaThreshold - areaWeaklyRightOfVertexPair poly i j hij
  if hex : excess ≤ 0 then 0
  else
    have hex' : 0 < excess := lt_of_not_ge hex
    let m := min lenSq 1
    have hm : 0 < m := lt_min hlen one_pos
    let ratio := tolerance * m / (tolerance * m + 2 * excess)
    have hden : 0 < tolerance * m + 2 * excess := by positivity
    have hratio1 : ratio < 1 := by
      rw [div_lt_one hden]
      nlinarith
    have hratio0 : 0 < ratio := by positivity
    2 * excess /
      findRationalWithSquareBetween (lenSq * (1 - ratio)) lenSq
        (by nlinarith) (by nlinarith)

/-- The growable distance is nonnegative. -/
lemma growableDistance_nonneg
    (poly : ConvexPolygon ℚ) (areaThreshold tolerance : ℚ) (htol : 0 < tolerance)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) :
    0 ≤ growableDistance poly areaThreshold tolerance htol i j hij := by
  simp only [growableDistance]
  split_ifs with hex
  · exact le_rfl
  · exact le_of_lt (div_pos (by linarith [lt_of_not_ge hex])
      (findRationalWithSquareBetween_positive _ _ _ _))

/--
The growth half-space of the ordered pair of vertices `(V_i, V_j)`: the closed
half-space of points at signed left-distance at most `growableDistance` (as
`tolerance → 0`) from the directed line `V_i → V_j` — that is, the half-space
bounded by the line parallel to `V_i → V_j` at perpendicular distance `d_*` on
its left, lying weakly to the *right* of that shifted line. A point strictly
outside it is so far to the left of `V_i → V_j` that the hull of `P ∪ {p}`
contains, beyond the part of `P` weakly right of the line (area `A_R`), a
triangle over the base `V_i V_j` of height `> d_*`, pushing the area past the
threshold.

The construction is exact and rational (see the module docstring): the
half-space is `{p | crossProduct (V_j − V_i) (p − V_i) ≤ 2·(A_* − A_R)}`,
realized by shifting the basepoint of the weakly-right half-space of
`V_i → V_j` to the left by `(2·excess / |V_i V_j|²) · rot90(V_j − V_i)`.
When `A_R ≥ A_*` the excess is clamped to `0`, giving the half-space weakly
to the right of the directed segment itself (a conservative superset of the
true, empty-interior constraint — always on the safe side for the containment
spec).
-/
def growthHalfspace
    (poly : ConvexPolygon K) (areaThreshold : K)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) : ClosedHalfSpace K :=
  let vi := poly.vertices i
  let vj := poly.vertices j
  let excess := max 0 (areaThreshold - areaWeaklyRightOfVertexPair poly i j hij)
  let leftNormal := Point.rotate90Counterclockwise (vj - vi)
  { basepoint := vi + (2 * excess / Point.lengthSq (vj - vi)) • leftNormal
    normal := Point.rotate90Counterclockwise (vi - vj)
    normal_pos := by
      rw [Point.lengthSq_rotate90Counterclockwise]
      exact Point.lengthSq_pos_of_ne _ (sub_ne_zero.mpr fun h => hij (poly.nodup h)) }

/--
A computable wrapper around `growthHalfspace` that does not depend on a proof
that `i ≠ j`. When `i = j` we return an arbitrary default closed half-space
(the whole-plane representation is not at hand, so we just pick a fixed
half-space to keep this total). This is only used to enumerate the per-pair
half-spaces over `List.finRange poly.vertex_count` without carrying the
`i ≠ j` proof through the iteration.
-/
def growthHalfspaceOfPair
    (poly : ConvexPolygon K) (areaThreshold : K)
    (i j : Fin poly.vertex_count) : ClosedHalfSpace K :=
  if hij : i ≠ j then
    growthHalfspace poly areaThreshold i j hij
  else
    -- Default: a fixed half-space, chosen so the structure is well-formed.
    -- Concretely, the closed half-space `{ p | p₀ ≥ 0 }`.
    { basepoint := ![0, 0]
      normal := ![1, 0]
      normal_pos := by
        unfold Point.lengthSq
        simp }

/-- The growth half-space test, in closed form: `p` passes exactly when its
signed area contribution over the base `V_i V_j` is at most twice the excess. -/
lemma contains_growthHalfspace_iff (poly : ConvexPolygon K) (areaThreshold : K)
    (i j : Fin poly.vertex_count) (hij : i ≠ j) (p : Point K) :
    (growthHalfspace poly areaThreshold i j hij).contains p = true ↔
      Point.crossProduct (poly.vertices j - poly.vertices i) (p - poly.vertices i)
        ≤ 2 * max 0 (areaThreshold - areaWeaklyRightOfVertexPair poly i j hij) := by
  have hne : poly.vertices j - poly.vertices i ≠ 0 :=
    sub_ne_zero.mpr fun h => hij (poly.nodup h).symm
  have hLne : (poly.vertices j 0 - poly.vertices i 0) * (poly.vertices j 0 - poly.vertices i 0)
      + (poly.vertices j 1 - poly.vertices i 1) * (poly.vertices j 1 - poly.vertices i 1) ≠ 0 := by
    have hL := Point.lengthSq_pos_of_ne _ hne
    simpa [Point.lengthSq, Pi.sub_apply] using ne_of_gt hL
  set L : K := (poly.vertices j 0 - poly.vertices i 0) * (poly.vertices j 0 - poly.vertices i 0)
      + (poly.vertices j 1 - poly.vertices i 1) * (poly.vertices j 1 - poly.vertices i 1) with hLdef
  set e : K := max 0 (areaThreshold - areaWeaklyRightOfVertexPair poly i j hij) with hedef
  have hdot0 : Point.dotProduct (growthHalfspace poly areaThreshold i j hij).normal
      (p - (growthHalfspace poly areaThreshold i j hij).basepoint)
      = 2 * e / L * L
        - Point.crossProduct (poly.vertices j - poly.vertices i) (p - poly.vertices i) := by
    simp only [growthHalfspace, Point.dotProduct, Point.rotate90Counterclockwise,
      Point.crossProduct, Point.lengthSq, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hLdef, hedef]
    ring
  have hdot : Point.dotProduct (growthHalfspace poly areaThreshold i j hij).normal
      (p - (growthHalfspace poly areaThreshold i j hij).basepoint)
      = 2 * e - Point.crossProduct (poly.vertices j - poly.vertices i) (p - poly.vertices i) := by
    rw [hdot0, div_mul_cancel₀ _ hLne]
  simp only [ClosedHalfSpace.contains, decide_eq_true_eq, ge_iff_le, hdot]
  constructor <;> intro h <;> linarith

/-! ### Comparing half-spaces -/

/-- A decidable sufficient condition for the inclusion `h' ⊆ h` of closed
half-spaces: the normals are parallel and equally oriented, and the basepoint of
`h'` lies in `h`. -/
def _root_.ClosedHalfSpace.subsetTest (h' h : ClosedHalfSpace K) : Bool :=
  decide (Point.crossProduct h.normal h'.normal = 0) &&
    decide (0 < Point.dotProduct h.normal h'.normal) &&
      decide (0 ≤ Point.dotProduct h.normal (h'.basepoint - h.basepoint))

/-- `subsetTest` is sound: it witnesses `h' ⊆ h`. -/
lemma _root_.ClosedHalfSpace.contains_of_subsetTest {h' h : ClosedHalfSpace K}
    (hsub : h'.subsetTest h = true) {p : Point K} (hp : h'.contains p = true) :
    h.contains p = true := by
  simp only [ClosedHalfSpace.subsetTest, Bool.and_eq_true, decide_eq_true_eq] at hsub
  obtain ⟨⟨hcross, hdot⟩, hbase⟩ := hsub
  simp only [ClosedHalfSpace.contains, decide_eq_true_eq, ge_iff_le] at hp ⊢
  have hm : 0 < Point.lengthSq h'.normal := h'.normal_pos
  -- `⟨n, p - b'⟩ * ‖m‖² = ⟨n, m⟩ * ⟨m, p - b'⟩ - (n × m) * (m × (p - b'))`
  have hkey : Point.dotProduct h.normal (p - h'.basepoint) * Point.lengthSq h'.normal
      = Point.dotProduct h.normal h'.normal * Point.dotProduct h'.normal (p - h'.basepoint)
        - Point.crossProduct h.normal h'.normal
          * Point.crossProduct h'.normal (p - h'.basepoint) := by
    simp only [Point.dotProduct, Point.crossProduct, Point.lengthSq, Pi.sub_apply]
    ring
  have hnu : 0 ≤ Point.dotProduct h.normal (p - h'.basepoint) := by
    rw [hcross, zero_mul, sub_zero] at hkey
    nlinarith [hkey, hm, hdot, hp]
  have hsplit : Point.dotProduct h.normal (p - h.basepoint)
      = Point.dotProduct h.normal (p - h'.basepoint)
        + Point.dotProduct h.normal (h'.basepoint - h.basepoint) := by
    simp only [Point.dotProduct, Pi.sub_apply]
    ring
  rw [hsplit]
  linarith

/-! ### The growth half-space intersection, verified -/

/-- The list of growth half-spaces of all ordered pairs of distinct vertices. -/
def growthHalfspaceList (poly : ConvexPolygon K) (areaThreshold : K) : List (ClosedHalfSpace K) :=
  let indices := List.finRange poly.vertex_count
  indices.flatMap (fun i =>
    (indices.filter (fun j => decide (i ≠ j))).map (fun j =>
      growthHalfspaceOfPair poly areaThreshold i j))

/-- The growth half-space intersection, accepted only when each of its own edge
half-spaces is verified to contain one of the growth half-spaces — which makes
the polygon a superset of the true intersection, so that a point outside it is
outside some growth half-space. -/
def growthHalfspaceIntersectionChecked (poly : ConvexPolygon K) (areaThreshold : K) :
    Option (ConvexPolygon K) :=
  let hs := growthHalfspaceList poly areaThreshold
  match ConvexPolygon.ofHalfSpaces hs with
  | none => none
  | some q =>
    match q.toHalfSpaces with
    | none => none
    | some qhs =>
      if qhs.all (fun hq => hs.any (fun h => h.subsetTest hq)) then some q else none

/-- **A point outside the verified growth half-space intersection is outside one
of the growth half-spaces.** -/
lemma exists_growthHalfspace_not_contains {poly : ConvexPolygon K} {areaThreshold : K}
    {q : ConvexPolygon K} (hq : growthHalfspaceIntersectionChecked poly areaThreshold = some q)
    {p : Point K} (hp : q.contains p = false) :
    ∃ (i j : Fin poly.vertex_count) (hij : i ≠ j),
      (growthHalfspace poly areaThreshold i j hij).contains p = false := by
  set hs := growthHalfspaceList poly areaThreshold with hsdef
  -- unpack the checked construction
  rw [growthHalfspaceIntersectionChecked] at hq
  try dsimp only at hq
  rcases hofhs : ConvexPolygon.ofHalfSpaces hs with _ | q'
  · rw [hofhs] at hq; simp at hq
  rw [hofhs] at hq
  try dsimp only at hq
  rcases hths : q'.toHalfSpaces with _ | qhs
  · rw [hths] at hq; simp at hq
  rw [hths] at hq
  try dsimp only at hq
  by_cases hchk : (qhs.all (fun hq' => hs.any (fun h => h.subsetTest hq'))) = true
  swap
  · rw [if_neg hchk] at hq; simp at hq
  rw [if_pos hchk] at hq
  obtain rfl := Option.some.inj hq
  -- some edge half-space of `q` rejects `p`
  have hrej : ∃ hq' ∈ qhs, hq'.contains p = false := by
    rw [ConvexPolygon.contains, hths] at hp
    dsimp only at hp
    by_contra hcon
    push Not at hcon
    have hall : qhs.all (fun h => h.contains p) = true := by
      rw [List.all_eq_true]
      intro x hx
      simpa using hcon x hx
    rw [hall] at hp
    simp at hp
  obtain ⟨hq', hq'mem, hq'rej⟩ := hrej
  -- the check supplies a growth half-space contained in it
  obtain ⟨h, hmem, hsub⟩ : ∃ h ∈ hs, h.subsetTest hq' = true := by
    have := (List.all_eq_true.mp hchk) hq' hq'mem
    simpa using this
  have hhrej : h.contains p = false := by
    by_contra hcase
    rw [Bool.not_eq_false] at hcase
    rw [ClosedHalfSpace.contains_of_subsetTest hsub hcase] at hq'rej
    simp at hq'rej
  -- read off the pair of vertices
  rw [hsdef, growthHalfspaceList, List.mem_flatMap] at hmem
  obtain ⟨i, -, hmem⟩ := hmem
  rw [List.mem_map] at hmem
  obtain ⟨j, hj, rfl⟩ := hmem
  have hij : i ≠ j := by
    have := List.of_mem_filter hj
    simpa using this
  refine ⟨i, j, hij, ?_⟩
  rwa [growthHalfspaceOfPair, dif_pos hij] at hhrej

/-!
### Threshold violated outside a growth half-space

If a point `p` lies strictly outside the growth half-space of an ordered pair of
distinct vertices `(V_i, V_j)` of `P`, then the area of the convex hull of
`P ∪ {p}` strictly exceeds the threshold.

This is proved downstream in `Moser.Real.ClippedArea` as
`Moser.areaThreshold_lt_area_of_outside_growthHalfspace`, where the real-plane
machinery is available: the hull contains both the part of `P` weakly right of
the line `V_i → V_j` — of area at least `areaWeaklyRightOfVertexPair`, by
`Moser.areaWeaklyRightOfVertexPair_le` — and the triangle `V_i V_j p`, whose area
exceeds the remaining excess by `contains_growthHalfspace_iff`; the two meet only
in the line `V_i V_j`, so their areas add.

The statement there is about `ConvexPolygon.ofListChecked`, the run-time-verified
hull, rather than `ConvexPolygon.ofList`: the shoelace area of the output of the
unverified hull algorithm carries no information (see `convexHullPoints_convex`).
-/

/--
The growth half-space intersection associated to `P`, `A_*`, and `τ`: the
convex polygon (if any) obtained by intersecting the per-pair growth
half-spaces over all ordered pairs `(V_i, V_j)` of distinct vertices of `P`.

The pair list is enumerated by iterating `List.finRange poly.vertex_count`
twice and filtering to ordered pairs `i ≠ j`. The resulting list of closed
half-spaces is fed to `ConvexPolygon.ofHalfSpaces`, which returns `none` if
the intersection is degenerate.
-/
def growthHalfspaceIntersection
    (poly : ConvexPolygon K) (areaThreshold : K) :
    Option (ConvexPolygon K) :=
  let indices := List.finRange poly.vertex_count
  let halfSpaces : List (ClosedHalfSpace K) :=
    indices.flatMap (fun i =>
      (indices.filter (fun j => decide (i ≠ j))).map (fun j =>
        growthHalfspaceOfPair poly areaThreshold i j))
  ConvexPolygon.ofHalfSpaces halfSpaces

/-!
### Threshold violated outside the growth half-space intersection

If `growthHalfspaceIntersectionChecked` returns `some q` and a point `p` lies
outside `q`, then the area of the convex hull of `P ∪ {p}` exceeds the
threshold. This is proved downstream in `Moser.Real.ClippedArea` as
`Moser.areaThreshold_lt_area_of_outside_growthHalfspaceIntersection`, by
combining `exists_growthHalfspace_not_contains` with the single-half-space
bound.

The *checked* intersection is what makes this work: `ConvexPolygon.ofHalfSpaces`
is not proved correct, so a point outside its output need not be outside the
true intersection. The run-time check verifies that each edge half-space of the
output contains one of the growth half-spaces, which is exactly what the
argument needs.
-/

end ConvexPolygon

end
