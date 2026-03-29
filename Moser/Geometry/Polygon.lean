import Mathlib

/-!
# Convex Polygons

This file defines convex polygons as ordered lists of rational vertices.
-/

/-- A point in the plane with rational coordinates -/
abbrev RationalPoint := (Fin 2) → ℚ

namespace RationalPoint

/-- Squared distance between two points (avoids square roots) -/
def distSq (p q : RationalPoint) : ℚ :=
  let dx := p 0 - q 0
  let dy := p 1 - q 1
  dx * dx + dy * dy

/-- Cross product of two 2D vectors (returns scalar) -/
def crossProduct (u v : RationalPoint) : ℚ := u 0 * v 1 - u 1 * v 0

/-- Dot product of two 2D vectors -/
def dotProduct (u v : RationalPoint) : ℚ := u 0 * v 0 + u 1 * v 1

/-- Euclidean length squared of a vector -/
def lengthSq (v : RationalPoint) : ℚ := v 0 * v 0 + v 1 * v 1

lemma lengthSq_nonneg (v : RationalPoint) : 0 ≤ lengthSq v := by
  unfold lengthSq
  nlinarith


/-- Check if a point is strictly to the left of the directed line from p1 to p2.
    Uses the cross product: positive means left, negative means right, zero means collinear. -/
def isStrictlyLeftOf (p p1 p2 : RationalPoint) : Bool :=
  crossProduct (p2 - p1) (p - p1) > 0

/-- Check if three points are in counterclockwise order -/
def ccw (p1 p2 p3 : RationalPoint) : Bool := isStrictlyLeftOf p3 p1 p2

def rotate90Counterclockwise (p : RationalPoint) : RationalPoint :=
  ![ -p 1, p 0 ]

lemma lengthSq_rotate90Counterclockwise (v : RationalPoint) :
    lengthSq (rotate90Counterclockwise v) = lengthSq v := by
  simp [lengthSq, rotate90Counterclockwise, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma lengthSq_pos_of_ne (v : RationalPoint) (hv : v ≠ 0) : 0 < lengthSq v := by
  simp only [lengthSq]
  by_contra h
  push_neg at h
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  exact hv (funext (fun i => by fin_cases i <;> simp_all))

end RationalPoint

structure ClosedHalfSpace where
  basepoint : RationalPoint
  /--
  The normal, where if the dot product of this with (p - basepoint) is nonnegative,
  then p is in the half-space.
  -/
  normal : RationalPoint
  /-- The normal must be nonzero (positive squared length). -/
  normal_pos : 0 < RationalPoint.lengthSq normal

-- def ClosedHalfSpace.boundingLine (half : ClosedHalfSpace) : Line := sorry

/--
Given two closed half-spaces, compute the intersection point of their boundary lines if it exists.
Returns none if the lines are parallel (no intersection or infinite intersection).
-/
def ClosedHalfSpace.lineIntersection (h1 h2 : ClosedHalfSpace) : Option RationalPoint := sorry

def ClosedHalfSpace.contains (h : ClosedHalfSpace) (p : RationalPoint) : Bool :=
  RationalPoint.dotProduct h.normal (p - h.basepoint) ≥ 0

def RationalPoint.toWeaklyLeft (p1 p2 : RationalPoint) (hne : p1 ≠ p2) : ClosedHalfSpace :=
  { basepoint := p1, normal := RationalPoint.rotate90Counterclockwise (p2 - p1),
    normal_pos := by
      rw [RationalPoint.lengthSq_rotate90Counterclockwise]
      exact RationalPoint.lengthSq_pos_of_ne _ (sub_ne_zero.mpr (Ne.symm hne)) }

def RationalPoint.toWeaklyRight (p1 p2 : RationalPoint) (hne : p1 ≠ p2) : ClosedHalfSpace :=
  { basepoint := p1, normal := RationalPoint.rotate90Counterclockwise (p1 - p2),
    normal_pos := by
      rw [RationalPoint.lengthSq_rotate90Counterclockwise]
      exact RationalPoint.lengthSq_pos_of_ne _ (sub_ne_zero.mpr hne) }

/--
Helper function to find a positive rational number whose square is between two given rationals.
Assumes `0 ≤ lower` and `lower < upper`.

Construction: Let `N = ⌈(upper+1)/(upper-lower)⌉ + 1` and `m = Nat.sqrt ⌊N²·lower⌋ + 1`.
Return `m / N`. The choice of `N` ensures `N·(√upper − √lower) ≥ 1`, which bounds `m` above by
`N·√upper`, so `(m/N)² ≤ upper`. The floor construction ensures `(m/N)² > lower`.
-/
def findRationalWithSquareBetween (lower upper : ℚ) (h0 : 0 ≤ lower) (hlt : lower < upper) : ℚ :=
  let d := upper - lower
  let N : ℕ := (⌈(upper + 1) / d⌉).toNat + 1
  let lF : ℕ := (⌊lower * (N : ℚ) ^ 2⌋).toNat
  (Nat.sqrt lF + 1 : ℚ) / N

lemma findRationalWithSquareBetween_positive (lower upper : ℚ)
    (h0 : 0 ≤ lower) (hlt : lower < upper) :
    0 < findRationalWithSquareBetween lower upper h0 hlt := by
  unfold findRationalWithSquareBetween
  apply div_pos
  · positivity
  · exact_mod_cast Nat.succ_pos _

/-- Key bound: `N ≥ (upper+1)/(upper-lower)` as rationals -/
private lemma findRat_N_bound (lower upper : ℚ) (h0 : 0 ≤ lower) (hlt : lower < upper) :
    (upper + 1) / (upper - lower) ≤
    ((⌈(upper + 1) / (upper - lower)⌉).toNat + 1 : ℕ) := by
  have hd : (0 : ℚ) < upper - lower := by linarith
  have hceil_pos : (0 : ℤ) < ⌈(upper + 1) / (upper - lower)⌉ :=
    Int.ceil_pos.mpr (div_pos (by linarith) hd)  -- upper > lower ≥ 0, so upper + 1 > 0
  have hceil_nn : (0 : ℤ) ≤ ⌈(upper + 1) / (upper - lower)⌉ := le_of_lt hceil_pos
  have hcast : ((⌈(upper + 1) / (upper - lower)⌉.toNat : ℕ) : ℤ) =
               ⌈(upper + 1) / (upper - lower)⌉ := Int.toNat_of_nonneg hceil_nn
  calc (upper + 1) / (upper - lower)
      ≤ (⌈(upper + 1) / (upper - lower)⌉ : ℚ) := Int.le_ceil _
    _ = ((⌈(upper + 1) / (upper - lower)⌉.toNat : ℕ) : ℚ) := by exact_mod_cast hcast.symm
    _ ≤ ((⌈(upper + 1) / (upper - lower)⌉.toNat + 1 : ℕ) : ℚ) := by
        exact_mod_cast Nat.le_succ _

/-- `√x ≤ (x+1)/2` for `x ≥ 0` (AM-GM with 1) -/
private lemma sqrt_le_half_add_one (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ≤ (x + 1) / 2 := by
  nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1)]

/-- `√upper + √lower ≤ upper + 1` -/
private lemma sqrt_sum_le (lower upper : ℚ) (h0 : 0 ≤ lower) (hlt : lower < upper) :
    Real.sqrt (upper : ℝ) + Real.sqrt (lower : ℝ) ≤ (upper : ℝ) + 1 := by
  have h0' : (0 : ℝ) ≤ lower := by exact_mod_cast h0
  have hlt' : (lower : ℝ) < upper := by exact_mod_cast hlt
  have h_upper_nn : (0 : ℝ) ≤ upper := le_of_lt (lt_of_le_of_lt h0' hlt')
  have := sqrt_le_half_add_one upper h_upper_nn
  have := sqrt_le_half_add_one lower h0'
  linarith [show (lower : ℝ) ≤ upper from le_of_lt hlt']

lemma findRationalWithSquareBetween_spec (lower upper : ℚ)
    (h0 : 0 ≤ lower) (hlt : lower < upper) :
    let r := findRationalWithSquareBetween lower upper h0 hlt
    lower ≤ r * r ∧ r * r ≤ upper := by
  simp only [findRationalWithSquareBetween]
  set d := upper - lower with hd_def
  set N : ℕ := (⌈(upper + 1) / d⌉).toNat + 1
  set lF : ℕ := (⌊lower * (N : ℚ) ^ 2⌋).toNat
  set m : ℕ := Nat.sqrt lF + 1
  -- Abbreviations in ℝ
  set sqL := Real.sqrt (lower : ℝ)
  set sqU := Real.sqrt (upper : ℝ)
  have hd : (0 : ℚ) < d := by simp [hd_def]; linarith
  have h0' : (0 : ℝ) ≤ (lower : ℝ) := by exact_mod_cast h0
  have hlt' : (lower : ℝ) < (upper : ℝ) := by exact_mod_cast hlt
  have h_upper_nn : (0 : ℝ) ≤ (upper : ℝ) := le_of_lt (lt_of_le_of_lt h0' hlt')
  have hN_pos : (0 : ℚ) < N := by exact_mod_cast Nat.succ_pos _
  -- lF = ⌊lower * N²⌋ with key floor facts
  have hlF_nn : (0 : ℤ) ≤ ⌊lower * (N : ℚ) ^ 2⌋ :=
    Int.floor_nonneg.mpr (by positivity)
  have hlF_cast : ((lF : ℕ) : ℤ) = ⌊lower * (N : ℚ) ^ 2⌋ :=
    Int.toNat_of_nonneg hlF_nn
  have hlF_le : (lF : ℚ) ≤ lower * (N : ℚ) ^ 2 := by
    have h1 : (⌊lower * (N : ℚ) ^ 2⌋ : ℚ) ≤ lower * (N : ℚ) ^ 2 := Int.floor_le _
    have h2 : ((lF : ℕ) : ℚ) = ((⌊lower * (N : ℚ) ^ 2⌋ : ℤ) : ℚ) := by exact_mod_cast hlF_cast
    linarith [h2 ▸ h1]
  have hlF_lt : lower * (N : ℚ) ^ 2 < (lF : ℚ) + 1 := by
    have h1 : lower * (N : ℚ) ^ 2 < (⌊lower * (N : ℚ) ^ 2⌋ : ℚ) + 1 := Int.lt_floor_add_one _
    have h2 : ((lF : ℕ) : ℚ) = ((⌊lower * (N : ℚ) ^ 2⌋ : ℤ) : ℚ) := by exact_mod_cast hlF_cast
    linarith [h2 ▸ h1]
  -- Nat.sqrt key facts: lF < m*m and Nat.sqrt(lF)*Nat.sqrt(lF) ≤ lF
  have hm_sq_gt : lF < m * m := Nat.sqrt_lt.mp (Nat.lt_succ_self _)
  have hsqrt_sq : Nat.sqrt lF * Nat.sqrt lF ≤ lF := by
    rw [← not_lt, ← Nat.sqrt_lt]; exact lt_irrefl _
  -- Cast m = Nat.sqrt lF + 1 to ℚ and ℝ
  have hm_eq : (m : ℚ) = (Nat.sqrt lF : ℚ) + 1 := by norm_cast
  have hm_eq_R : (m : ℝ) = (Nat.sqrt lF : ℝ) + 1 := by norm_cast
  -- Lower bound: lower ≤ (m/N)²
  refine ⟨?_, ?_⟩
  · -- lower ≤ (m/N)*(m/N)
    rw [div_mul_div_comm]
    have h2 : (lF : ℚ) + 1 ≤ (m : ℚ) * m := by exact_mod_cast Nat.succ_le_of_lt hm_sq_gt
    have h_key : lower * ((N : ℚ) * N) ≤ (m : ℚ) * m := by nlinarith [hlF_lt]
    have hNN : (0 : ℚ) < (N : ℚ) * N := by positivity
    rw [← hm_eq, le_div_iff₀ hNN]
    linarith
  · -- Upper bound: (m/N)*(m/N) ≤ upper
    rw [div_mul_div_comm]
    have hNN : (0 : ℚ) < (N : ℚ) * N := by positivity
    -- Suffices to show m * m ≤ upper * (N * N)
    suffices h : (m : ℚ) * m ≤ upper * ((N : ℚ) * N) by
      rw [← hm_eq, div_le_iff₀ hNN]; linarith
    -- Prove m * m ≤ upper * N * N via Real.sqrt
    -- Step 1: (Nat.sqrt lF : ℝ) ≤ N * √lower
    have hsqrtlF_le : (Nat.sqrt lF : ℝ) ≤ (N : ℝ) * Real.sqrt lower := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ Nat.sqrt lF),
          ← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (N : ℝ) * Real.sqrt lower)]
      apply Real.sqrt_le_sqrt
      have h1 : (Nat.sqrt lF : ℝ) * Nat.sqrt lF ≤ (lF : ℝ) := by exact_mod_cast hsqrt_sq
      have h2 : (lF : ℝ) ≤ (lower : ℝ) * (N : ℝ) ^ 2 := by exact_mod_cast hlF_le
      nlinarith [Real.sq_sqrt h0', Real.sqrt_nonneg (lower : ℝ)]
    -- Step 2: 1 ≤ N * (√upper - √lower)
    have hgap : 1 ≤ (N : ℝ) * (Real.sqrt upper - Real.sqrt lower) := by
      have hsum_pos : 0 < Real.sqrt upper + Real.sqrt lower := by
        have := Real.sqrt_pos.mpr (lt_of_le_of_lt h0' hlt')
        linarith [Real.sqrt_nonneg (lower : ℝ)]
      have hsum_le : Real.sqrt upper + Real.sqrt lower ≤ (upper : ℝ) + 1 :=
        sqrt_sum_le lower upper h0 hlt
      have hfactor : (Real.sqrt upper - Real.sqrt lower) * (Real.sqrt upper + Real.sqrt lower) =
                     (upper : ℝ) - lower := by
        linear_combination Real.mul_self_sqrt h_upper_nn - Real.mul_self_sqrt h0'
      have hN_bound : ((upper : ℝ) + 1) / ((upper : ℝ) - lower) ≤ (N : ℝ) :=
        by exact_mod_cast findRat_N_bound lower upper h0 hlt
      have hUL_R : (0 : ℝ) < (upper : ℝ) - lower := by exact_mod_cast hd
      have hN_UL : (upper : ℝ) + 1 ≤ (N : ℝ) * ((upper : ℝ) - lower) :=
        (div_le_iff₀ hUL_R).mp hN_bound
      -- N*(√U-√L)*(√U+√L) = N*(U-L) ≥ U+1 ≥ √U+√L, so N*(√U-√L) ≥ 1
      have hprod : Real.sqrt upper + Real.sqrt lower ≤
          (N : ℝ) * (Real.sqrt upper - Real.sqrt lower) * (Real.sqrt upper + Real.sqrt lower) :=
        calc Real.sqrt upper + Real.sqrt lower
            ≤ (upper : ℝ) + 1 := hsum_le
          _ ≤ (N : ℝ) * ((upper : ℝ) - lower) := hN_UL
          _ = (N : ℝ) * ((Real.sqrt upper - Real.sqrt lower) * (Real.sqrt upper + Real.sqrt lower)) := by
              rw [hfactor]
          _ = (N : ℝ) * (Real.sqrt upper - Real.sqrt lower) * (Real.sqrt upper + Real.sqrt lower) := by
              ring
      apply le_of_mul_le_mul_right _ hsum_pos
      linarith
    -- Step 3: m ≤ N * √upper
    have hm_le : (m : ℝ) ≤ (N : ℝ) * Real.sqrt upper := by
      rw [hm_eq_R]; linarith [hsqrtlF_le, hgap]
    -- Conclude: m * m ≤ upper * N * N
    have hkey : ((m : ℚ) * m : ℝ) ≤ ((upper * ((N : ℚ) * N) : ℚ) : ℝ) := by
      push_cast
      have := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ (m : ℝ)) hm_le
      nlinarith [Real.mul_self_sqrt h_upper_nn]
    exact_mod_cast hkey

/--
Change the half-space by moving the basepoint inward by at least `dist` in the normal direction,
and at most `dist + tolerance` to account for numerical issues.
-/
def ClosedHalfSpace.moveInward (h : ClosedHalfSpace) (dist tolerance : ℚ) (hdist : 0 < dist) (htol : 0 < tolerance) :
    ClosedHalfSpace :=
  let sqLen := RationalPoint.lengthSq h.normal
  -- compute a scaling of the direction
  -- so that it is of length at least dist but at no more than (dist+tolerance)
  -- I.e. we must scale by a factor statisfying
  -- `dist/length < scaleFactor < (dist+tolerance)/length`
  -- put another way, we need
  -- `dist^2/sqLen < scaleFactor^2 < (dist+tolerance)^2/sqLen`
  let scaleFactor : ℚ :=
    findRationalWithSquareBetween
      (dist * dist / sqLen) ((dist + tolerance) * (dist + tolerance) / sqLen)
      (by
        have : 0 ≤ h.normal.lengthSq := RationalPoint.lengthSq_nonneg h.normal
        have : 0 ≤ dist * dist := by nlinarith
        positivity
      ) (by
        -- have : 0 < h.normal.lengthSq := by exact h.normal_pos
        have : 0 < sqLen := by exact h.normal_pos
        -- have : 0 ≤ dist * dist := by nlinarith
        field_simp
        nlinarith)
  let scaledDirection : RationalPoint := ![h.normal 0 * scaleFactor, h.normal 1 * scaleFactor]
  { basepoint := h.basepoint + scaledDirection, normal := h.normal,
    normal_pos := h.normal_pos }

structure OpenHalfSpace where
  basepoint : RationalPoint
  /-- The direction -/
  normal : RationalPoint

def OpenHalfSpace.contains (h : OpenHalfSpace) (p : RationalPoint) : Bool :=
  RationalPoint.dotProduct h.normal (p - h.basepoint) > 0

def RationalPoint.toStrictlyLeft (p1 p2 : RationalPoint) : OpenHalfSpace :=
  { basepoint := p1, normal := RationalPoint.rotate90Counterclockwise (p2 - p1) }



/-- A convex polygon represented by its vertices in counterclockwise order.
We allow degenerate polygons of 0, 1, or 2 vertices,
but require that all vertices are distinct,
and in counterclockwise order for 3 or more vertices.
-/
structure ConvexPolygon where
  vertex_count : ℕ
  /-- The vertices of the polygon in counterclockwise order -/
  vertices : Fin vertex_count → RationalPoint
  /-- All vertices are distinct -/
  nodup : Function.Injective vertices
  /-- Counterclockwise -/
  vertices_extremeRationalPoints : ∀ i j k : Fin vertex_count,
    i < j → j < k →
      RationalPoint.ccw (vertices i) (vertices j) (vertices k) = true
deriving Repr, DecidableEq

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

/-- Compute the convex hull of a list of points using a Graham-scan-like algorithm.
    Returns vertices in counterclockwise order. -/
def convexHullRationalPoints (points : List RationalPoint) : List RationalPoint :=
  if points.length ≤ 1 then points
  else
    -- Sort by x-coordinate, then y-coordinate
    let sorted := points.mergeSort (fun p q => p 0 < q 0 || (p 0 == q 0 && p 1 ≤ q 1))
    -- Build lower hull (left to right)
    let lower := sorted.foldl grahamScanStep []
    -- Build upper hull (right to left)
    let upper := sorted.reverse.foldl grahamScanStep []
    -- Combine, removing duplicate endpoints
    match lower.reverse, upper.reverse with
    | [], u => u
    | l, [] => l
    | l, u => l ++ u.tail


/-- Filter a list to keep only points that are on the convex hull boundary -/
def filterToExtremeRationalPoints (points : List RationalPoint) : List RationalPoint :=
  let hull := convexHullRationalPoints points
  points.filter (fun p => hull.contains p)

/-- Construct a ConvexPolygon from a list of points by removing duplicates
    and keeping only extreme points of the convex hull. -/
def ConvexPolygon.ofList (vertices : List RationalPoint) : ConvexPolygon where
  vertex_count := (filterToExtremeRationalPoints vertices).length
  vertices := fun i => (filterToExtremeRationalPoints vertices).get ⟨i, by omega⟩
  nodup := by
    sorry
  vertices_extremeRationalPoints := by
    sorry

/--
Returns a list of closed half-spaces corresponding to the edges of the convex polygon.
If there are fewer than 3 vertices,
returns none since we cannot define half-spaces for degenerate polygons.
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
  some (ConvexPolygon.ofList vertices)

def ConvexPolygon.contains (poly : ConvexPolygon) (p : RationalPoint) : Bool :=
  match poly.toHalfSpaces with
  | none => false
  | some halfSpaces => halfSpaces.all (fun h => h.contains p)

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
