import Moser.Geometry.RationalPoint
import Moser.Geometry.RationalUtility

/-!
# Half Spaces and Lines

This file defines closed and open half-spaces and lines over points in an
ordered field `K`.
-/

variable {K : Type*}

section

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A closed half-space in `K²`, given by a basepoint and an inward-pointing normal. -/
structure ClosedHalfSpace (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- A point on the boundary line of the half-space. -/
  basepoint : Point K
  /--
  The normal, where if the dot product of this with (p - basepoint) is nonnegative,
  then p is in the half-space.
  -/
  normal : Point K
  /-- The normal must be nonzero (positive squared length). -/
  normal_pos : 0 < Point.lengthSq normal

/-- An open half-space in `K²`, given by a basepoint and an inward-pointing normal. -/
structure OpenHalfSpace (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- A point on the boundary line of the half-space. -/
  basepoint : Point K
  /--
  The normal, where if the dot product of this with (p - basepoint) is positive,
  then p is in the half-space.
  -/
  normal : Point K
  /-- The normal must be nonzero (positive squared length). -/
  normal_pos : 0 < Point.lengthSq normal

/-- Decide whether the point `p` lies in the open half-space `h`. -/
def OpenHalfSpace.contains (h : OpenHalfSpace K) (p : Point K) : Bool :=
  Point.dotProduct h.normal (p - h.basepoint) > 0

/-- The open half-space strictly to the left of the directed segment from `p1` to `p2`. -/
def Point.toStrictlyLeft (p1 p2 : Point K) (hne : p1 ≠ p2) : OpenHalfSpace K :=
  { basepoint := p1, normal := Point.rotate90Counterclockwise (p2 - p1),
    normal_pos := by
      rw [Point.lengthSq_rotate90Counterclockwise]
      exact Point.lengthSq_pos_of_ne _ (sub_ne_zero.mpr (Ne.symm hne)) }

/-- A line in `K²`, given by a point on the line and a nonzero direction vector. -/
structure Line (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- A point lying on the line. -/
  point : Point K
  /-- A nonzero direction vector for the line. -/
  direction : Point K
  /-- direction must be nonzero -/
  direction_pos : 0 < Point.lengthSq direction

/-- Decide whether two lines `l1` and `l2` are parallel (cross product of directions is zero). -/
def Line.parallel (l1 l2 : Line K) : Bool :=
  Point.crossProduct l1.direction l2.direction = 0

/--
Note AI generated
-/
def Line.intersection (l1 l2 : Line K) : Option (Point K) :=
  if l1.parallel l2 then none
  else
    let d := Point.crossProduct l1.direction l2.direction
    let t := Point.crossProduct (l2.point - l1.point) l2.direction / d
    some (l1.point + t • l1.direction)

/-- The boundary line of a closed half-space (perpendicular to its normal). -/
def ClosedHalfSpace.boundaryLine (h : ClosedHalfSpace K) : Line K :=
  { point := h.basepoint, direction := Point.rotate90Counterclockwise h.normal,
    direction_pos := by
      rw [Point.lengthSq_rotate90Counterclockwise]
      exact h.normal_pos }

/--
Given two closed half-spaces, compute the intersection point of their boundary lines if it exists.
Returns none if the lines are parallel (no intersection or infinite intersection).
-/
def ClosedHalfSpace.lineIntersection (h1 h2 : ClosedHalfSpace K) : Option (Point K) :=
  Line.intersection (h1.boundaryLine) (h2.boundaryLine)

/-- Decide whether the point `p` lies in the closed half-space `h`. -/
def ClosedHalfSpace.contains (h : ClosedHalfSpace K) (p : Point K) : Bool :=
  Point.dotProduct h.normal (p - h.basepoint) ≥ 0

/-- The closed half-space weakly to the left of the directed segment from `p1` to `p2`. -/
def Point.toWeaklyLeft (p1 p2 : Point K) (hne : p1 ≠ p2) : ClosedHalfSpace K :=
  { basepoint := p1, normal := Point.rotate90Counterclockwise (p2 - p1),
    normal_pos := by
      rw [Point.lengthSq_rotate90Counterclockwise]
      exact Point.lengthSq_pos_of_ne _ (sub_ne_zero.mpr (Ne.symm hne)) }

/-- The closed half-space weakly to the right of the directed segment from `p1` to `p2`. -/
def Point.toWeaklyRight (p1 p2 : Point K) (hne : p1 ≠ p2) : ClosedHalfSpace K :=
  { basepoint := p1, normal := Point.rotate90Counterclockwise (p1 - p2),
    normal_pos := by
      rw [Point.lengthSq_rotate90Counterclockwise]
      exact Point.lengthSq_pos_of_ne _ (sub_ne_zero.mpr hne) }

end

/--
Change the half-space by moving the basepoint inward by at least `dist` in the normal direction,
and at most `dist + tolerance` to account for numerical issues.

Specialised to `ℚ` because the implementation relies on
`findRationalWithSquareBetween`, which is a rational-specific construction
(it uses `Nat.sqrt`/`Int.floor` to pin down a rational with a prescribed
squared bound). When upgrading the base field, this operation should be
re-derived from exact square roots.
-/
def ClosedHalfSpace.moveInward (h : ClosedHalfSpace ℚ) (dist tolerance : ℚ)
    (hdist : 0 < dist) (htol : 0 < tolerance) :
    ClosedHalfSpace ℚ :=
  let sqLen := Point.lengthSq h.normal
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
        have : 0 ≤ h.normal.lengthSq := Point.lengthSq_nonneg h.normal
        have : 0 ≤ dist * dist := by nlinarith
        positivity
      ) (by
        -- have : 0 < h.normal.lengthSq := by exact h.normal_pos
        have : 0 < sqLen := by exact h.normal_pos
        -- have : 0 ≤ dist * dist := by nlinarith
        field_simp
        nlinarith)
  let scaledDirection : Point ℚ := ![h.normal 0 * scaleFactor, h.normal 1 * scaleFactor]
  { basepoint := h.basepoint + scaledDirection, normal := h.normal,
    normal_pos := h.normal_pos }

/--
Change the half-space by moving the basepoint *outward* (against the normal direction),
enlarging the half-space, by at least `dist` and at most `dist + tolerance`.

The mirror image of `ClosedHalfSpace.moveInward`; see its docstring for why this is
specialised to `ℚ`.
-/
def ClosedHalfSpace.moveOutward (h : ClosedHalfSpace ℚ) (dist tolerance : ℚ)
    (hdist : 0 < dist) (htol : 0 < tolerance) :
    ClosedHalfSpace ℚ :=
  let sqLen := Point.lengthSq h.normal
  let scaleFactor : ℚ :=
    findRationalWithSquareBetween
      (dist * dist / sqLen) ((dist + tolerance) * (dist + tolerance) / sqLen)
      (by
        have : 0 ≤ h.normal.lengthSq := Point.lengthSq_nonneg h.normal
        have : 0 ≤ dist * dist := by nlinarith
        positivity
      ) (by
        have : 0 < sqLen := by exact h.normal_pos
        field_simp
        nlinarith)
  let scaledDirection : Point ℚ := ![h.normal 0 * scaleFactor, h.normal 1 * scaleFactor]
  { basepoint := h.basepoint - scaledDirection, normal := h.normal,
    normal_pos := h.normal_pos }
