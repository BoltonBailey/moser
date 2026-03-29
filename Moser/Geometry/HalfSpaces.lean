import Moser.Geometry.RationalPoint
import Moser.Geometry.RationalUtility

/-!
# Half Spaces and Lines

This file defines closed and open half-spaces and lines over rational points.
-/

structure ClosedHalfSpace where
  basepoint : RationalPoint
  /--
  The normal, where if the dot product of this with (p - basepoint) is nonnegative,
  then p is in the half-space.
  -/
  normal : RationalPoint
  /-- The normal must be nonzero (positive squared length). -/
  normal_pos : 0 < RationalPoint.lengthSq normal

structure OpenHalfSpace where
  basepoint : RationalPoint
  /--
  The normal, where if the dot product of this with (p - basepoint) is positive,
  then p is in the half-space.
  -/
  normal : RationalPoint
  /-- The normal must be nonzero (positive squared length). -/
  normal_pos : 0 < RationalPoint.lengthSq normal

def OpenHalfSpace.contains (h : OpenHalfSpace) (p : RationalPoint) : Bool :=
  RationalPoint.dotProduct h.normal (p - h.basepoint) > 0

def RationalPoint.toStrictlyLeft (p1 p2 : RationalPoint) (hne : p1 ≠ p2) : OpenHalfSpace :=
  { basepoint := p1, normal := RationalPoint.rotate90Counterclockwise (p2 - p1),
    normal_pos := by
      rw [RationalPoint.lengthSq_rotate90Counterclockwise]
      exact RationalPoint.lengthSq_pos_of_ne _ (sub_ne_zero.mpr (Ne.symm hne)) }

structure Line where
  point : RationalPoint
  direction : RationalPoint
  /-- direction must be nonzero -/
  direction_pos : 0 < RationalPoint.lengthSq direction

def Line.parallel (l1 l2 : Line) : Bool :=
  RationalPoint.crossProduct l1.direction l2.direction = 0

/--
Note AI generated
-/
def Line.intersection (l1 l2 : Line) : Option RationalPoint :=
  if l1.parallel l2 then none
  else
    let d := RationalPoint.crossProduct l1.direction l2.direction
    let t := RationalPoint.crossProduct (l2.point - l1.point) l2.direction / d
    some (l1.point + t • l1.direction)

def ClosedHalfSpace.boundaryLine (h : ClosedHalfSpace) : Line :=
  { point := h.basepoint, direction := RationalPoint.rotate90Counterclockwise h.normal,
    direction_pos := by
      rw [RationalPoint.lengthSq_rotate90Counterclockwise]
      exact h.normal_pos }

/--
Given two closed half-spaces, compute the intersection point of their boundary lines if it exists.
Returns none if the lines are parallel (no intersection or infinite intersection).
-/
def ClosedHalfSpace.lineIntersection (h1 h2 : ClosedHalfSpace) : Option RationalPoint :=
  Line.intersection (h1.boundaryLine) (h2.boundaryLine)

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
Change the half-space by moving the basepoint inward by at least `dist` in the normal direction,
and at most `dist + tolerance` to account for numerical issues.
-/
def ClosedHalfSpace.moveInward (h : ClosedHalfSpace) (dist tolerance : ℚ)
    (hdist : 0 < dist) (htol : 0 < tolerance) :
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
