import Mathlib
import Moser.Geometry.PolygonArea

/-!
# Constants for Moser's Worm Problem

This file defines the key constants used in the computational approach:
- `areaThreshold`: Maximum area for candidate Moser sets
- `distanceCutoff`: Maximum distance from origin for polygon vertices
-/

namespace Moser

/--
Area threshold for candidate Moser sets (0.232240)
This is the number we are trying to beat with our working set polygons.
-/
def areaThreshold : ℚ := .divInt 232240 1000000

/--
The "initial worm" iis a worm that we
assume any set in our working set must contain an unshifted copy of.

This makes it convenient to exclude points from working set polygons
on the basis of containing a point
such that the hull of such a point with the initial worm would have area > threshold.

We could consider redefining this when optimizing
-/
def InitialWorm : ConvexPolygon where
  vertex_count := 3
  vertices := fun i =>
    match i with
    | ⟨0, _⟩ => ![0, 0]
    | ⟨1, _⟩ => ![.divInt 1 2, 0]
    | ⟨2, _⟩ => ![0, .divInt 1 2]
    | _ => ![0, 0] -- This case won't happen due to the finiteness of vertex_count
  nodup := by native_decide
  vertices_extremeRationalPoints := by native_decide

-- Example computation: area of InitialWorm
example : InitialWorm.area = 1 / 8 := by
  native_decide


def offset := areaThreshold * 4
#eval offset

/--
A convex polygon representing an upper bound
on the range of locations a point in the working set can contain.

This is the square with vertices at (± offset, ± offset).
Any point outside this square cannot be contained in a convex polygon
that also contains the InitialWorm without exceeding the area threshold.
(Because otherwise there would be a triangle that was too large.)

TODO We could potentially optimize this to the smallest polygon for which the above is true.
Which would in turn let us improve the distance cutoff
and thus reduce the fineness needed in angle discretization.
-/
def LocationRange : ConvexPolygon where
  vertex_count := 4
  vertices := fun i =>

    match i with
    | ⟨0, _⟩ => ![-offset, -offset]
    | ⟨1, _⟩ => ![offset, -offset]
    | ⟨2, _⟩ => ![offset, offset]
    | ⟨3, _⟩ => ![-offset, offset]
    | _ => ![0, 0] -- This case won't happen due to the finiteness of vertex_count
  nodup := by native_decide
  vertices_extremeRationalPoints := by native_decide

def upperBoundSqrtTwo : ℚ  := .divInt 1414213562373095 1000000000000000

/--
An upper bound on the distance from the origin for points in the LocationRange
-/
def distanceCutoff : ℚ := offset * upperBoundSqrtTwo


end Moser
