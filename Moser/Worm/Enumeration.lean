import Mathlib
import Moser.Worm.Basic
import Moser.DirectIsometry.Discretization

/-!
# Worm Enumeration

This file enumerates candidate worms by their convex hulls (equiangular polygons).
-/

namespace Moser

open Rat

-- /--
-- Given a ConvexPolygon,
-- enumerate all possible worms that could have this polygon as their convex hull.
-- That is, all permutations of the vertices.
-- Returns empty list if polygon has fewer than 2 vertices.
-- -/
-- def enumerateWormsFromPolygon (poly : ConvexPolygon) : List Worm :=
--   let verts := poly.vertices
--   if h : verts.length ≥ 2 then
--     let perms := verts.permutations
--     perms.pmap
--       (fun vts (hmem : vts ∈ perms) =>
--         { vertices := vts,
--           nonempty := by
--             have := (List.mem_permutations.mp hmem).length_eq
--             omega })
--       (fun _ hx => hx)
--   else []

-- /--
-- Given a ConvexPolygon and a approximation factor
-- returns optionally a rescaled ConvexPolygon such that at least one worm
-- with that convex hull has unit length.

-- find the length of its worms approximately.
-- And then rescale the polygon for at least one worm to have unit length.
-- -/
-- def ConvexPolygon.rescaleToUnitWorm (poly : ConvexPolygon) (epsilon : ℚ) :
--     Option ConvexPolygon :=
--   let worms := enumerateWormsFromPolygon poly
--   -- Upper bound on lengths of worms
--   let wormLengths := worms.map (fun w => w.lengthApprox epsilon + epsilon)
--   let smallestLength := wormLengths.foldl min (wormLengths.head!)
--   if smallestLength ≤ 0 then none
--   else
--     let scaleFactor := 1 / smallestLength
--     let scaledPoly :=
--       { vertices := poly.vertices.map (fun p => (p.1 * scaleFactor, p.2 * scaleFactor)) }
--     some scaledPoly


-- def generateRandomPolygon (seed : ℕ) (numVertices : ℕ) : ConvexPolygon :=
--   let randomPoints : List Point :=
--     List.range numVertices |>.map (fun i =>
--       let x : ℚ := ((seed + i * 373) % 1000 : ℕ) / 1000
--       let y : ℚ := ((seed + i * 737) % 1000 : ℕ) / 1000
--       (x, y))
--   { vertices := randomPoints }

-- /--
-- Enumerate a list of at most n polygons.
-- -/
-- def enumeratePolygons (size : ℕ) : List ConvexPolygon :=
--   -- Generate random polygons using different seeds
--   List.range size |>.map (fun seed => generateRandomPolygon seed (seed % 5 + 3))

-- /-- Default worm enumeration with reasonable parameters -/
-- def defaultWormEnumeration (n : ℕ) : List ConvexPolygon :=
--   let epsilon : ℚ := 1 / (n + 1)
--   let polygons := enumeratePolygons n
--   polygons.filterMap (fun poly => ConvexPolygon.rescaleToUnitWorm poly epsilon)

-- #eval enumeratePolygons 2

end Moser
