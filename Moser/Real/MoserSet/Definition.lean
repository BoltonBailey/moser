import Mathlib
import Moser.Worm.Basic
import Moser.Isometry.Planar

-- /-!
-- # Moser Set Definition

-- This file defines what it means for a set to be a Moser set.
-- -/

-- namespace Moser

-- /-- A set M ⊆ ℝ² is a Moser set if every unit-length worm fits inside M via some isometry -/
-- def IsMoserSet (M : Set (ℝ × ℝ)) : Prop :=
--   ∀ (w : Worm), ∃ (iso : DirectIsometry),
--     w.toPath ⊆ Set.image (fun p => (↑iso.cos * p.1 - ↑iso.sin * p.2 + ↑iso.translation.1,
--                                      ↑iso.sin * p.1 + ↑iso.cos * p.2 + ↑iso.translation.2)) M

-- /-- A computational approximation: M is a Moser set if every worm from a finite list fits -/
-- def IsApproximateMoserSet (M : Set (ℝ × ℝ)) (worms : List ConvexPolygon) (isos : List DirectIsometry) : Prop :=
--   ∀ w ∈ worms, ∃ iso ∈ isos,
--     ∀ v ∈ w.vertices, v ∈ M ∨ sorry  -- TODO: proper containment check

-- end Moser
