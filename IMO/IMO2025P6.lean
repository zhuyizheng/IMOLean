/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


open scoped Finset Function

namespace IMO2025P6

/-- A cell of the grid. -/
abbrev Cell : Type := Fin 2025 × Fin 2025

/-- A rectangular tile on the grid, given by two corners. -/
structure Tile where
  /-- The lower left corner. -/
  lowerLeft : Cell
  /-- The upper right corner. -/
  upperRight : Cell
  below_left : lowerLeft ≤ upperRight

/-- The cells of a rectangle. -/
def Tile.cells (t : Tile) : Set Cell := Set.Icc t.lowerLeft t.upperRight

/-- The answer to be determined. -/
def answer : ℕ := sorry

theorem result :
    IsLeast {k : ℕ | ∃ tiles : Fin k → Tile,
      Pairwise (Disjoint on (fun i ↦ (tiles i).cells)) ∧
      ∃ e : Fin 2025 ≃ Fin 2025, (⋃ i, (tiles i).cells)ᶜ = Set.range fun i ↦ (i, e i)} answer := by
  sorry

end IMO2025P6
