/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


namespace IMO2021P5

/-- The arrangement of walnuts, as an equiv from holes to walnuts (0-based). -/
abbrev Position : Type := Fin 2021 ≃ Fin 2021

/-- The numbers of the walnuts swapped in move `k` (0-based), given the position. -/
def Position.swapped (p : Position) (k : Fin 2021) : Fin 2021 × Fin 2021 :=
  (p ((p.symm k) - 1), p ((p.symm k) + 1))

/-- A single move, on a pair of position and move number. -/
def move (p : Position × Fin 2021) : Position × Fin 2021 :=
  (p.1.trans (Equiv.swap (p.1.swapped p.2).1 (p.1.swapped p.2).2), p.2 + 1)

/-- The position after `n` moves. -/
def Position.nth (p : Position) (n : Fin 2021) : Position := (move^[n] (p, 0)).1

theorem result (p : Position) :
    ∃ k, (((p.nth k).swapped k).1 < k ∧ k < ((p.nth k).swapped k).2) ∨
      (((p.nth k).swapped k).2 < k ∧ k < ((p.nth k).swapped k).1) := by
  sorry

end IMO2021P5
