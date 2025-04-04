/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


open scoped Finset

namespace IMO2020P5

/-- The answer to be determined. -/
def answer : Set ℕ := sorry

theorem result :
    {n : ℕ | 1 < n ∧ ∀ (deck : Fin n → ℕ), (∀ i, 0 < deck i) → (Pairwise fun j k ↦
      ∃ S : Finset (Fin n), S.Nonempty ∧
        (deck j + deck k : ℝ) / 2 = (∏ i ∈ S, (deck i : ℝ)) ^ (1 / (#S : ℝ))) →
      ∀ i j, deck i = deck j} = answer := by
  sorry

end IMO2020P5
