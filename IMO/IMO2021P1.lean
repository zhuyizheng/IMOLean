/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


namespace IMO2021P1

theorem result {n : ℕ} (hn : 100 ≤ n) {S : Finset ℕ} (hS : S ⊆ Finset.Icc n (2 * n)) :
    (∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ IsSquare (a + b)) ∨
    (∃ a ∈ Finset.Icc n (2 * n) \ S, ∃ b ∈ Finset.Icc n (2 * n) \ S,
      a ≠ b ∧ IsSquare (a + b)) := by
  sorry

end IMO2021P1
