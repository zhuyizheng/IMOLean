/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


open scoped Finset

namespace IMO2025P4

/-- The answer to be determined. -/
def answer : Set ℕ := sorry

theorem result : {a₁ | ∃ a : ℕ → ℕ, a 0 = a₁ ∧ ∀ i, 0 < a i ∧ 3 ≤ #(Nat.properDivisors (a i)) ∧
    a (i + 1) = (((Nat.properDivisors (a i)).sort (· ≤ ·)).reverse.take 3).sum} = answer := by
  sorry

end IMO2025P4
