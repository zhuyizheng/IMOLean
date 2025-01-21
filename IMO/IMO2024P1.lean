/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


namespace IMO2024P1

/-- The answer to be determined. -/
def answer : Set ℝ := sorry

theorem result : {α : ℝ | ∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, ⌊i * α⌋} = answer := by
  sorry

end IMO2024P1
