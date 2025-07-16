/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


namespace IMO2025P3

/-- The condition on functions in the problem. -/
def Bonza (f : ℕ+ → ℕ+) : Prop := ∀ a b : ℕ+, (f a : ℤ) ∣ (b ^ (a : ℕ) : ℤ) - (f b ^ (f a : ℕ) : ℤ)

/-- The answer to be determined. -/
def answer : ℝ := sorry

theorem result : IsLeast {c : ℝ | ∀ f : ℕ+ → ℕ+, Bonza f → ∀ n, f n ≤ c * n}
    answer := by
  sorry

end IMO2025P3
