/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


open scoped Nat

namespace IMO2022P5

/-- The answer to be determined. -/
def answer : Set (ℕ × ℕ × ℕ) := sorry

theorem result : {(a, b, p) | 0 < a ∧ 0 < b ∧ 0 < p ∧ Nat.Prime p ∧ a ^ p = b ! + p} = answer := by
  sorry

end IMO2022P5
