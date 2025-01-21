/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


namespace IMO2024P6

open scoped Cardinal

/-- The condition on functions in the problem. -/
def Aquaesulian (f : ℚ → ℚ) : Prop := ∀ x y, f (x + f y) = f x + y ∨ f (f x + y) = x + f y

/-- The answer to be determined. -/
def answer : ℕ := sorry

theorem result :
    IsLeast {c : ℕ | ∀ f, Aquaesulian f → #(Set.range (fun r ↦ f r + f (-r))) ≤ c} answer := by
  sorry

end IMO2024P6
