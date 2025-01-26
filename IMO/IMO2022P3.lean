/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


open scoped Finset

namespace IMO2022P3

/-- The condition of the problem on a placement of numbers round a circle. -/
def Condition (k : ℕ) (S : Finset ℕ) (p : Fin #S ≃ S) : Prop :=
  ∀ i, have : NeZero #S := ⟨i.pos.ne'⟩
  ∃ x : ℕ, 0 < x ∧ ((p i : ℕ) * (p (i + 1) : ℕ)) = x ^ 2 + x + k

theorem result {k : ℕ} (hk : 0 < k) (S : Finset ℕ) (hS : ∀ p ∈ S, Odd p ∧ Nat.Prime p)
    (p₁ p₂ : Fin #S ≃ S) : (∃ i, ∀ j, p₂ j = p₁ (j + i)) ∨ ∃ i, ∀ j, p₂ j = p₁ (Fin.rev j + i) := by
  sorry

end IMO2022P3
