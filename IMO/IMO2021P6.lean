/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


open scoped Finset

namespace IMO2021P6

theorem result {m : ℕ} (hm : 2 ≤ m) (A : Finset ℤ) (B : Fin m → Finset ℤ) (hBA : ∀ i, B i ⊆ A)
    (hB : ∀ k, ∑ i ∈ B k, i = m ^ ((k : ℕ) + 1)) : (m : ℚ) / 2 ≤ #A := by
  sorry

end IMO2021P6
