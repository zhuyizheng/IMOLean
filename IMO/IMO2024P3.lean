/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


open scoped Finset

namespace IMO2024P3

/-- The property of a sequence being eventually periodic. -/
def EventuallyPeriodic (b : ℕ → ℕ) : Prop := ∃ p M, 0 < p ∧ ∀ m, M ≤ m → b (m + p) = b m

/-- Following usual Lean conventions, this is expressed with indices starting from 0, rather than
from 1 as in the informal statment (but `N` remains as the index of the last term for which `a n`
is not defined in terms of previous terms). -/
theorem result {a : ℕ → ℕ} {N : ℕ} (h0 : ∀ i, 0 < a i)
    (ha : ∀ n, N < n → a n = #{i ∈ (Finset.range n) | a i = a (n - 1)}) :
    EventuallyPeriodic (fun i ↦ a (2 * i)) ∨ EventuallyPeriodic (fun i ↦ a (2 * i + 1)) := by
  sorry

end IMO2024P3
