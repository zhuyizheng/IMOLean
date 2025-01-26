/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


open scoped Polynomial

namespace IMO2023P3

/-- The answer to be determined. -/
def answer : Set.Ici 2 → Set (ℕ → ℕ) := sorry

theorem result : (fun (k : Set.Ici 2) ↦ {a : ℕ → ℕ |
    (∀ i, 0 < a i) ∧ ∃ P : ℕ[X], P.Monic ∧ P.degree = k ∧
    ∀ n, P.eval (a n) = ∏ i ∈ Finset.Icc (n + 1) (n + ↑k), a i}) = answer := by
  sorry

end IMO2023P3
