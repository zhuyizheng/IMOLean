/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


namespace IMO2023P4

/-- The expression in the problem statement (adjusted to 0-based indices). -/
noncomputable def a (x : Fin 2023 → ℝ) (n : Fin 2023) : ℝ := √((∏ i ≤ n, x i) * ∏ i ≤ n, 1 / (x i))

theorem result {x : Fin 2023 → ℝ} (hx0 : ∀ i, 0 < x i) (hxi : Function.Injective x)
    (ha : ∀ n, a x n ∈ Set.range ((↑·) : ℤ → ℝ)) : 3034 ≤ a x ⟨2022, by decide⟩ := by
  sorry

end IMO2023P4
