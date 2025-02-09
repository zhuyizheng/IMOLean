/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


namespace IMO2021P2

theorem result {n : ℕ} (x : Fin n → ℝ) : ∑ i, ∑ j, √|x i - x j| ≤ ∑ i, ∑ j, √|x i + x j| := by
  sorry

end IMO2021P2
