/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


open scoped Finset
open Module

namespace IMO2020P6

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

theorem result : ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} (hn : 1 < n) {S : Finset P} (hSn : #S = n)
    (hSdist : (S : Set P).Pairwise fun x y ↦ 1 ≤ dist x y),
    ∃ l : AffineSubspace ℝ P, finrank ℝ l.direction = 1 ∧
      (∃ p₁ p₂, p₁ ∈ S ∧ p₂ ∈ S ∧ l.SOppSide p₁ p₂) ∧
      ∀ p ∈ S, c * (n : ℝ) ^ (-1 / 3 : ℝ) ≤ Metric.infDist p l := by
  sorry

end IMO2020P6
