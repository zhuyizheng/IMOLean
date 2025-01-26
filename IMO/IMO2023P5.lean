/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


open scoped Finset

namespace IMO2023P5

/-- A circle of a Japanese triangle. -/
abbrev Circle (n : ℕ) : Type := Σ i : Fin n, Fin ((i : ℕ) + 1)

/-- A Japanese triangle. -/
structure JapaneseTriangle (n : ℕ) where
  /-- The red circle in each row. -/
  redCirclePos : (i : Fin n) → Fin ((i : ℕ) + 1)

/-- The set of red circles in a Japanese triangle. -/
def JapaneseTriangle.redCircles {n : ℕ} (jt : JapaneseTriangle n) : Finset (Circle n) :=
  Finset.image (fun i ↦ ⟨i, jt.redCirclePos i⟩) Finset.univ

/-- A ninja path in a Japanese triangle. -/
structure NinjaPath (n : ℕ) where
  /-- The circles in the path. -/
  circlePos : (i : Fin n) → Fin ((i : ℕ) + 1)
  adjacent : ∀ i : Fin n, ∀ hi : (i : ℕ) + 1 < n,
    (circlePos ⟨(i : ℕ) + 1, hi⟩ : ℕ) = (circlePos i : ℕ) ∨
      (circlePos ⟨(i : ℕ) + 1, hi⟩ : ℕ) = (circlePos i : ℕ) + 1

/-- The set of circles in a ninja path. -/
def NinjaPath.circles {n : ℕ} (np : NinjaPath n) : Finset (Circle n) :=
  Finset.image (fun i ↦ ⟨i, np.circlePos i⟩) Finset.univ

/-- The answer to be determined. -/
def answer : ℕ+ → ℕ := sorry

theorem result (n : ℕ+) : IsGreatest {k : ℕ | ∀ jt : JapaneseTriangle n, ∃ np : NinjaPath n,
    k ≤ #(np.circles ∩ jt.redCircles)} (answer n) := by
  sorry

end IMO2023P5
