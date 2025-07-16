/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


namespace IMO2025P5

/-- Whether all the numbers chosen are valid. -/
def ValidSeq (c : ℝ) {n : ℕ} (x : Fin n → ℝ) : Prop := (∀ i : Fin n, 0 ≤ x i) ∧
  (∀ i : Fin n, Even (i : ℕ) → (∑ j ≤ i, x j) ≤ c * ((i : ℕ) + 1)) ∧
  (∀ i : Fin n, Odd (i : ℕ) → (∑ j ≤ i, (x j) ^ 2) ≤ ((i : ℕ) + 1))

/-- Whether a sequence of numbers chosen is a win for the given player (expressed as the 0-based
numbers of that player's moves, mod 2): the other player makes the first invalid move. -/
def Wins (c : ℝ) (p : ℕ) {n : ℕ} (x : Fin n → ℝ) : Prop := ∃ i : Fin n, (i : ℕ) % 2 ≠ p ∧
  IsLeast {j : Fin n | ¬ ValidSeq c (Fin.take ((j : ℕ) + 1) (by omega) x)} i

/-- A strategy for a given player gives a choice of number in every position, with the convention
that invalid moves lose and the strategy's choices are ignored in cases where it is not that
player's turn, a previous move was invalid or the sequence of previous moves is not possible
under the strategy. -/
abbrev Strategy : Type := ⦃k : ℕ⦄ → (Fin k → ℝ) → ℝ

/-- Playing a strategy, k turns, against a given sequence of opponent moves (possibly not
valid). -/
def Strategy.play (s : Strategy) (p : ℕ) (opponentMoves : ℕ → ℝ) : (k : ℕ) → Fin k → ℝ
| 0 => Fin.elim0
| k + 1 => Fin.snoc (s.play p opponentMoves k)
    (if k % 2 = p then s (s.play p opponentMoves k) else opponentMoves k)

/-- Whether a strategy wins for the given player, against all possible opponent moves. -/
def Strategy.Winning (s : Strategy) (c : ℝ) (p : ℕ) : Prop :=
  ∀ opponentMoves : ℕ → ℝ, ∃ k : ℕ, Wins c p (s.play p opponentMoves k)

/-- The answer to be determined. -/
def answer : Set ℝ × Set ℝ := sorry

theorem result :
    ({c : ℝ | ∃ s : Strategy, s.Winning c 0}, {c : ℝ | ∃ s : Strategy, s.Winning c 1}) =
      answer := by
  sorry

end IMO2025P5
