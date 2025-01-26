/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


open scoped Finset

namespace IMO2022P1

/-- The two types of coins. -/
inductive Coin : Type where
  | A : Coin
  | B : Coin

/-- A row of coins. -/
abbrev Row (n : ℕ) : Type := Fin (2 * n) → Coin

open scoped Classical in
/-- The property of a row having `n` of each kind of coin. -/
def Row.valid {n : ℕ} (c : Row n) : Prop := #{i | c i = Coin.A} = n

open scoped Classical in
/-- The first coin in the chain containing coin `k` (zero-based). -/
noncomputable def Row.chainLeft {n : ℕ} (c : Row n) (k : Fin (2 * n)) : Fin (2 * n) :=
  {j ∈ Finset.Iic k | ∀ i, j ≤ i → i ≤ k → c i = c k}.min' ⟨k, by
    simp only [Finset.mem_filter, Finset.mem_Iic, le_refl, true_and]
    rintro i hki hik
    rw [le_antisymm hki hik]⟩

open scoped Classical in
/-- The last coin in the chain containing coin `k` (zero-based). -/
noncomputable def Row.chainRight {n : ℕ} (c : Row n) (k : Fin (2 * n)) : Fin (2 * n) :=
  {j ∈ Finset.Ici k | ∀ i, k ≤ i → i ≤ j → c i = c k}.max' ⟨k, by
    simp only [Finset.mem_filter, Finset.mem_Ici, le_refl, true_and]
    rintro i hki hik
    rw [le_antisymm hki hik]⟩

/-- Move coins `a` through `b` to the left of the row. -/
def Row.move {n : ℕ} (c : Row n) (a b : Fin (2 * n)) : Row n :=
  fun i ↦ if b < i then c i else c ⟨(((i : ℕ) + (a : ℕ)) % ((b : ℕ) + 1)),
    (Nat.mod_lt _ (by omega)).trans_le (by omega)⟩

/-- The operation moving the chain containing coin `k` (zero-based). -/
noncomputable def Row.operation {n : ℕ} (k : Fin (2 * n)) (c : Row n) : Row n :=
  c.move (c.chainLeft k) (c.chainRight k)

/-- The operation moving the chain containing coin `k` (one-based). -/
noncomputable def Row.operationOneBased {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ 2 * n) (c : Row n) :
    Row n :=
  c.operation ⟨k - 1, by omega⟩

/-- The answer to be determined. -/
def answer : Set (ℕ × ℕ) := sorry

theorem result : {(n, k) | ∃ hk1 : 1 ≤ k, ∃ hkn : k ≤ 2 * n, ∀ c : Row n, c.valid →
    ∃ i, ∀ j₁ j₂ : Fin (2 * n), (j₁ : ℕ) < n → (j₂ : ℕ) < n →
    (Row.operationOneBased hk1 hkn)^[i] c j₁ = (Row.operationOneBased hk1 hkn)^[i] c j₂} =
    answer := by
  sorry

end IMO2022P1
