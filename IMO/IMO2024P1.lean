/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib

open Real Int Nat Finset

namespace IMO2024P1

/-- The answer to be determined. -/
def answer : Set ℝ := { x | ∃ k : ℤ, x = 2 * k }


lemma SumReduceZero (f : ℕ → ℤ) (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, f i = (∑ i ∈ Finset.Icc 0 n, f i) - f 0 := by
  have h1: Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by ext; simp; omega
  have h2: 0 ∉ Finset.Icc 1 n := by simp
  simp [h1, h2]

lemma SumSucc (f : ℕ → ℤ) (n : ℕ) : n > 1 →  ∑ i ∈ Finset.Icc 1 n, f i = (∑ i ∈ Finset.Icc 1 (n - 1), f i) + f n := by
  intro hn
  have h1: Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by ext; simp; omega
  have h2: n ∉ Finset.Icc 1 (n - 1) := by simp; omega
  simp [h1, h2]
  ring



lemma DvdOneIsOne {n : ℕ} : (n:ℤ) ∣ (1:ℤ) → n = 1 := by
  intro h
  have hn1 := Int.one_dvd n
  have h1 : 0 ≤ (1:ℤ) := by simp
  have hn2: 0 ≤ (n:ℤ) := by simp
  have h1equal := Int.dvd_antisymm hn2 h1
  convert h1equal h hn1
  norm_cast



theorem result : {α : ℝ | ∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, ⌊i * α⌋} = answer := by
  let S (n : ℕ) (α : ℝ) : ℤ :=  ∑ i ∈ Finset.Icc 1 n, ⌊↑i * α⌋
  have rewriteS : {α : ℝ | ∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ i ∈ Finset.Icc 1 n, ⌊i * α⌋} = {α : ℝ | ∀ n : ℕ,  0 < n →  (n : ℤ) ∣ S n α} := by
    dsimp [S]
  rw [rewriteS]

  rw [answer]

  have hSumInt : ∀ (z : ℤ) (n : ℕ), 0 < n → S n z = ∑ i ∈ Finset.Icc 1 n, i * z := by
    intro z n hn
    dsimp [S]
    apply Finset.sum_congr rfl
    intro i hi
    convert Int.floor_intCast (i * z)
    push_cast
    rfl
    infer_instance

  have reduced : ∀ (k : ℤ)  (n : ℕ), 0 < n → ↑n ∣ S n (2 * k : ℤ) := by
    intro k n hn
    have hSumReduce: ∑ i ∈ Finset.Icc 1 n, ⌊i * ((2 * k : ℤ) : ℝ)⌋ = n * (n + 1) * k := by
      calc
      ∑ i ∈ Finset.Icc 1 n, ⌊↑i * ((2 * k : ℤ) : ℝ)⌋ = ∑ i ∈ Finset.Icc 1 n, ↑i * (2 * k) := by
        apply hSumInt (2 * k) n hn
      _ = (∑ i ∈ Finset.Icc 0 n, ↑i * (2 * k)) - ↑0 * (2 * k) := by apply SumReduceZero
      _ = ∑ i ∈ Finset.Icc 0 n, ↑i * (2 * k) := by simp
      _ = (∑ i ∈ Finset.Icc 0 n, ↑i) * (2 * k) := by rw [Finset.sum_mul]
      _ = (∑ i ∈ Finset.range (n + 1), ↑i) * (2 * k) := by
        have hRange: Finset.Icc 0 n = Finset.range (n + 1) := by ext; simp; omega
        rw [hRange]
      _ = (∑ i ∈ Finset.range (n + 1), ↑i) * 2 * k := by ring
      _ = (∑ i ∈ Finset.range (n + 1), i) * 2 * k := by simp
      _ =  n * (n + 1) * k:= by
        congr 1
        norm_cast
        rw [Finset.sum_range_id_mul_two]
        simp
        ring
    dsimp [S]
    rw [hSumReduce]
    use (n + 1) * k
    ring

  have Sadditive : ∀ (z : ℤ) (α : ℝ) (n : ℕ), 0 < n → S n (z + α) = S n z + S n α := by
    intro z α n hn
    calc
    S n (z + α) = ∑ i ∈ Finset.Icc 1 n, ⌊↑i * (z + α)⌋ := by dsimp [S]
    _ =  ∑ i ∈ Finset.Icc 1 n, (i * z + ⌊i * α⌋) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
      rw [add_comm _ (i * α), add_comm _ ⌊(i * α)⌋]
      convert Int.floor_add_intCast (i * α) (i * z)
      simp
    _ = ∑ i ∈ Finset.Icc 1 n, i * z + ∑ i ∈ Finset.Icc 1 n, ⌊i * α⌋ := by apply Finset.sum_add_distrib
    _ = S n z +  ∑ i ∈ Finset.Icc 1 n, ⌊i * α⌋ := by simp only [hSumInt z n hn]
    _ = S n z + S n α := by dsimp [S]

  ext α
  simp
  constructor
  swap

  · show  (∃ (k : ℤ), α = 2 * ↑k) → ∀ (n : ℕ), 0 < n → ↑n ∣ S n α
    intro hα n hn
    obtain ⟨k, hk⟩ := hα
    convert reduced k n hn
    norm_cast at hk

  · show (∀ (n : ℕ), 0 < n → ↑n ∣ S n α) → ∃ (k : ℤ), α = 2 * ↑k
    intro hα
    let z := ⌊α⌋
    let β := α - ⌊α⌋
    have hβ0 : 0 ≤ β := by simp [β]
    have hβ1 : β < 1 := by
      have h1: α < ⌊α⌋ + 1 := by apply Int.lt_floor_add_one
      have h2: α - ⌊α⌋ < 1 := by linarith
      exact h2

    by_contra hContra

    cases Int.even_or_odd z with
    | inl hEven =>
      obtain ⟨k, hk⟩ := hEven

      have hβ : ∀ (n : ℕ), 0 < n → ↑n ∣ S n β := by
        intro n hn
        have hAdd: S n α = S n (2 * k : ℤ) + S n β := by
          have hαSplit:  α = (2 * k : ℤ) + β := by
            simp only [β, hk, z]
            ring
          rw [← Sadditive (2 * k) β n, hαSplit]
          exact hn

        specialize hα n hn
        rw [hAdd] at hα
        specialize reduced k n hn
        rw [← Int.dvd_add_right reduced]
        exact hα
      clear hα

      have hβ0Strict : 0 < β := by
        have : 0 ≠ β := by
          by_contra hContraTemp
          have hαk: α = 2 * k := by
            calc
            α = β + z := by simp [β, z]
            _ = z := by simp [hContraTemp]
            _ = k + k := by simp [hk]
            _ = 2 * k := by ring
          have hαk1:  ∃ (k : ℤ), α = 2 * k := by use k
          contradiction
        positivity
      clear hβ0

      have hArchiTemp : ∃ m : ℕ, 1 ≤ m • β := by
        exact Archimedean.arch 1 hβ0Strict
      have hArchi : ∃ m : ℕ, 1 ≤ m * β := by
        obtain ⟨m, hm⟩ := hArchiTemp
        rw [nsmul_eq_mul m β] at hm
        use m
      clear hArchiTemp
      let m := Nat.find hArchi
      have hm1Temp: 1 ≤ m * β := by exact Nat.find_spec hArchi
      have hm0Temp (j: ℕ): j < m →  ¬ (1 ≤ j * β) := by exact Nat.find_min hArchi
      have hm2Temp0: m ≠ 0 := by
        by_contra hm
        rw [hm] at hm1Temp
        simp at hm1Temp
        linarith
      have hm2TempGreater0 : 0 < m := by omega
      have hm2Temp1: m ≠ 1 := by
        by_contra hm
        rw [hm] at hm1Temp
        simp at hm1Temp
        linarith
      have hm2: m ≥ 2 := by omega
      have hm1: ⌊m * β⌋ = 1 := by
        rw [Int.floor_eq_iff]
        simp
        constructor
        · exact hm1Temp
        · calc
          m * β = (m - 1) * β + β := by ring
          _ < 1 + β := by
            gcongr
            specialize hm0Temp (m - 1)
            have : 0 < m := by omega
            simp [hm2, this] at hm0Temp
            simp
            exact hm0Temp
          _ < 1 + 1 := by simp [hβ1]

      have hm0 (j: ℕ): j < m → ⌊j * β⌋ = 0 := by
        rw [Int.floor_eq_iff]
        simp
        intro hj
        constructor
        · simp [hβ0Strict]
        · specialize hm0Temp j
          apply hm0Temp at hj
          linarith

      clear hm1Temp
      clear hm0Temp

      have hCalc : S m β = 1 := by
        calc
        S m β = ∑ i ∈ Finset.Icc 1 m, ⌊↑i * β⌋ := by dsimp [S]
        _ = ∑ i ∈ Finset.Icc 1 (m - 1), ⌊↑i * β⌋ + ⌊m * β⌋ := by
          have : m > 1 := by linarith
          simp only [SumSucc (λ i ↦ ⌊↑i * β⌋) m, this]
        _ = ∑ i ∈ Finset.Icc 1 (m - 1), ⌊↑i * β⌋ + 1 := by simp [hm1]
        _ = ∑ i ∈ Finset.Icc 1 (m - 1), 0 + 1 := by
          congr 1
          apply Finset.sum_congr rfl;
          intro j hj
          simp at hj
          apply hm0
          omega
        _ = 1 := by simp

      specialize hβ m hm2TempGreater0
      simp only [hCalc] at hβ
      have hmEq1 : m = 1 := DvdOneIsOne hβ
      apply hm2Temp1 at hmEq1
      exact hmEq1


    | inr hOdd =>
      obtain ⟨k, hk⟩ := hOdd

      let β' := β - 1
      have hβ'1 : -1 ≤ β' := by simp [hβ0, β']
      have hβ'0 : β' < 0 := by simp [hβ1, β']
      clear hβ0
      clear hβ1

      have hβ' : ∀ (n : ℕ), 0 < n → ↑n ∣ S n β' := by
        intro n hn
        have hAdd: S n α = S n (2 * (k + 1) : ℤ) + S n β' := by
          have hαSplit: α = (2 * (k + 1) : ℤ) + β' := by
            simp only [β, β', hk, z]
            push_cast
            ring
          rw [← Sadditive (2 * (k + 1)) β' n, hαSplit]
          exact hn

        specialize hα n hn
        rw [hAdd] at hα
        specialize reduced (k + 1) n hn
        rw [← Int.dvd_add_right reduced]
        exact hα
      clear hα

      have hβ'Neg : 0 < -β' := by simp [hβ'0]
      have hArchiTemp : ∃ m : ℕ, 2 ≤ m • (-β') := by
        exact Archimedean.arch 2 hβ'Neg
      have hArchi2 : ∃ m : ℕ, 2 ≤ m * (-β') := by
        obtain ⟨m, hm⟩ := hArchiTemp
        rw [nsmul_eq_mul m (-β')] at hm
        use m
      clear hArchiTemp
      have hArchi : ∃ m : ℕ, 1 < m * (-β') := by
        obtain ⟨m, hm⟩ := hArchi2
        use m
        linarith
      let m := Nat.find hArchi
      have hm1TempNeg: 1 < m * (-β') := by exact Nat.find_spec hArchi
      have hm0TempNeg (j: ℕ): j < m →  ¬ (1 < j * (-β')) := by exact Nat.find_min hArchi
      have hm2Temp0: m ≠ 0 := by
        by_contra hm
        rw [hm] at hm1TempNeg
        simp at hm1TempNeg
        linarith
      have hm2TempGreater0 : 0 < m := by omega
      have hm2Temp1: m ≠ 1 := by
        by_contra hm
        rw [hm] at hm1TempNeg
        simp at hm1TempNeg
        linarith
      have hNeg (m : ℕ): m * (-β') = - (m * β') := by simp
      have hm1Temp : m * β' < -1 := by
        rw [hNeg] at hm1TempNeg
        linarith
      clear hm1TempNeg
      have hm0Temp (j: ℕ): j < m →  -1 ≤ j * β'  := by
        intro hj
        specialize hm0TempNeg j hj
        rw [hNeg] at hm0TempNeg
        linarith
      clear hm0TempNeg

      have hm2: m ≥ 2 := by omega
      have hm1: ⌊m * β'⌋ = -2 := by
        rw [Int.floor_eq_iff]
        simp
        constructor
        swap
        · linarith
        · calc
          m * β' = (m - 1) * β' + β' := by ring
          _ ≥ -1 + β' := by
            show -1 + β' ≤ (↑m - 1) * β' + β'
            gcongr
            specialize hm0Temp (m - 1)
            have : 0 < m := by omega
            simp [hm2, this] at hm0Temp
            simp
            exact hm0Temp
          _ ≥ -1 + (-1) := by simp [hβ'1]
          _ = -2 := by norm_cast

      have hm0 (j: ℕ): 0 < j → j < m → ⌊j * β'⌋ = -1 := by
        rw [Int.floor_eq_iff]
        simp
        intro hj0 hj
        constructor
        swap
        · apply mul_neg_of_pos_of_neg
          simp [hj0]
          exact hβ'0
        · specialize hm0Temp j
          apply hm0Temp at hj
          linarith

      clear hm1Temp
      clear hm0Temp

      have hCalc : S m β' = m * (-1) - 1 := by
        calc
        S m β' = ∑ i ∈ Finset.Icc 1 m, ⌊↑i * β'⌋ := by dsimp [S]
        _ = ∑ i ∈ Finset.Icc 1 (m - 1), ⌊↑i * β'⌋ + ⌊m * β'⌋ := by
          have : m > 1 := by linarith
          simp only [SumSucc (λ i ↦ ⌊↑i * β'⌋) m, this]
        _ = ∑ i ∈ Finset.Icc 1 (m - 1), ⌊↑i * β'⌋ + (-2) := by simp [hm1]
        _ = ∑ i ∈ Finset.Icc 1 (m - 1), (-1) + (-2) := by
          congr 1
          apply Finset.sum_congr rfl;
          intro j hj
          simp at hj
          apply hm0
          omega
          omega
        _ = (m - 1) * (-1) + (-2) := by simp [Finset.sum_const, Finset.card_range, hm2TempGreater0];
        _ = m * (-1) - 1 := by ring

      specialize hβ' m hm2TempGreater0
      simp only [hCalc] at hβ'
      have hDiv := Int.dvd_refl m
      rw [← Int.dvd_add_right hDiv] at hβ'
      ring_nf at hβ'
      rw [Int.dvd_neg] at hβ'
      have hmEq1 : m = 1 := DvdOneIsOne hβ'
      apply hm2Temp1 at hmEq1
      exact hmEq1

end IMO2024P1
