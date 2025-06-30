/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


namespace IMO2024P2

/-- The answer to be determined. -/
def answer : Set (ℕ × ℕ) := {(a, b) : (ℕ × ℕ) | a = 1 ∧ b = 1}

theorem result : {(a, b) | 0 < a ∧ 0 < b ∧ ∃ g N : ℕ, 0 < g ∧ 0 < N ∧ ∀ n : ℕ, N ≤ n →
    Nat.gcd (a ^ n + b) (b ^ n + a) = g} = answer := by
  ext a_b_pair
  let (a, b) := a_b_pair
  simp
  constructor
  swap
  · intro h
    rw [answer] at h
    simp at h
    obtain ⟨ha1, hb1⟩ := h
    constructor
    · simp [ha1]
    · constructor
      · simp [hb1]
      · use 2
        simp
        use 1
        simp
        intro n hn
        simp [ha1, hb1]
  · intro h
    obtain ⟨ha1, hb1, g, hg0, C, hC0, hC⟩ := h
    reduce
    clear a_b_pair

    let M := a * b + 1
    have gcd_a_M: Nat.gcd a M = 1 := by simp [M]
    have gcd_b_M: Nat.gcd b M = 1 := by simp [M]

    let phi := Nat.totient M

    have euler_a : a ^ phi ≡ 1 [MOD M] := by apply Nat.ModEq.pow_totient; exact gcd_a_M
    have euler_b : b ^ phi ≡ 1 [MOD M] := by apply Nat.ModEq.pow_totient; exact gcd_b_M

    have M0 : M > 0 := by simp [ha1, hb1, M]
    have phi0 : phi > 0 := by simp [phi, M0]
    have phi1 : phi ≥ 1 := by omega

    let n := phi * (C + 1)
    have euler_a_n : a ^ n ≡ 1 [MOD M] := by
      dsimp [n]
      generalize C + 1 = D
      calc
      a ^ (phi * D) ≡ (a ^ phi) ^ D [MOD M] := by congr 1; ring
      _ ≡ 1 ^ D [MOD M] := by gcongr
      _ ≡ 1 [MOD M] := by congr 1; ring

    have euler_b_n : b ^ n ≡ 1 [MOD M] := by
      dsimp [n]
      generalize C + 1 = D
      calc
      b ^ (phi * D) ≡ (b ^ phi) ^ D [MOD M] := by congr 1; ring
      _ ≡ 1 ^ D [MOD M] := by gcongr
      _ ≡ 1 [MOD M] := by congr 1; ring

    have hn : C + 1 ≤ n := by simp [n, phi1];
    have hn1: 1 ≤ n := by linarith
    let n_minus := n - 1
    have hn2: n = n_minus + 1 := by simp [n_minus, hn1]
    have hn_minus : C ≤ n_minus := by
      suffices hs: C + 1 - 1 ≤ n - 1 by simp at hs; exact hs
      gcongr

    have gcd_n_minus : Nat.gcd (a ^ n_minus + b) (b ^ n_minus + a) = g := by
      specialize hC n_minus
      apply hC
      assumption

    have gcd_n : Nat.gcd (a ^ n + b) (b ^ n + a) = g := by
      specialize hC n
      apply hC
      linarith

    have gcd_n_plus : Nat.gcd (a ^ (n + 1) + b) (b ^ (n + 1) + a) = g := by
      specialize hC (n + 1)
      apply hC
      linarith

    have M_div_g : @Dvd.dvd ℕ Nat.instDvd M g := by
      have a_minus : a * (a ^ n_minus + b) ≡ 0 [MOD M] := by
        calc
        a * (a ^ n_minus + b) ≡ a ^ n + a * b [MOD M] := by congr 1; simp only [hn2]; ring
        _ ≡  1 + a * b [MOD M] := by gcongr
        _ ≡ M [MOD M] := by congr 1; ring
        _ ≡ 0 [MOD M] := by rw [Nat.modEq_iff_dvd]; simp
      have M_div_a_minus_mul : @Dvd.dvd ℕ  Nat.instDvd M (a * (a ^ n_minus + b)) := by
        rw [← Nat.modEq_zero_iff_dvd]
        assumption
      have M_div_a_minus : @Dvd.dvd ℕ  Nat.instDvd M (a ^ n_minus + b) := by
        zify
        zify at M_div_a_minus_mul
        refine Int.dvd_of_dvd_mul_right_of_gcd_one M_div_a_minus_mul ?_
        simp [gcd_a_M, Nat.gcd_comm]
      have b_minus : b * (b ^ n_minus + a) ≡ 0 [MOD M] := by
        calc
        b * (b ^ n_minus + a) ≡ b ^ n + b * a [MOD M] := by simp only [hn2]; ring; rfl
        _ ≡  1 + b * a [MOD M] := by gcongr
        _ ≡ M [MOD M] := by congr 1; ring
        _ ≡ 0 [MOD M] := by rw [Nat.modEq_iff_dvd]; simp
      have M_div_b_minus_mul : @Dvd.dvd ℕ  Nat.instDvd M (b * (b ^ n_minus + a)) := by
        rw [← Nat.modEq_zero_iff_dvd]
        assumption
      have M_div_b_minus : @Dvd.dvd ℕ  Nat.instDvd M (b ^ n_minus + a) := by
        zify
        zify at M_div_b_minus_mul
        refine Int.dvd_of_dvd_mul_right_of_gcd_one M_div_b_minus_mul ?_
        simp [gcd_b_M, Nat.gcd_comm]
      have M_div_g := Nat.dvd_gcd M_div_a_minus M_div_b_minus
      rw [gcd_n_minus] at M_div_g
      exact M_div_g

    have b_cong_minus_1 : 1 + b ≡ 0 [MOD M] := by
      trans (a ^ n + b)
      · gcongr
      · rw [Nat.modEq_zero_iff_dvd]
        rw [← gcd_n, Nat.dvd_gcd_iff] at M_div_g
        tauto

    have a_cong_minus_1 : 1 + a ≡ 0 [MOD M] := by
      trans (b ^ n + a)
      · gcongr
      · rw [Nat.modEq_zero_iff_dvd]
        rw [← gcd_n, Nat.dvd_gcd_iff] at M_div_g
        tauto

    have gcd_M_2 : 0 ≡ 2 [MOD M] := by
      have M_div_a_plus :  @Dvd.dvd ℕ  Nat.instDvd M (a ^ (n + 1) + b) := by
        rw [← gcd_n_plus, Nat.dvd_gcd_iff] at M_div_g
        tauto

      calc
      0 ≡ 0 + 0 [MOD M] := by simp; rfl
      _ ≡ (1 + a) + (1 + b) [MOD M] := by gcongr
      _ ≡ a * 1 + b + 2 [MOD M] := by congr 1; ring
      _ ≡ a * a ^ n + b + 2 [MOD M] := by gcongr
      _ ≡ a ^ (n + 1) + b + 2 [MOD M] := by congr 1; ring
      _ ≡ 0 + 2 [MOD M] := by gcongr; rw [Nat.modEq_zero_iff_dvd]; assumption
      _ ≡ 2 [MOD M] := by simp; rfl

    have M_div_2 :  @Dvd.dvd ℕ  Nat.instDvd M 2 := by rw [← Nat.modEq_zero_iff_dvd]; symm; assumption
    have M_leq_2 : M ≤ 2 := by apply Nat.le_of_dvd; simp; assumption
    by_contra hContra
    have hContra1: a ≠ 1 ∨ b ≠ 1 := by tauto
    have ha: a ≥ 1 := by omega
    have hb: b ≥ 1 := by omega
    have hM: M ≥ 3 := by
      obtain ha1 | hb1 := hContra1
      · simp [M]
        have ha2 : a ≥ 2 := by omega
        have h2: 2 = 2 * 1 := by simp
        rw [h2]
        gcongr
      · simp [M]
        have hb2 : b ≥ 2 := by omega
        have h2: 2 = 1 * 2 := by simp
        rw [h2]
        gcongr
    omega

end IMO2024P2
