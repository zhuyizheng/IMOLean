/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


namespace IMO2024P6

open scoped Cardinal

/-- The condition on functions in the problem. -/
def Aquaesulian (f : ℚ → ℚ) : Prop := ∀ x y, f (x + f y) = f x + y ∨ f (f x + y) = x + f y

/-- The answer to be determined. -/
def answer : ℕ := 2


lemma size_at_least_two {α : Type*} {S : Set α} {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    2 ≤ #S := by
  let T : Set α := {x, y}
  have hT : T ⊆ S := by
    intro z hz
    simp [T] at hz
    cases hz with
    | inl hz =>
      simp [hz, hx]
    | inr hz =>
      simp [hz, hy]

  have : #T = 2 := by
    rw [Cardinal.mk_insert, Cardinal.mk_singleton]
    · norm_cast
    · simp [hxy]

  rw [← this]
  exact Cardinal.mk_le_mk_of_subset hT


universe u
lemma three_elements {S : Type u} (h : ¬ (#S ≤ 2)) :
    ∃ (x y z : S), x ≠ y ∧ y ≠ z ∧ x ≠ z := by
  have h3 : 3 ≤ #S := by
    contrapose! h
    apply Order.le_of_lt_succ
    norm_cast

  let T := ULift.{u} (Fin 3)  -- T : Type u
  have hT : #T = 3 := by norm_cast
  have hTS :  #T ≤ #S := by rw [hT]; assumption

  rcases (Cardinal.le_def T S).mp hTS with ⟨f, hf⟩

  let x := f (ULift.up 0)
  let y := f (ULift.up 1)
  let z := f (ULift.up 2)
  have hx: x = f { down := 0} := by dsimp [x]
  have hy: y = f { down := 1} := by dsimp [y]
  have hz: z = f { down := 2} := by dsimp [z]

  have hxy : x ≠ y := by
    intro heq
    rw [hx, hy] at heq
    have := congrArg (ULift.down) (hf heq)
    rw [ULift.down_up, ULift.down_up] at this
    omega

  have hyz : y ≠ z := by
    intro heq
    rw [hy, hz] at heq
    have := congrArg (ULift.down) (hf heq)
    rw [ULift.down_up, ULift.down_up] at this
    omega

  have hxz : x ≠ z := by
    intro heq
    rw [hx, hz] at heq
    have := congrArg (ULift.down) (hf heq)
    rw [ULift.down_up, ULift.down_up] at this
    omega

  exact ⟨x, y, z, hxy, hyz, hxz⟩



theorem result :
    IsLeast {c : ℕ | ∀ f, Aquaesulian f → #(Set.range (fun r ↦ f r + f (-r))) ≤ c} answer := by
  rw [answer]
  constructor
  swap
  · dsimp [lowerBounds]
    intro a ha
    let f (x : ℚ) : ℚ := ⌊2 * x⌋ - x
    specialize ha f
    have Aq_f : Aquaesulian f := by
      rw [Aquaesulian]
      intro x y
      have f_int_additive (k : ℤ) (x : ℚ): f (x + k) = f x + k := by
        dsimp [f]
        ring
        norm_cast
        have flooradd (k0 : ℤ): ⌊x * 2 + k0⌋ = ⌊x * 2⌋ + k0 := by simp
        rw [flooradd (k * 2)]
        push_cast
        ring
      let r := x - ⌊x⌋
      let s := y - ⌊y⌋
      have xadd : x = r + ⌊x⌋ := by ring
      have yadd : y = s + ⌊y⌋ := by ring
      let xplusy_floor : ℤ := ⌊x⌋ + ⌊y⌋
      have f_add_1 : f (x + f y) = f (r + f s) + ⌊x⌋ + ⌊y⌋ := by
        nth_rw 1 [xadd, yadd]
        rw [f_int_additive ⌊y⌋ s]
        calc
        f (r + ⌊x⌋ + (f s + ⌊y⌋)) = f (r + f s + xplusy_floor):= by congr 1; simp [xplusy_floor]; ring
        _ = f (r + f s) + ⌊x⌋ + ⌊y⌋ := by simp [f_int_additive]; simp [xplusy_floor]; ring
      have f_add_2 : f x + y = f r + s + ⌊x⌋ + ⌊y⌋ := by
        nth_rw 1 [xadd, yadd]
        rw [f_int_additive ⌊x⌋ r]
        ring
      have f_add_3 : f (f x + y) = f (f r + s) + ⌊x⌋ + ⌊y⌋ := by
        nth_rw 1 [xadd, yadd]
        rw [f_int_additive ⌊x⌋ r]
        calc
        f (f r + ⌊x⌋ + (s + ⌊y⌋)) = f (f r + s + xplusy_floor):= by congr 1; simp [xplusy_floor]; ring
        _ = f (f r + s) + ⌊x⌋ + ⌊y⌋ := by simp [f_int_additive]; simp [xplusy_floor]; ring
      have f_add_4 : x + f y = r + f s + ⌊x⌋ + ⌊y⌋ := by
        nth_rw 1 [xadd, yadd]
        rw [f_int_additive ⌊y⌋ s]
        ring

      rw [f_add_1, f_add_3, f_add_2, f_add_4]
      simp
      have r_range : 0 ≤ r ∧ r < 1 := by
        have hx1 : ⌊x⌋ ≤ x := by bound
        have hx2 : x < ⌊x⌋ + 1  := by bound
        constructor
        · bound
        · nth_rw 1 [xadd] at hx2
          rw [add_comm] at hx2
          simp at hx2
          assumption
      have s_range : 0 ≤ s ∧ s < 1 := by
        have hx1 : ⌊y⌋ ≤ y := by bound
        have hx2 : y < ⌊y⌋ + 1  := by bound
        constructor
        · bound
        · nth_rw 1 [yadd] at hx2
          rw [add_comm] at hx2
          simp at hx2
          assumption
      have f_val_1 (t : ℚ) : 0 ≤ t → t < 1/2 → f t = -t := by
        dsimp [f]
        intro ht1 ht2
        simp
        constructor
        assumption
        linarith
      have f_val_2 (t : ℚ) : 1/2 ≤ t → t < 1 → f t = 1 - t := by
        dsimp [f]
        intro ht1 ht2
        simp
        apply Int.floor_eq_iff.mpr
        constructor
        · ring
          nlinarith
        · ring
          nlinarith
      have f_val_3 (t : ℚ) : 1 ≤ t → t < 3/2 → f t = 2 - t := by
        dsimp [f]
        intro ht1 ht2
        simp
        suffices ht : ⌊2 * t⌋ = 2 by rw [ht]; decide
        apply Int.floor_eq_iff.mpr
        constructor
        · ring
          nlinarith
        · ring
          nlinarith
      by_cases r_split : r < 1/2
      · have hfr : f r = -r := by apply f_val_1; tauto; tauto
        by_cases s_split : s < 1/2
        · have hfs : f s = -s := by apply f_val_1; tauto; tauto
          rw [hfr, hfs]
          by_cases r_s_comp : r < s
          · right
            let t := -r + s
            suffices ht : f t = -t  by dsimp [t] at ht; rw [ht]; ring
            apply f_val_1
            · dsimp [t]
              linarith
            · dsimp [t]
              linarith
          · left
            let t := r + (-s)
            suffices ht : f t = -t  by dsimp [t] at ht; rw [ht]; ring
            apply f_val_1
            · dsimp [t]
              linarith
            · dsimp [t]
              linarith
        · have hfs : f s = 1 - s := by apply f_val_2; linarith; tauto
          rw [hfr, hfs]
          by_cases r_s_comp : r > s - 1/2
          · left
            let t := r + (1 - s)
            suffices ht : f t = 1 - t  by dsimp [t] at ht; rw [ht]; ring
            apply f_val_2
            · dsimp [t]
              linarith
            · dsimp [t]
              linarith
          · right
            let t := -r + s
            suffices ht : f t = 1 - t  by dsimp [t] at ht; rw [ht]; ring
            apply f_val_2
            · dsimp [t]
              linarith
            · dsimp [t]
              linarith
      · have hfr : f r = 1 - r := by apply f_val_2; linarith; tauto
        by_cases s_split : s < 1/2
        · have hfs : f s = -s := by apply f_val_1; tauto; tauto
          rw [hfr, hfs]
          by_cases r_s_comp : s > r - 1/2
          · right
            let t := 1 - r + s
            suffices ht : f t = 1 - t  by dsimp [t] at ht; rw [ht]; ring
            apply f_val_2
            · dsimp [t]
              linarith
            · dsimp [t]
              linarith
          · left
            let t := r + (-s)
            suffices ht : f t = 1 - t  by dsimp [t] at ht; rw [ht]; ring
            apply f_val_2
            · dsimp [t]
              linarith
            · dsimp [t]
              linarith
        · have hfs : f s = 1 - s := by apply f_val_2; linarith; tauto
          rw [hfr, hfs]
          by_cases r_s_comp : r > s
          · left
            let t := r + (1 - s)
            suffices ht : f t = 2 - t  by dsimp [t] at ht; rw [ht]; ring
            apply f_val_3
            · dsimp [t]
              linarith
            · dsimp [t]
              linarith
          · right
            let t := 1 - r + s
            suffices ht : f t = 2 - t  by dsimp [t] at ht; rw [ht]; ring
            apply f_val_3
            · dsimp [t]
              linarith
            · dsimp [t]
              linarith
    apply ha at Aq_f
    let range_size := #(Set.range fun r ↦ f r + f (-r))
    have a_upper_bound : range_size ≤ a := by dsimp [range_size]; assumption
    have range_2 : 2 ≤ range_size := by
      have hx : (0 : ℚ) ∈ Set.range fun r ↦ f r + f (-r) := by
        simp
        use 0
        simp [f]
      have hy : (-1 : ℚ) ∈ Set.range fun r ↦ f r + f (-r) := by
        simp
        use -1/3
        simp [f]
        ring
      have hxy : (0 : ℚ) ≠ (-1 : ℚ) := by simp
      exact size_at_least_two hx hy hxy
    have temp : 2 ≤ (a : Cardinal.{0}) := by
      exact le_trans range_2 a_upper_bound
    norm_cast at temp

  · simp
    intro f hf
    let arrow (x : ℚ) (y : ℚ) : Prop := f (x + f y) = f x + y
    have harrow_xy : ∀ x y, arrow x y ∨ arrow y x := by
      dsimp [arrow]
      dsimp [Aquaesulian] at hf
      intro x y
      specialize hf x y
      obtain hf1 | hf2 := hf
      · tauto
      · right
        rw [add_comm, add_comm _ x]
        assumption
    have harrow_x : ∀ x, arrow x x := by
      intro x
      specialize harrow_xy x x
      tauto
    have hinj : Function.Injective f := by
      intro a b hab
      have harrowabba := harrow_xy a b
      obtain harrowab | harrowba := harrowabba
      · suffices htemp : f a + a = f a + b by simp at htemp; exact htemp
        calc
        f a + a = f (a + f a) := by
          specialize harrow_x a
          dsimp [arrow] at harrow_x
          symm
          assumption
        _ = f (a + f b) := by congr 3
        _ = f a + b := by simp [harrowab, arrow]
      · suffices htemp : f b + b = f b + a by simp at htemp; symm; exact htemp
        calc
        f b + b = f (b + f b) := by
          specialize harrow_x b
          dsimp [arrow] at harrow_x
          symm
          assumption
        _ = f (b + f a) := by congr 2; symm; exact hab
        _ = f b + a := by simp [harrowba, arrow]
    have harrow_con (s r : ℚ): arrow s r → (f r + f (-r) = 0 ∨ f (f s) = s + f r + f (-r)) := by
      intro hsr
      dsimp [arrow] at hsr
      let x := s + f r
      let y := -r
      specialize harrow_xy x y
      obtain harrow_xy | harrow_xy := harrow_xy
      · simp [arrow, x, y, hsr] at harrow_xy
        apply hinj at harrow_xy
        left
        rw [add_assoc] at harrow_xy
        simp at harrow_xy
        exact harrow_xy
      · simp [arrow, x, y, hsr] at harrow_xy
        right
        rw [harrow_xy]
        ring
    have hnonzero_unique (a b : ℚ) : f a + f (-a) ≠ 0 → f b + f (-b) ≠ 0 → f a + f (-a) = f b + f (-b) := by
      intro ha hb
      specialize harrow_xy a b
      obtain harrow_ab | harrow_ab := harrow_xy
      · trans f (f a) - a
        · specialize harrow_con a a
          specialize harrow_x a
          have : f (f a) = a + f a + f (-a) := by tauto
          simp [this]
          ring
        · specialize harrow_con a b
          have : f (f a) = a + f b + f (-b) := by tauto
          simp [this]
          ring
      · trans f (f b) - b
        swap
        · specialize harrow_con b b
          specialize harrow_x b
          have : f (f b) = b + f b + f (-b) := by tauto
          simp [this]
          ring
        · specialize harrow_con b a
          have : f (f b) = b + f a + f (-a) := by tauto
          simp [this]
          ring
    have hno_three (a b c: ℚ) : f a + f (-a) ≠ f b + f (-b) → f b + f (-b) ≠ f c + f (-c) → f a + f (-a) ≠ f c + f (-c) -> False := by
      intro hfa hfb hfc
      by_cases hfa0 : f a + f (-a) = 0
      · rw [hfa0] at hfa
        symm at hfa
        rw [hfa0] at hfc
        symm at hfc
        specialize hnonzero_unique b c hfa hfc
        tauto
      · by_cases hfb0 : f b + f (-b) = 0
        · rw [hfb0] at hfa
          rw [hfb0] at hfb
          symm at hfb
          specialize hnonzero_unique a c hfa hfb
          tauto
        · specialize hnonzero_unique a b hfa0 hfb0
          tauto
    apply Classical.byContradiction
    intro hC
    have := three_elements hC
    obtain ⟨⟨x0, a, ha⟩ , ⟨y0, b, hb⟩ , ⟨z0, c, hc⟩ , hneq⟩ := this
    simp at ha
    simp at hb
    simp at hc
    simp at hneq
    specialize hno_three a b c
    rw [ha, hb, hc] at hno_three
    tauto

end IMO2024P6
