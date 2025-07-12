/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib


namespace IMO2024P5


opaque S : ℕ

axiom S_2023 : S = 2023

lemma S_bigger_1 : S > 1 := by rw [S_2023]; decide

/-- A cell on the board for the game. -/
abbrev Cell : Type := Fin (S + 1) × Fin S

/-- A row that is neither the first nor the last (and thus contains a monster). -/
abbrev InteriorRow : Type := (Set.Icc ⟨1, by have := S_bigger_1; omega⟩ ⟨S - 1, by omega⟩ : Set (Fin (S + 1)))

/-- Data for valid positions of the monsters. -/
abbrev MonsterData : Type := InteriorRow ↪ Fin S

/-- The cells with monsters as a Set, given an injection from rows to columns. -/
def MonsterData.monsterCells (m : MonsterData) :
    Set Cell :=
  Set.range (fun x : InteriorRow ↦ ((x : Fin (S + 1)), m x))

/-- Whether two cells are adjacent. -/
def Adjacent (x y : Cell) : Prop :=
  Nat.dist x.1 y.1 + Nat.dist x.2 y.2 = 1

/-- A valid path from the first to the last row. -/
structure Path where
  /-- The cells on the path. -/
  cells : List Cell
  nonempty : cells ≠ []
  head_first_row : (cells.head nonempty).1 = ⟨0, by omega⟩
  last_last_row : (cells.getLast nonempty).1 = ⟨S, by omega⟩
  valid_move_seq : cells.Chain' Adjacent

/-- The first monster on a path, or `none`. -/
noncomputable def Path.firstMonster (p : Path) (m : MonsterData) : Option Cell :=
  letI := Classical.propDecidable
  p.cells.find? (fun x ↦ (x ∈ m.monsterCells : Bool))
#check List.find?
/-- A strategy, given the results of initial attempts, returns a path for the next attempt. -/
abbrev Strategy : Type := ⦃k : ℕ⦄ → (Fin k → Option Cell) → Path

/-- Playing a strategy, k attempts. -/
noncomputable def Strategy.play (s : Strategy) (m : MonsterData) :
    (k : ℕ) → Fin k → Option Cell
| 0 => Fin.elim0
| k + 1 => Fin.snoc (s.play m k) ((s (s.play m k)).firstMonster m)

/-- The predicate for a strategy winning within the given number of attempts. -/
def Strategy.WinsIn (s : Strategy) (m : MonsterData) (k : ℕ) : Prop :=
  none ∈ Set.range (s.play m k)

/-- Whether a strategy forces a win within the given number of attempts. -/
def Strategy.ForcesWinIn (s : Strategy) (k : ℕ) : Prop :=
  ∀ m, s.WinsIn m k


lemma S_bigger_0 : S > 0 := by
  have := S_bigger_1
  omega

lemma S1_bigger_0 : S - 1 > 0 := by
  have := S_bigger_1
  omega

lemma hS01 : S = S - 1 + 1 := by
  have := S_bigger_1
  omega

lemma hS12 : S - 1 = S - 2 + 1 := by
  have := S_bigger_1
  omega

lemma hS02 : S = S - 2 + 2 := by
  have := S_bigger_1
  omega


section FunAppendHeadLastChain
variable {T : Type*}
variable {m n p : ℕ}
variable (R : T → T → Prop)
variable (F : Fin m → T)
variable (G : Fin n → T)
variable (H : Fin p → T)

lemma list_of_fn_head (hLF : List.ofFn F ≠ []):
  have hm: m > 0 := by simp at hLF; omega
  (List.ofFn F).head hLF = F ⟨0, hm⟩ := by
  intro hLF
  rw [List.head_ofFn]

lemma list_of_fn_last (hLF : List.ofFn F ≠ []):
  have hm : m = (m - 1) + 1 := by simp at hLF; omega
  (List.ofFn F).getLast hLF = F ⟨m - 1, by omega⟩ := by
  intro hLF
  rw [List.getLast_ofFn]

def fn_chain : Prop := ∀ (i : ℕ), (hi : i + 1 < m) → R (F ⟨i, by omega⟩) (F ⟨i + 1, hi⟩)

lemma list_of_fn_chain : (List.ofFn F).Chain' R ↔
  fn_chain R F := by
  simp [List.chain'_iff_get]
  constructor
  · intro h i hi
    have : i < m - 1 := by omega
    specialize h i this
    exact h
  · intro h i hi
    have : i + 1 < m := by omega
    specialize h (⟨i, by omega⟩: Fin m) this
    exact h

lemma appendval1 (i : ℕ) (hi : i < m) :
  Fin.append F G ⟨i, by omega⟩ = F ⟨i, hi⟩ := by
  simp [Fin.append, Fin.addCases]
  split_ifs
  congr 1

lemma appendval2 (j : ℕ) (hj : j < n) :
  Fin.append F G ⟨m + j, by omega⟩ = G ⟨j, hj⟩ := by
  simp [Fin.append, Fin.addCases]

lemma list_append_head (hLFG : List.ofFn (Fin.append F G) ≠ []) (hm : m > 0) :
  (List.ofFn (Fin.append F G)).head hLFG = F ⟨0, hm⟩ := by
  rw [list_of_fn_head (Fin.append F G), ← appendval1 F G]

lemma list_append_last (hLFG : List.ofFn (Fin.append F G) ≠ []) (hn : n > 0) :
  have hn1 : n = (n - 1) + 1 := by simp at hLFG; omega
  (List.ofFn (Fin.append F G)).getLast hLFG = G ⟨n - 1, by omega⟩ := by
  intro hn1
  rw [list_of_fn_last (Fin.append F G), ← appendval2 F G]
  congr
  omega

lemma fn_append_chain (hm : m = (m - 1) + 1) (hn : n > 0) :
  fn_chain R (Fin.append F G) ↔ fn_chain R F ∧ fn_chain R G ∧ R (F ⟨m - 1, by omega⟩) (G ⟨0, by omega⟩) := by
  rw [fn_chain, fn_chain, fn_chain]
  constructor
  · intro h1
    repeat' constructor
    · intro i hi
      have : i + 1 < m + n := by omega
      specialize h1 i this
      convert h1
      · rw [appendval1]
      · rw [appendval1]
    · intro j hj
      have : m + j + 1 < m + n := by omega
      specialize h1 (m + j) this
      convert h1
      · rw [appendval2]
      · rw [← appendval2 F G (j + 1) hj]
        congr 1
    · have : m - 1 + 1 < m + n := by omega
      specialize h1 (m - 1) this
      convert h1
      · rw [appendval1]
      · rw [← appendval2 F G 0 hn]
        congr 1
        simp
        omega
  · intro h i hi
    obtain ⟨hF, hG, hFG⟩ := h
    by_cases hi1 : i + 1 < m
    · rw [appendval1, appendval1]
      exact hF i hi1
    · by_cases hi2 : i ≥ m
      · let j := i - m
        have hj: j < n := by omega
        have hj1: j + 1 < n := by omega
        have hij : i = m + j := by omega
        have hR : R (G ⟨j, hj⟩) (G ⟨j + 1, hj1⟩) := hG j hj1
        convert hR
        · rw [←appendval2 F G j]
          congr 2
        · rw [←appendval2 F G (j + 1)]
          congr 2
          omega
      · have hi : i = m - 1 := by omega
        convert hFG
        · rw [appendval1]
          congr 2
          omega
        · rw [←appendval2 F G 0]
          congr 2
          omega

def append3 {T : Type*} {m n p: ℕ} (F : Fin m → T) (G : Fin n → T) (H : Fin p → T) := Fin.append F (Fin.append G H)

lemma list_append3_head (hLFGH : List.ofFn (append3 F G H) ≠ []) (hm : m > 0) :
  (List.ofFn (append3 F G H)).head hLFGH = F ⟨0, hm⟩ := by
  dsimp [append3]
  dsimp [append3] at hLFGH
  rw [list_append_head]

lemma list_append3_last (hLFGH : List.ofFn (append3 F G H) ≠ []) (hp : p > 0) :
  have hp1 : p = (p - 1) + 1 := by simp at hLFGH; omega
  (List.ofFn (append3 F G H)).getLast hLFGH = H ⟨p - 1, by omega⟩ := by
  dsimp [append3]
  dsimp [append3] at hLFGH
  rw [list_append_last]
  · have : p - 1 < p := by omega
    rw [← appendval2 G H]
    congr 2
    omega
  · omega

lemma append3_chain (hm : m = (m - 1) + 1) (hn : n = (n - 1) + 1) (hp : p > 0) :
  fn_chain R (append3 F G H) ↔ fn_chain R F ∧ fn_chain R G ∧ fn_chain R H ∧ R (F ⟨m - 1, by omega⟩) (G ⟨0, by omega⟩) ∧ R (G ⟨n - 1, by omega⟩) (H ⟨0, by omega⟩) := by
  dsimp [append3]
  have hnp : n + p > 0 := by omega
  rw [fn_append_chain, fn_append_chain]
  constructor
  · intro h
    obtain ⟨hF, ⟨⟨hG, hH, hGH⟩, hFG⟩⟩ := h
    repeat (first | constructor | assumption | rw [appendval1] | convert hFG)
  · intro h
    obtain ⟨hF, hG, hH, hFG, hGH⟩ := h
    repeat (first | constructor | assumption | rw [appendval1] | convert hFG)
  · exact hn
  · exact hm

end FunAppendHeadLastChain


lemma valid_col_0 : 0 < S := S_bigger_0
lemma valid_col_S1 : S - 1 < S := by have := hS01; omega
lemma valid_row_0 : 0 < S + 1 := by simp
lemma valid_row_1 : 1 < S + 1 := by simp [S_bigger_0]
lemma valid_row_2 : 2 < S + 1 := by have := S_bigger_1; omega
lemma valid_row_i_plus_2 (i : Fin (S - 1)): i.val + 2 < S + 1 := by
  have : i.val < S - 1:= by simp
  omega

section DefStrategy

def ulcorner : Cell := (⟨0, valid_row_0⟩, ⟨0, valid_col_0⟩)
def cornerfn (i : Fin 1): Cell := ulcorner
def row1fn (j: Fin S) : Cell := (⟨1, valid_row_1⟩, j)
def collastfn (i : Fin (S - 1)) : Cell := (⟨i.val + 2, valid_row_i_plus_2 i⟩, ⟨S - 1, valid_col_S1⟩)

def path1fn := append3 cornerfn row1fn collastfn

lemma path1valid : (List.ofFn path1fn).Chain' Adjacent := by
  rw [list_of_fn_chain, path1fn, append3_chain]
  repeat' (first | constructor | rw [fn_chain])
  · intro i hi
    omega
  · intro i hi
    rw [Adjacent]
    repeat rw [row1fn]
    simp
    rw [Nat.dist]
    omega
  · intro i hi
    rw [Adjacent]
    repeat rw [collastfn]
    simp
    rw [Nat.dist]
    omega
  · rw [Adjacent, row1fn, collastfn]
    simp
    rw [Nat.dist]
  · have := S_bigger_0
    omega
  · exact S1_bigger_0

def path1 : Path := {
  cells := List.ofFn path1fn
  nonempty := by rw [path1fn]; simp
  head_first_row := by dsimp [path1fn]; rw [list_append3_head, cornerfn, ulcorner]; rfl; decide
  last_last_row := by dsimp [path1fn]; rw [list_append3_last, collastfn]; simp; have := S_bigger_1; omega; exact S1_bigger_0
  valid_move_seq := path1valid
}


def row0_cell (j : Fin S) : Cell := (⟨0, valid_row_0⟩, j)
def row1_cell (j : Fin S) : Cell := (⟨1, valid_row_1⟩, j)
def row2_cell (j : Fin S) : Cell := (⟨2, valid_row_2⟩, j)
def col_upto_row2_fn (j : Fin S) (i : Fin 3) : Cell :=
  if i = 0 then row0_cell j else if i = 1 then row1_cell j else row2_cell j
def col_from_row2_fn (j : Fin S) (i : Fin (S - 1)) : Cell := (⟨i.val + 2, by omega⟩, j)

lemma valid_col_j_left (j : Fin S) (hj1 : ⟨0, valid_col_0⟩ < j) : j - 1 < S := by omega
lemma valid_col_j_right (j : Fin S) (hj2 : j < ⟨S - 1, valid_col_S1⟩) : j + 1 < S := by omega


def path2leftfn (j : Fin S) (hj1 : ⟨0, valid_col_0⟩ < j) (hj2 : j < ⟨S - 1, valid_col_S1⟩) := Fin.append (col_upto_row2_fn ⟨j - 1, valid_col_j_left j hj1⟩) (col_from_row2_fn j)
def path2rightfn (j : Fin S) (hj1 : ⟨0, valid_col_0⟩ < j) (hj2 : j < ⟨S - 1, valid_col_S1⟩) := Fin.append (col_upto_row2_fn ⟨j + 1, valid_col_j_right j hj2⟩) (col_from_row2_fn j)

lemma path2leftvalid (j : Fin S) (hj1 : ⟨0, valid_col_0⟩ < j) (hj2 : j < ⟨S - 1, valid_col_S1⟩) : (List.ofFn (path2leftfn j hj1 hj2)).Chain' Adjacent := by
  rw [list_of_fn_chain, path2leftfn, fn_append_chain]
  repeat' (first | constructor | rw [fn_chain])
  · intro i hi
    rw [Adjacent]
    have : i = 0 ∨ i = 1 := by omega
    obtain ⟨_, _⟩ := this
    · dsimp [col_upto_row2_fn]
      repeat rw [row0_cell, row1_cell]
      simp
      rw [Nat.dist]
    · dsimp [col_upto_row2_fn]
      simp
      split_ifs
      · omega
      · repeat rw [row1_cell, row2_cell]
        simp
        rw [Nat.dist]
  · intro i hi
    rw [Adjacent]
    repeat rw [col_from_row2_fn]
    simp
    rw [Nat.dist]
    omega
  · rw [Adjacent, col_upto_row2_fn, col_from_row2_fn]
    simp
    repeat rw [row2_cell]
    simp
    rw [Nat.dist]
    omega
  · exact S1_bigger_0

lemma path2rightvalid (j : Fin S) (hj1 : ⟨0, valid_col_0⟩ < j) (hj2 : j < ⟨S - 1, valid_col_S1⟩) : (List.ofFn (path2rightfn j hj1 hj2)).Chain' Adjacent := by
  rw [list_of_fn_chain, path2rightfn, fn_append_chain]
  repeat' (first | constructor | rw [fn_chain])
  · intro i hi
    rw [Adjacent]
    have : i = 0 ∨ i = 1 := by omega
    obtain ⟨_, _⟩ := this
    · dsimp [col_upto_row2_fn]
      repeat rw [row0_cell, row1_cell]
      simp
      rw [Nat.dist]
    · dsimp [col_upto_row2_fn]
      simp
      split_ifs
      · omega
      · repeat rw [row1_cell, row2_cell]
        simp
        rw [Nat.dist]
  · intro i hi
    rw [Adjacent]
    repeat rw [col_from_row2_fn]
    simp
    rw [Nat.dist]
    omega
  · rw [Adjacent, col_upto_row2_fn, col_from_row2_fn]
    simp
    repeat rw [row2_cell]
    simp
    rw [Nat.dist]
    omega
  · exact S1_bigger_0

def path2left (j : Fin S) (hj1 : ⟨0, valid_col_0⟩ < j) (hj2 : j < ⟨S - 1, valid_col_S1⟩): Path := {
  cells := List.ofFn (path2leftfn j hj1 hj2)
  nonempty := by rw [path2leftfn]; simp
  head_first_row := by dsimp [path2leftfn]; rw [list_append_head, col_upto_row2_fn]; rfl; decide
  last_last_row := by dsimp [path2leftfn]; rw [list_append_last, col_from_row2_fn]; simp; omega; exact S1_bigger_0
  valid_move_seq := path2leftvalid j hj1 hj2
}

def path2right (j : Fin S) (hj1 : ⟨0, valid_col_0⟩ < j) (hj2 : j < ⟨S - 1, valid_col_S1⟩): Path := {
  cells := List.ofFn (path2rightfn j hj1 hj2)
  nonempty := by rw [path2rightfn]; simp
  head_first_row := by dsimp [path2rightfn]; rw [list_append_head, col_upto_row2_fn]; rfl; decide
  last_last_row := by dsimp [path2rightfn]; rw [list_append_last, col_from_row2_fn]; simp; omega; exact S1_bigger_0
  valid_move_seq := path2rightvalid j hj1 hj2
}

def path3rightfn1 (k : Fin (2 * (S - 1))) : Cell :=
  if Odd k.val then (⟨k.val / 2 + 1, by omega⟩, ⟨k.val / 2 + 1, by omega⟩)
  else (⟨k.val / 2, by omega⟩, ⟨k.val / 2 + 1, by omega⟩)
def path3leftfn1 (k : Fin (2 * (S - 1))) : Cell :=
  if Odd k.val then (⟨k.val / 2 + 1, by omega⟩, ⟨S - 1 - (k.val / 2 + 1), by omega⟩)
  else (⟨k.val / 2, by omega⟩, ⟨S - 1 - (k.val / 2 + 1), by omega⟩)

def path3rightfn2 (k : Fin 1) : Cell := (⟨S, by omega⟩, ⟨S - 1, valid_col_S1⟩)
def path3leftfn2 (k : Fin 1) : Cell := (⟨S, by omega⟩, ⟨0, valid_col_0⟩)

def path3rightfn := Fin.append path3rightfn1 path3rightfn2
def path3leftfn := Fin.append path3leftfn1 path3leftfn2

lemma odd_plus_1_even (k : ℕ) (hk : Odd k) : ¬ Odd (k + 1) := by simp_all
lemma odd_plus_1_val (k : ℕ) (hk : Odd k) : (k + 1) / 2 = k / 2 + 1 := by apply Odd.exists_bit1 at hk; obtain ⟨b, hb⟩ := hk; rw [hb]; omega
lemma even_plus_1_odd (k : ℕ) (hk : ¬ Odd k) : Odd (k + 1) := by simp_all
lemma even_plus_1_val (k : ℕ) (hk : ¬ Odd k) : (k + 1) / 2 = k / 2 := by
  have := Nat.even_or_odd k;
  have hk : Even k := by tauto;
  rw [Even] at hk
  obtain ⟨b, hb⟩ := hk; rw [hb]; omega
lemma lastodd: Odd (2 * (S - 1) - 1)  := by rw [Odd]; use S - 2; have := S_bigger_1; omega
lemma lastval: (2 * (S - 1) - 1) / 2 = S - 2 := by have := S_bigger_1; omega
lemma firsteven : ¬ Odd 0 := by simp
lemma firstval : 0 / 2 = 0 := by simp

lemma path3rightfn1adj : fn_chain Adjacent path3rightfn1 := by
  repeat' (first | assumption | constructor | rw [fn_chain])
  · intro k hk
    rw [Adjacent]
    repeat rw [path3rightfn1]
    · split_ifs with hk0 hk1 hk2
      · have := odd_plus_1_even k
        tauto
      · simp
        rw [odd_plus_1_val]
        simp
        rw [Nat.dist]
        omega
        exact hk0
      · simp
        rw [even_plus_1_val]
        simp
        rw [Nat.dist]
        omega
        exact hk0
      · have := even_plus_1_odd k
        tauto

lemma path3leftfn1adj : fn_chain Adjacent path3leftfn1 := by
  repeat' (first | assumption | constructor | rw [fn_chain])
  · intro k hk
    rw [Adjacent]
    repeat rw [path3leftfn1]
    · split_ifs with hk0 hk1 hk2
      · have := odd_plus_1_even k
        tauto
      · simp
        rw [odd_plus_1_val]
        simp
        have : S - 1 > k / 2 + 1:= by
          simp at hk0;
          rw [Odd] at hk0;
          obtain ⟨b, hb⟩ := hk0;
          rw [hb] at hk;
          have : b < S - 2 := by omega;
          have : k / 2 = b := by omega;
          omega
        rw [Nat.dist]
        omega
        exact hk0
      · simp
        rw [even_plus_1_val]
        simp
        rw [Nat.dist]
        omega
        exact hk0
      · have := even_plus_1_odd k
        tauto

lemma path3rightvalid : (List.ofFn path3rightfn).Chain' Adjacent := by
  have := S_bigger_1
  rw [list_of_fn_chain, path3rightfn, fn_append_chain]
  have := path3rightfn1adj
  repeat' (first | assumption | constructor | rw [fn_chain])
  · intro k hk
    omega
  · simp
    rw [path3rightfn1, path3rightfn2]
    have := lastodd
    have := lastval
    split_ifs
    · simp only [lastval]
      rw [Adjacent]
      simp
      have : S - 2 + 1 = S - 1 := by omega
      rw [this]
      simp
      rw [Nat.dist]
      omega
    · contradiction
  · omega

lemma path3leftvalid : (List.ofFn path3leftfn).Chain' Adjacent := by
  have := S_bigger_1
  rw [list_of_fn_chain, path3leftfn, fn_append_chain]
  have := path3leftfn1adj
  repeat' (first | assumption | constructor | rw [fn_chain])
  · intro k hk
    omega
  · simp
    rw [path3leftfn1, path3leftfn2]
    have := lastodd
    have := lastval
    split_ifs
    · simp only [lastval]
      rw [Adjacent]
      simp
      have : S - 2 + 1 = S - 1 := by omega
      rw [this]
      simp
      rw [Nat.dist]
      omega
    · contradiction
  · omega

def path3right : Path := {
  cells := List.ofFn path3rightfn
  nonempty := by rw [path3rightfn]; simp
  head_first_row := by dsimp [path3rightfn]; rw [list_append_head, path3rightfn1]; split_ifs; simp_all; simp; have := S_bigger_1; omega
  last_last_row := by dsimp [path3rightfn]; rw [list_append_last, path3rightfn2]; simp
  valid_move_seq := path3rightvalid
}
def path3left : Path := {
  cells := List.ofFn path3leftfn
  nonempty := by rw [path3leftfn]; simp
  head_first_row := by dsimp [path3leftfn]; rw [list_append_head, path3leftfn1]; split_ifs; simp_all; simp; have := S_bigger_1; omega
  last_last_row := by dsimp [path3leftfn]; rw [list_append_last, path3leftfn2]; simp
  valid_move_seq := path3leftvalid
}


def lefttoedgefn (i : Fin (S + 1)) (j : Fin S) (k : Fin j) : Cell := (i, ⟨j - 1 - k, by omega⟩)
def righttoedgefn (i : Fin (S + 1)) (j : Fin S) (k : Fin (S - 1 - j)) : Cell := (i, ⟨j + 1 + k, by omega⟩)
def leftedgedownfn (i : Fin (S + 1)) (k : Fin (S - i)) : Cell := (⟨i + 1 + k, by omega⟩, ⟨0, S_bigger_0⟩)
def rightedgedownfn (i : Fin (S + 1)) (k : Fin (S - i)) : Cell := (⟨i + 1 + k, by omega⟩, ⟨S - 1, valid_col_S1⟩)

def Restrict {T : Type*} {n : ℕ} (F : Fin n → T) (m : ℕ) (h : m ≤ n) (i : Fin m) : T := F (Fin.castLE h i)

def path4rightfn1 (k : Fin (2 * (S - 1))) (hk : k.val ≥ 3) := Restrict path3rightfn1 (k - 1) (by omega)
def path4rightfn2 (k : Fin (2 * (S - 1))) (hk : k.val ≥ 3) :=
  lefttoedgefn (path3rightfn1 k).1 (path3rightfn1 k).2
def path4rightfn3 (k : Fin (2 * (S - 1))) (hk : k.val ≥ 3) :=
  leftedgedownfn  (path3rightfn1 k).1

def path4rightfn (k : Fin (2 * (S - 1))) (hk : k.val ≥ 3) :=
  append3 (path4rightfn1 k hk) (path4rightfn2 k hk) (path4rightfn3 k hk)

def path4leftfn1 (k : Fin (2 * (S - 1))) (hk : k.val ≥ 3) := Restrict path3leftfn1 (k - 1) (by omega)
def path4leftfn2 (k : Fin (2 * (S - 1))) (hk : k.val ≥ 3) :=
  righttoedgefn (path3leftfn1 k).1 (path3leftfn1 k).2
def path4leftfn3 (k : Fin (2 * (S - 1))) (hk : k.val ≥ 3) :=
  rightedgedownfn  (path3leftfn1 k).1

def path4leftfn (k : Fin (2 * (S - 1))) (hk : k.val ≥ 3) :=
  append3 (path4leftfn1 k hk) (path4leftfn2 k hk) (path4leftfn3 k hk)

lemma odd_minus_2_odd (k : ℕ) (hk : k ≥ 3): Odd k ↔ Odd (k - 1 - 1) := by
  constructor
  · intro hk
    apply Odd.exists_bit1 at hk; obtain ⟨b, hb⟩ := hk; use b - 1; omega
  · intro hk
    apply Odd.exists_bit1 at hk; obtain ⟨b, hb⟩ := hk; use b + 1; omega

lemma odd_minus_2_val (k : ℕ) (hk : k ≥ 3): (k - 1 - 1) / 2 = k / 2 - 1 := by
  by_cases hk : Odd k
  · apply Odd.exists_bit1 at hk;
    obtain ⟨b, hb⟩ := hk; rw [hb]; omega
  · have := Nat.even_or_odd k;
    have hk : Even k := by tauto;
    rw [Even] at hk;
    obtain ⟨b, hb⟩ := hk; rw [hb]; omega

lemma path3right1notlastrow (k : Fin (2 * (S - 1))) : (path3rightfn1 k).1.val < S := by
  rw [path3rightfn1]
  split_ifs <;> (simp; omega)
lemma path3right1notfirstcol (k : Fin (2 * (S - 1))) : (path3rightfn1 k).2.val > 0 := by
  rw [path3rightfn1]
  split_ifs <;> simp
lemma path3left1notlastrow (k : Fin (2 * (S - 1))) : (path3leftfn1 k).1.val < S := by
  rw [path3leftfn1]
  split_ifs <;> (simp; omega)
lemma path3left1notlastcol (k : Fin (2 * (S - 1))) : (path3leftfn1 k).2.val < S - 1 := by
  rw [path3leftfn1]
  split_ifs <;> (simp; exact S_bigger_1)

lemma path4rightvalid (k : Fin (2 * (S - 1))) (hk : k.val ≥ 3) : (List.ofFn (path4rightfn k hk)).Chain' Adjacent := by
  have := S_bigger_1
  have path3adj := path3rightfn1adj
  rw [list_of_fn_chain, path4rightfn, append3_chain]
  repeat' (first | constructor | rw [fn_chain])
  · intro i hi
    rw [Adjacent]
    repeat rw [path4rightfn1]
    repeat rw [Restrict]
    simp
    exact path3adj i _
  · intro i hi
    rw [Adjacent]
    repeat rw [path4rightfn2]
    repeat rw [lefttoedgefn]
    simp [Nat.dist]
    omega
  · intro i hi
    rw [Adjacent]
    repeat rw [path4rightfn3]
    repeat rw [leftedgedownfn]
    simp [Nat.dist]
    omega
  · rw [Adjacent]
    repeat rw [path4rightfn1]
    repeat rw [path4rightfn2]
    repeat rw [lefttoedgefn]
    repeat rw [Restrict]
    simp
    repeat rw [path3rightfn1]
    simp
    split_ifs
    · simp
      rw [odd_minus_2_val]
      repeat rw [Nat.dist]
      omega
      exact hk
    · have := odd_minus_2_odd k hk
      tauto
    · have := odd_minus_2_odd k hk
      tauto
    · simp
      rw [odd_minus_2_val]
      repeat rw [Nat.dist]
      omega
      exact hk
  · rw [Adjacent]
    repeat rw [path4rightfn2]
    repeat rw [path4rightfn3]
    repeat rw [lefttoedgefn]
    repeat rw [leftedgedownfn]
    simp
    rw [Nat.dist]
    omega
  · omega
  · have := path3right1notfirstcol k
    omega
  · have := path3right1notlastrow k
    omega

lemma path4leftvalid (k : Fin (2 * (S - 1))) (hk : k.val ≥ 3) : (List.ofFn (path4leftfn k hk)).Chain' Adjacent := by
  have := S_bigger_1
  have path3adj := path3leftfn1adj
  rw [list_of_fn_chain, path4leftfn, append3_chain]
  repeat' (first | constructor | rw [fn_chain])
  · intro i hi
    rw [Adjacent]
    repeat rw [path4leftfn1]
    repeat rw [Restrict]
    simp
    exact path3adj i _
  · intro i hi
    rw [Adjacent]
    repeat rw [path4leftfn2]
    repeat rw [righttoedgefn]
    simp [Nat.dist]
    omega
  · intro i hi
    rw [Adjacent]
    repeat rw [path4leftfn3]
    repeat rw [rightedgedownfn]
    simp [Nat.dist]
    omega
  · rw [Adjacent]
    repeat rw [path4leftfn1]
    repeat rw [path4leftfn2]
    repeat rw [righttoedgefn]
    repeat rw [Restrict]
    simp
    repeat rw [path3leftfn1]
    simp
    split_ifs
    · simp
      rw [odd_minus_2_val]
      repeat rw [Nat.dist]
      omega
      exact hk
    · have := odd_minus_2_odd k hk
      tauto
    · have := odd_minus_2_odd k hk
      tauto
    · simp
      rw [odd_minus_2_val]
      repeat rw [Nat.dist]
      omega
      exact hk
  · rw [Adjacent]
    repeat rw [path4leftfn2]
    repeat rw [path4leftfn3]
    repeat rw [righttoedgefn]
    repeat rw [rightedgedownfn]
    simp
    have := path3left1notlastcol k
    have : ↑(path3leftfn1 k).2 + 1 + (S - 1 - ↑(path3leftfn1 k).2 - 1) = S - 1:= by omega
    rw [this, Nat.dist, Nat.dist]
    omega
  · omega
  · have := path3left1notlastcol k
    omega
  · have := path3left1notlastrow k
    omega

def path4right (k : Fin (2 * (S - 1))) (hk : k.val ≥ 3): Path := {
  cells := List.ofFn (path4rightfn k hk)
  nonempty := by rw [path4rightfn]; simp; omega
  head_first_row := by dsimp [path4rightfn]; rw [list_append3_head, path4rightfn1, Restrict, path3rightfn1]; split_ifs; simp_all; simp; omega
  last_last_row := by dsimp [path4rightfn]; rw [list_append3_last, path4rightfn3, leftedgedownfn]; simp; rw [path3rightfn1]; split_ifs; simp_all; omega; simp; omega; have := path3right1notlastrow k; omega
  valid_move_seq := path4rightvalid k hk
}
def path4left (k : Fin (2 * (S - 1))) (hk : k.val ≥ 3): Path := {
  cells := List.ofFn (path4leftfn k hk)
  nonempty := by rw [path4leftfn]; simp; omega
  head_first_row := by dsimp [path4leftfn]; rw [list_append3_head, path4leftfn1, Restrict, path3leftfn1]; split_ifs; simp_all; simp; omega
  last_last_row := by dsimp [path4leftfn]; rw [list_append3_last, path4leftfn3, rightedgedownfn]; simp; rw [path3leftfn1]; split_ifs; simp_all; omega; simp; omega; have := path3left1notlastrow k; omega
  valid_move_seq := path4leftvalid k hk
}


def ValidMonSeq {k : ℕ} (P : Fin k → Option Cell) : Prop := ∀ i, (P i).isSome
def getMonSeq {k : ℕ} (P : Fin k → Option Cell) (i : Fin k) (hP : ValidMonSeq P): Cell := Option.get (P i) (hP i)

def s00 {L : ℕ} (P : Fin L → Option Cell) (hL : L = 0): Path := path1

noncomputable def s01 {L : ℕ} (P : Fin L → Option Cell) (hL : L = 1) : Path :=
  letI Decidable := Classical.propDecidable
  if hP : ValidMonSeq P then
    letI j := (getMonSeq P ⟨0, by clear Decidable; rw [hL]; decide⟩ hP).2
    if hj2 : j < ⟨S - 1, valid_col_S1⟩ then
      if hj1 : ⟨0, valid_col_0⟩ < j then path2left j hj1 hj2
      else path3right
    else path3left
  else path1

noncomputable def s02 {L : ℕ} (P : Fin L → Option Cell) (hL : L = 2) : Path :=
  letI Decidable := Classical.propDecidable
  have := S_bigger_1
  if hP : ValidMonSeq P then
    letI j := (getMonSeq P ⟨0, by clear Decidable; rw [hL]; decide⟩ hP).2
    letI qrow := (getMonSeq P ⟨1, by clear Decidable; rw [hL]; decide⟩ hP).1
    letI qcol := (getMonSeq P ⟨1, by clear Decidable; rw [hL]; decide⟩ hP).2
    if hj2 : j < ⟨S - 1, valid_col_S1⟩ then
      if hj1 : ⟨0, valid_col_0⟩ < j then path2right j hj1 hj2
      else
        if hq: qrow.val ≥ 2 ∧ qrow.val < S ∧ qrow.val = qcol.val then
          path4right ⟨2 * qrow.val - 1, by clear Decidable; omega⟩ (by clear Decidable; simp; omega)
        else if hq: qrow.val ≥ 2 ∧ qrow.val < S - 1 ∧ qrow.val + 1 = qcol.val then
          path4right ⟨2 * qrow.val, by clear Decidable; omega⟩ (by clear Decidable; simp; omega)
        else path1
    else
      if hq: qrow.val ≥ 2 ∧ qrow.val < S ∧ qrow.val + qcol.val = S - 1 then
        path4left ⟨2 * qrow.val - 1, by clear Decidable; omega⟩ (by clear Decidable; simp; omega)
      else if hq: qrow.val ≥ 2 ∧ qrow.val < S - 1 ∧ qrow.val + qcol.val = S - 2 then
        path4left ⟨2 * qrow.val, by clear Decidable; omega⟩ (by clear Decidable; simp; omega)
      else path1
  else path1

noncomputable def s0 : Strategy := fun L P =>
  if hL : L = 0 then
    s00 P hL
  else if hL : L = 1 then
    s01 P hL
  else if hL : L = 2 then
    s02 P hL
  else path1


lemma s0_1 (L : ℕ) (P : Fin L → Option Cell) : L = 0 →  s0 P = path1 := by
  intro hL
  rw [s0]
  split_ifs
  rw [s00]

lemma s0_2 (L : ℕ) (hL : L = 1) (P : Fin L → Option Cell) (hP : ValidMonSeq P) :
  letI j := (getMonSeq P ⟨0, by rw [hL]; decide⟩ hP).2
  (∀ (hj1 : ⟨0, valid_col_0⟩ < j) (hj2 : j < ⟨S - 1, valid_col_S1⟩), s0 P = path2left j hj1 hj2)
  ∧ (j = ⟨0, valid_col_0⟩ → s0 P = path3right)
  ∧ (j = ⟨S - 1, valid_col_S1⟩ → s0 P = path3left) := by
  rw [s0]
  have := S_bigger_1
  constructor
  · intro hj1 hj2
    split_ifs
    · omega
    · rw [s01]
      split_ifs
      rfl
  · constructor
    · intro hj
      split_ifs with hL0
      · omega
      · rw [s01]
        split_ifs with hj2 hj1
        · omega
        · rfl
        · simp [hj] at hj2
          omega
    · intro hj
      split_ifs with hL0
      · omega
      · rw [s01]
        split_ifs with hj2 hj1
        · omega
        · simp [hj] at hj1
          omega
        · rfl

lemma s0_3 (L : ℕ) (hL : L = 2) (P : Fin L → Option Cell) (hP : ValidMonSeq P) :
  letI j := (getMonSeq P ⟨0, by rw [hL]; decide⟩ hP).2
  letI qrow := (getMonSeq P ⟨1, by rw [hL]; decide⟩ hP).1
  letI qcol := (getMonSeq P ⟨1, by rw [hL]; decide⟩ hP).2
  (∀ (hj1 : ⟨0, valid_col_0⟩ < j) (hj2 : j < ⟨S - 1, valid_col_S1⟩), s0 P = path2right j hj1 hj2)
  ∧ (j = ⟨0, valid_col_0⟩ → (hqrowlb : qrow.val ≥ 2) → (hqrowub : qrow.val < S) → (hqrc : qrow.val = qcol.val) → s0 P = path4right ⟨2 * qrow.val - 1, by omega⟩ (by simp; omega))
  ∧ (j = ⟨0, valid_col_0⟩ → (hqrowlb : qrow.val ≥ 2) → (hqrowub : qrow.val < S - 1) → (hqrc : qrow.val + 1= qcol.val) → s0 P = path4right ⟨2 * qrow.val, by omega⟩ (by simp; omega))
  ∧ (j = ⟨S - 1, valid_col_S1⟩ → (hqrowlb : qrow.val ≥ 2) → (hqrowub : qrow.val < S) → (hqrc : qrow.val + qcol.val = S - 1) → s0 P = path4left ⟨2 * qrow.val - 1, by omega⟩ (by simp; omega))
  ∧ (j = ⟨S - 1, valid_col_S1⟩ → (hqrowlb : qrow.val ≥ 2) → (hqrowub : qrow.val < S - 1) → (hqrc : qrow.val + qcol.val = S - 2) → s0 P = path4left ⟨2 * qrow.val, by omega⟩ (by simp; omega)) := by

  rw [s0]
  have := S_bigger_1
  constructor
  · intro hj1 hj2
    split_ifs
    · omega
    · omega
    · rw [s02]
      split_ifs
      rfl
  · constructor
    · intro hj
      split_ifs with hL0 hL1
      · omega
      · omega
      · rw [s02]
        intros
        split_ifs with hj2 hj1 <;> (rw [hj] at hj2; try simp at hj2; omega)
    · constructor
      · intro hj
        split_ifs with hL0 hL1
        · omega
        · omega
        · rw [s02]
          intros
          split_ifs with hj2 hj1 <;> (rw [hj] at hj2; try simp at hj2; omega)
      · constructor
        · intro hj
          intros
          split_ifs with hL0 hL1
          · omega
          · omega
          · rw [s02]
            split_ifs with hj2 hj1 <;> (try omega)
            · rfl
        · intros
          split_ifs with hL0 hL1
          · omega
          · omega
          · rw [s02]
            split_ifs with hj2 hj1 <;> (try omega)
            · rfl

end DefStrategy

section FindFirst
variable {T : Type*}
variable {m n k: ℕ}
variable (F : Fin m → T)
variable (G : Fin n → T)
variable (H : Fin k → T)
variable (A : Set T)

lemma ListFindNone :
  letI := Classical.propDecidable
  (List.ofFn F).find? (fun x ↦ (x ∈ A : Bool)) = none ↔ ∀ (i : Fin m), ¬ F i ∈ A := by simp

lemma ListFindSome (y : T):
  letI := Classical.propDecidable
  (List.ofFn F).find? (fun x ↦ (x ∈ A : Bool)) = some y ↔ ∃ (i : Fin m), (y = F i ∧ y ∈ A ∧ ∀ (j : Fin m), j.val < i.val → ¬ F j ∈ A) := by
  induction m with
  | zero => simp
  | succ m ih =>
    let G (i : Fin m) : T := F i.succ
    specialize ih G
    rw [List.ofFn_succ]
    by_cases h0 : F 0 ∈ A
    · rw [List.find?_cons_of_pos]
      simp
      constructor
      · intro hF0
        use 0
        constructor
        · exact hF0.symm
        · constructor
          · rw [← hF0]; exact h0
          · simp
      · intro hF0
        obtain ⟨i, hFi1, hFi2, hFi3⟩ := hF0
        specialize hFi3 0
        have : ¬ 0 < i.val := by tauto
        have : 0 = i.val := by omega
        convert hFi1.symm
        simp [Fin.ext_iff]
        exact this
      · simp [h0]
    · rw [List.find?_cons_of_neg]
      · constructor
        · intro hF0
          rw [ih] at hF0
          obtain ⟨i0, hG1, hG2, hG3⟩ := hF0
          use i0 + 1
          constructor
          · convert hG1; simp
          · constructor
            · convert hG2
            . intro j hj
              by_cases hj0 : j.val = 0
              · convert h0; rw [Fin.ext_iff]; exact hj0
              · have : j.val - 1 < j.val := by omega
                specialize hG3 ⟨j - 1, by omega⟩
                simp at hj
                have : j.val - 1 < i0.val := by omega
                specialize hG3 this
                convert hG3
                simp
                have : j.val = j.val - 1 + 1 := by omega
                simp [←this]
        · intro hF0
          obtain ⟨i0, hFi1, hFi2, hFi3⟩ := hF0
          rw [ih]
          have hi00 : i0 ≠ 0 := by by_contra hC; rw [hC] at hFi1; rw [hFi1] at hFi2; tauto
          use Fin.pred i0 hi00
          have : G (i0.pred hi00) = F i0 := by dsimp [G]; congr 1; simp
          rw [this]
          constructor
          · rw [hFi1]
          · constructor
            · exact hFi2
            · intro j hj
              dsimp [G]
              specialize hFi3 (Fin.succ j)
              apply hFi3
              simp
              simp at hj
              omega
      · simp; exact h0

lemma ListFindNone2 :
  letI := Classical.propDecidable
  (List.ofFn (Fin.append F G)).find? (fun x ↦ (x ∈ A : Bool)) = none ↔ (∀ i, ¬ F i ∈ A) ∧ (∀ i, ¬ G i ∈ A) := by simp

lemma ListFindSome2 (y : T):
  letI := Classical.propDecidable
  (List.ofFn (Fin.append F G)).find? (fun x ↦ (x ∈ A : Bool)) = some y ↔
  ( (∃ (i : Fin m), (y = F i ∧ y ∈ A ∧ ∀ (j : Fin m), j.val < i.val → ¬ F j ∈ A))
    ∨
    ((∀ i, ¬ F i ∈ A) ∧ ∃ (i : Fin n), (y = G i ∧ y ∈ A ∧ ∀ (j : Fin n), j.val < i.val → ¬ G j ∈ A))
  ) := by
  rw [ListFindSome]
  constructor
  · intro h
    obtain ⟨i0, hi0⟩ := h
    by_cases hi0m : i0.val < m
    · left
      use ⟨i0.val, hi0m⟩
      rw [appendval1 F G i0 hi0m] at hi0
      simp at hi0
      simp
      obtain ⟨hi01, hi02, hi03⟩ := hi0
      repeat (first | constructor | assumption)
      · intro j hj
        specialize hi03 ⟨j, by omega⟩ hj
        rw [appendval1 F G j] at hi03
        exact hi03
    · right
      obtain ⟨hi01, hi02, hi03⟩ := hi0
      constructor
      · intro i
        specialize hi03 ⟨i, by omega⟩
        rw [appendval1 F G i] at hi03
        apply hi03
        simp
        omega
      · let i1 := i0.val - m
        use ⟨i1, by omega⟩
        have i0_sum : i0 = ⟨m + i1, by omega⟩ := by simp [Fin.ext_iff]; omega
        rw [i0_sum] at hi01
        rw [i0_sum] at hi03
        rw [appendval2 F G] at hi01
        repeat (first | constructor | assumption)
        · intro j hj
          specialize hi03 ⟨m + j, by omega⟩ (by simp; omega)
          rw [appendval2 F G] at hi03
          assumption
  · intro h
    obtain hF | hG := h
    · obtain ⟨i0, hi01, hi02, hi03⟩ := hF
      use ⟨i0, by omega⟩
      rw [appendval1 F G]
      repeat (first | constructor | assumption)
      · intro j hj
        rw [appendval1 F G]
        simp at hj
        specialize hi03 ⟨j, by omega⟩ hj
        assumption
    · obtain ⟨hF, j0, hj01, hj02, hj03⟩ := hG
      use ⟨m + j0, by omega⟩
      rw [appendval2 F G]
      repeat (first | constructor | assumption)
      · intro j hj
        by_cases hjm : j.val < m
        · rw [appendval1]
          exact hF ⟨j.val, by omega⟩
        · let j1 := j.val - m
          simp at hj
          simp at hjm
          have hj1m : j = ⟨m + j1, by omega⟩ := by simp [Fin.ext_iff]; omega
          rw [hj1m]
          rw [appendval2]
          apply hj03 ⟨j1, by omega⟩
          simp
          omega

lemma ListFindNone3 :
  letI := Classical.propDecidable
  (List.ofFn (append3 F G H)).find? (fun x ↦ (x ∈ A : Bool)) = none ↔ (∀ i, ¬ F i ∈ A) ∧ (∀ i, ¬ G i ∈ A) ∧ (∀ i, ¬ H i ∈ A):= by dsimp [append3]; simp

lemma ListFindSome3 (y : T):
  letI := Classical.propDecidable
  (List.ofFn (append3 F G H)).find? (fun x ↦ (x ∈ A : Bool)) = some y ↔
  ( (∃ (i : Fin m), (y = F i ∧ y ∈ A ∧ ∀ (j : Fin m), j.val < i.val → ¬ F j ∈ A))
    ∨
    ((∀ i, ¬ F i ∈ A) ∧
      (
        (∃ (i : Fin n), (y = G i ∧ y ∈ A ∧ ∀ (j : Fin n), j.val < i.val → ¬ G j ∈ A))
        ∨
        ((∀ i, ¬ G i ∈ A) ∧ ∃ (i : Fin k), (y = H i ∧ y ∈ A ∧ ∀ (j : Fin k), j.val < i.val → ¬ H j ∈ A))
      )
    )
  ) := by
  rw [append3]
  rw [ListFindSome2]
  rw [←ListFindSome2 G H A y]
  rw [ListFindSome (Fin.append G H)]

end FindFirst

section MonsterAlign

variable (m : MonsterData)
variable (x y : Cell)

lemma monsterdiffrow (hx : x ∈ m.monsterCells) (hy : y ∈ m.monsterCells): x.1 = y.1 → x = y := by
  unfold MonsterData.monsterCells at *
  unfold Set.range at *
  simp at *
  obtain ⟨a, ha1, ha2⟩ := hx
  obtain ⟨b, hb1, hb2⟩ := hy
  intro hxy
  rw [←ha2, ←hb2] at hxy
  simp at hxy
  trans (a, m ⟨a, by simp; exact ha1⟩)
  · exact ha2.symm
  · rw [← hb2]
    congr

lemma monsterdiffcol (hx : x ∈ m.monsterCells) (hy : y ∈ m.monsterCells): x.2 = y.2 → x = y := by
  unfold MonsterData.monsterCells at *
  unfold Set.range at *
  simp at *
  obtain ⟨a, ha1, ha2⟩ := hx
  obtain ⟨b, hb1, hb2⟩ := hy
  intro hxy
  rw [←ha2, ←hb2] at hxy
  simp at hxy
  trans (a, m ⟨a, by simp; exact ha1⟩)
  · exact ha2.symm
  · rw [← hb2]
    congr

lemma monsternotfirstrow (hx : x.1.val = 0) : x ∉ m.monsterCells := by
  unfold MonsterData.monsterCells
  unfold Set.range
  simp
  intro a ha
  by_contra hC
  rw [← hC] at hx
  simp at hx
  obtain ⟨ha, _⟩ := ha
  apply Fin.le_def.mp at ha
  simp at ha
  apply_fun (·.val) at hx
  rw [hx] at ha
  simp at ha

lemma monsternotlastrow (hx : x.1.val = S) : x ∉ m.monsterCells := by
  unfold MonsterData.monsterCells
  unfold Set.range
  simp
  intro a ha
  by_contra hC
  rw [← hC] at hx
  simp at hx
  obtain ⟨_ , ha⟩ := ha
  apply Fin.le_def.mp at ha
  simp at ha
  rw [hx] at ha
  have := S_bigger_1
  omega

lemma monstereveryrow (i : ℕ): 1 ≤ i → i ≤ S - 1 → ∃ (z : Cell), z ∈ m.monsterCells ∧ z.1.val = i := by
  intro hi1 hi2
  let i0 : Fin (S + 1) := ⟨i, by omega⟩
  have : i0 ∈ Set.Icc ⟨1, by have := S_bigger_1; omega⟩ ⟨S - 1, by omega⟩ := by simp; constructor <;> simp [i0, hi1, hi2]
  use (i0, m ⟨i0, this⟩ )
  constructor
  · dsimp [MonsterData.monsterCells, Set.range]
    use ⟨i0, this⟩
  · simp [i0]


lemma hS3 : S ≥ 3 := by rw [S_2023]; decide

def rowoneindex : InteriorRow := ⟨⟨1, valid_row_1⟩, by dsimp [Set.Icc]; simp; have := hS3; omega⟩
def rowtwoindex : InteriorRow := ⟨⟨2, valid_row_2⟩, by dsimp [Set.Icc]; simp; have := hS3; omega⟩

lemma monsterpossible1 (a : Fin S) (hS3 : S ≥ 3) : ∃ (m : MonsterData), (⟨1, valid_row_1⟩, a) ∈ m.monsterCells ∧ m rowoneindex = a := by
  let mfun0 (i : InteriorRow) : Fin S := ⟨i.val.val - 1, by omega⟩
  have : Function.Injective mfun0 := by
    dsimp [Function.Injective, mfun0, InteriorRow, Set.Icc]
    intro x y hxy
    simp at hxy
    have ⟨hx1, _⟩ := x.property
    apply Fin.le_def.mp at hx1
    simp at hx1
    have ⟨hy1, _⟩ := y.property
    apply Fin.le_def.mp at hy1
    simp at hy1
    ext
    omega

  let m0 : MonsterData := ⟨mfun0, this⟩
  let m := Function.Embedding.setValue m0 rowoneindex a
  use m
  dsimp [MonsterData.monsterCells, Set.range]
  constructor
  · use rowoneindex
    simp [rowoneindex, m]
  · simp [rowoneindex, m]

lemma monsterpossible2 (a b: Fin S) (hS3 : S ≥ 3) : a ≠ b → ∃ (m : MonsterData), ((⟨1, valid_row_1⟩, a) ∈ m.monsterCells ∧ (⟨2, valid_row_2⟩, b) ∈ m.monsterCells ∧ m rowoneindex = a) := by
  intro hab
  let ⟨m1, hm1, hm2⟩ := monsterpossible1 a hS3
  let m := Function.Embedding.setValue m1 rowtwoindex b
  use m
  dsimp [MonsterData.monsterCells, Set.range]
  have : m rowoneindex = a := by
    simp [rowoneindex, m]
    have h12 : rowoneindex ≠ rowtwoindex := by simp [rowoneindex, rowtwoindex]
    have h1m : m1 rowoneindex ≠ b := by simp [hm2, hab]
    convert Function.Embedding.setValue_eq_of_ne h12 h1m
    exact hm2.symm
  constructor
  · use rowoneindex
    simp [this]
    dsimp [rowoneindex]
  · constructor
    · use rowtwoindex
      simp [rowtwoindex, m]
    · exact this


end MonsterAlign


section PlayEndIn3

variable (s : Strategy)
variable (m : MonsterData)
#check s0

lemma splay0 : s.play m 0 = Fin.elim0 := by
  dsimp [Strategy.play]
lemma splaysucc1 (k : ℕ) (i : Fin k): s.play m (k + 1) i.castSucc = s.play m k i := by
  dsimp [Strategy.play]
  simp
lemma splaysucc2 (k : ℕ) : s.play m (k + 1) (Fin.last k) = (s (s.play m k)).firstMonster m := by
  dsimp [Strategy.play]
  simp

lemma s0play1 : ∃ (x : Cell), s0.play m 1 0 = some x ∧ x.1.val = 1 ∧ x ∈ m.monsterCells := by
  have := S_bigger_1
  have h1: 1 ≤ 1 := by omega
  have h2: 1 ≤ S - 1 := by omega
  have ⟨z, hz0, hz1⟩ := monstereveryrow m 1 h1 h2
  use z
  constructor
  · convert (splaysucc2 s0 m 0)
    rw [splay0]
    dsimp [s0, s00, Path.firstMonster]
    rw [path1]
    simp
    rw [path1fn]
    symm
    rw [ListFindSome3]
    right
    constructor
    · intro i
      simp [cornerfn]
      apply monsternotfirstrow m ulcorner
      simp [ulcorner]
    · left
      use z.2
      rw [row1fn]
      constructor
      · have : z = (z.1, z.2) := by simp
        rw [this]
        congr
        simp [Fin.ext_iff]
        exact hz1
      · constructor
        · exact hz0
        · intro j hj
          by_contra hC
          have : z.1 = (row1fn j).1 := by rw [row1fn]; simp [hz1, Fin.ext_iff]
          have := monsterdiffrow m z (row1fn j) hz0 hC this
          rw [row1fn] at this
          have : z.2 = j := by simp [this]
          simp at hj
          omega
  · constructor <;> assumption

lemma s0winsin3: s0.ForcesWinIn 3 := by
  dsimp [Strategy.ForcesWinIn, Strategy.WinsIn]
  intro m
  dsimp [Set.range]
  by_contra hC
  simp at hC
  have hC1 := hC 1
  have hC2 := hC 2
  replace hC1 : ∃ x, some x = s0.play m 3 1  := by rw [← Option.ne_none_iff_exists]; exact hC1
  replace hC2 : ∃ x, some x = s0.play m 3 2  := by rw [← Option.ne_none_iff_exists]; exact hC2
  obtain ⟨y, hCy_backup⟩ := hC1
  have hCy := hCy_backup
  obtain ⟨z, hCz_backup⟩ := hC2
  have hCz := hCz_backup
  clear hC
  have h210 := splaysucc1 s0 m 1 0
  have h320 := splaysucc1 s0 m 2 0
  have h321 := splaysucc1 s0 m 2 1
  have h3 := splaysucc2 s0 m 2
  have h2 := splaysucc2 s0 m 1
  simp at *
  rw [Path.firstMonster, s0] at h2
  rw [h321, h2] at hCy
  simp at hCy
  rw [s01] at hCy

  -- 1st try, find monster x on row 1, use path1
  have ⟨x, hx01, hx02, hx03⟩ := s0play1 m

  have hV1: ValidMonSeq (s0.play m 1) := by
    dsimp [ValidMonSeq]
    intro i
    have : i = 0 := by omega
    simp [this, hx01]

  have hMS1: getMonSeq (s0.play m 1) 0 hV1 = x := by
    dsimp [getMonSeq]
    simp [hx01]

  have hV2 : ValidMonSeq (s0.play m 2) := by
    dsimp [ValidMonSeq]
    intro i1
    have : i1 = 0 ∨ i1 = 1 := by omega
    cases this with
    | inl hi10 => rw [hi10, h210]; simp [hx01]
    | inr hi11 => rw [hi11, ← h321]; simp [← hCy_backup]

  have hMS20: getMonSeq (s0.play m 2) 0 hV2 = x := by
    dsimp [getMonSeq]
    rw [← h210] at hx01
    simp [hx01]

  have hMS21: getMonSeq (s0.play m 2) 1 hV2 = y := by
    dsimp [getMonSeq]
    rw [h321] at hCy_backup
    simp [← hCy_backup]

  simp [hV1, hMS1] at hCy

  by_cases hx2 : x.2 < ⟨S - 1, valid_col_S1⟩
  · simp [hx2] at hCy
    by_cases hx1 : ⟨0, valid_col_0⟩ < x.2
    · -- 2nd try, monster at (1, x.2), 0 < x.2 < S-1, use path2left
      simp [hx1] at hCy
      rw [path2left] at hCy
      simp at hCy
      rw [path2leftfn] at hCy
      symm at hCy
      rw [ListFindSome2] at hCy
      obtain hCy1 | hCy2 := hCy
      · obtain ⟨i, hCy10, hCy11, _⟩ := hCy1
        rw [col_upto_row2_fn, row0_cell, row1_cell, row2_cell] at hCy10
        split_ifs at hCy10 with hi0 hi1
        · apply monsternotfirstrow at hCy11
          · contradiction
          · rw [hCy10]
        · have : y.1 = x.1 := by simp [hx01, hCy10, Fin.ext_iff, hx02]
          have := monsterdiffrow m y x hCy11 hx03 this
          apply_fun (·.2.val) at this
          rw [hCy10] at this
          simp at this
          omega
        · -- 3rd try, monster at (2, x.2 - 1), use path2right
          have hi2 : i = 2 := by omega
          rw [Path.firstMonster, s0] at h3
          rw [h3] at hCz
          simp at hCz
          rw [s02] at hCz
          simp [hV2, hMS20, hMS21, hx1, hx2] at hCz
          rw [path2right] at hCz
          simp at hCz
          rw [path2rightfn] at hCz
          symm at hCz
          rw [ListFindSome2] at hCz
          obtain hCz1 | hCz2 := hCz
          · obtain ⟨i, hCz10, hCz11, _⟩ := hCz1
            rw [col_upto_row2_fn, row0_cell, row1_cell, row2_cell] at hCz10
            split_ifs at hCz10 with hi0 hi1
            · apply monsternotfirstrow at hCz11
              · contradiction
              · rw [hCz10]
            · have : z.1 = x.1 := by simp [hx01, hCz10, Fin.ext_iff, hx02]
              have := monsterdiffrow m z x hCz11 hx03 this
              apply_fun (·.2.val) at this
              rw [hCz10] at this
              simp at this
            · have hi2 : i = 2 := by omega
              have : z.1 = y.1 := by simp [hCz10, hCy10]
              have := monsterdiffrow m z y hCz11 hCy11 this
              apply_fun (·.2.val) at this
              rw [hCz10, hCy10] at this
              simp at this
              omega
          · obtain ⟨_, i, hCz20, hCz21, _⟩ := hCz2
            rw [col_from_row2_fn] at hCz20
            have : x = z := by
              apply monsterdiffcol m x z
              · tauto
              · assumption
              · rw [hCz20]
            rw [← this] at hCz20
            apply_fun (·.1.val) at hCz20
            simp at hCz20
            omega
      · obtain ⟨_, i, hCy20, hCy21, _⟩ := hCy2
        rw [col_from_row2_fn] at hCy20
        have : x = y := by
          apply monsterdiffcol m x y
          · tauto
          · assumption
          · rw [hCy20]
        rw [← this] at hCy20
        apply_fun (·.1.val) at hCy20
        simp at hCy20
        omega
    · -- 2nd try, monster at (1, 0), use path3right
      simp [hx1] at hCy
      rw [path3right] at hCy
      simp only at hCy
      rw [path3rightfn] at hCy
      symm at hCy
      rw [ListFindSome2] at hCy
      have hx20: x.2.val = 0 := by simp at hx1; apply Fin.le_def.mp at hx1; simp at hx1; exact hx1

      obtain hCy1 | hCy2 := hCy
      · obtain ⟨q, hCy10, hCy11, hCy12⟩ := hCy1
        rw [path3rightfn1] at hCy10
        rw [Path.firstMonster, s0] at h3
        rw [h3] at hCz
        simp at hCz
        rw [s02] at hCz
        simp [hV2, hMS20, hMS21, hx1, hx2] at hCz
        split_ifs at hCy10 with hqodd
        · -- 3nd try, monster at (k, k), use path4right, odd case
          have hyodd: 2 ≤ y.1.val ∧ y.1.val < S ∧ y.1.val = y.2.val := by
            rw [hCy10]; simp; constructor
            · by_contra hCq
              have hy20: y.2.val > 0 := by simp [hCy10]
              have hxyneq: x ≠ y := by intro hCxy; rw [hCxy] at hx20; omega
              have : x.1.val = y.1.val := by simp [hx02, hCy10]; omega
              have hxy1: x.1 = y.1 := by simp [this, Fin.ext_iff]
              have := monsterdiffrow m x y hx03 hCy11 hxy1
              contradiction
            · omega
          have : 2 ≤ y.2.val := by obtain ⟨hyodd1, hyodd2, hyodd3⟩ := hyodd; rw [←hyodd3]; exact hyodd1
          simp [hyodd] at hCz
          simp [this] at hCz
          dsimp [path4right, path4rightfn] at hCz
          symm at hCz
          rw [ListFindSome3] at hCz
          obtain hCz1 | hCz2 := hCz
          · obtain ⟨r, hCz11, hCz12, _⟩ := hCz1
            dsimp [path4rightfn1, Restrict] at hCz11
            specialize hCy12 (Fin.castLE (by omega) r)
            apply hCy12
            · simp
              have : y.2.val = q.val / 2 + 1 := by simp [hCy10]
              have : r < 2 * y.2.val - 1 - 1 := by simp
              omega
            · rw [← hCz11]; exact hCz12
          · obtain ⟨_, hCz2⟩ := hCz2
            have : Odd (2 * y.2.val - 1) := by dsimp [Odd]; use y.2.val - 1; omega
            obtain hCz2 | hCz2 := hCz2
            · obtain ⟨r, hCz21, hCz22, _⟩ := hCz2
              convert monsterdiffrow m y z hCy11 hCz22
              simp
              constructor
              · rw [hCy10, hCz21, path4rightfn2, lefttoedgefn]
                simp
                dsimp [path3rightfn1]
                simp [this]
                rw [hCy10]
                simp
                omega
              · intro hCyz
                rw [hCy10, hCz21, path4rightfn2, lefttoedgefn] at hCyz
                apply_fun (·.2.val) at hCyz
                simp at hCyz
                dsimp [path3rightfn1] at hCyz
                simp [this] at hCyz
                simp [hCy10] at hCyz
                omega
            · obtain ⟨_, r, hCz21, hCz22, _⟩ := hCz2
              convert monsterdiffcol m x z hx03 hCz22
              simp
              constructor
              · rw [hCz21, path4rightfn3, leftedgedownfn]
                simp [hx20, Fin.ext_iff]
              · intro hCxz
                rw [hCz21, path4rightfn3, leftedgedownfn] at hCxz
                apply_fun (·.1.val) at hCxz
                simp at hCxz
                dsimp [path3rightfn1] at hCxz
                simp [this] at hCxz
                simp [hCy10] at hCxz
                omega
        · -- 3rd try, monster at (k - 1, k), use path4right, even case
          have hyodd: 2 ≤ y.1.val ∧ y.1.val < S - 1 ∧ y.1.val + 1 = y.2.val := by
            rw [hCy10]; simp; constructor
            · by_contra hCq
              have : q.val / 2 = 0 ∨ q.val / 2 = 1 := by omega
              obtain hq0 | hq1 := this
              · convert monsternotfirstrow m y _ hCy11
                simp [hCy10, hq0]
              · have hy20: y.2.val > 0 := by simp [hCy10]
                have hxyneq: x ≠ y := by intro hCxy; rw [hCxy] at hx20; omega
                have : x.1.val = y.1.val := by simp [hx02, hCy10]; omega
                have hxy1: x.1 = y.1 := by simp [this, Fin.ext_iff]
                have := monsterdiffrow m x y hx03 hCy11 hxy1
                contradiction
            · omega
          have : y.1.val ≠ y.2.val := by obtain ⟨hyodd1, hyodd2, hyodd3⟩ := hyodd; omega
          simp [hyodd] at hCz
          simp [this] at hCz
          dsimp [path4right, path4rightfn] at hCz
          symm at hCz
          rw [ListFindSome3] at hCz
          obtain hCz1 | hCz2 := hCz
          · obtain ⟨r, hCz11, hCz12, _⟩ := hCz1
            dsimp [path4rightfn1, Restrict] at hCz11
            specialize hCy12 (Fin.castLE (by omega) r)
            apply hCy12
            · simp
              have : y.2.val = q.val / 2 + 1 := by simp [hCy10]
              omega
            · rw [← hCz11]; exact hCz12
          · obtain ⟨_, hCz2⟩ := hCz2
            have : ¬ Odd (2 * y.1.val) := by simp [Odd]; intro x hx; omega
            obtain hCz2 | hCz2 := hCz2
            · obtain ⟨r, hCz21, hCz22, _⟩ := hCz2
              convert monsterdiffrow m y z hCy11 hCz22
              simp
              constructor
              · rw [hCy10, hCz21, path4rightfn2, lefttoedgefn]
                simp
                dsimp [path3rightfn1]
                simp [this]
                rw [hCy10]
              · intro hCyz
                rw [hCy10, hCz21, path4rightfn2, lefttoedgefn] at hCyz
                apply_fun (·.2.val) at hCyz
                simp at hCyz
                dsimp [path3rightfn1] at hCyz
                simp [this] at hCyz
                simp [hCy10] at hCyz
                omega
            · obtain ⟨_, r, hCz21, hCz22, _⟩ := hCz2
              convert monsterdiffcol m x z hx03 hCz22
              simp
              constructor
              · rw [hCz21, path4rightfn3, leftedgedownfn]
                simp [hx20, Fin.ext_iff]
              · intro hCxz
                rw [hCz21, path4rightfn3, leftedgedownfn] at hCxz
                apply_fun (·.1.val) at hCxz
                simp at hCxz
                dsimp [path3rightfn1] at hCxz
                simp [this] at hCxz
                simp [hCy10] at hCxz
                have : q.val / 2 ≥ 2 := by apply_fun (·.1.val) at hCy10; simp at hCy10; rw [hCy10] at hyodd; tauto
                omega
      · obtain ⟨_, i, hCy20, hCy21, _⟩ := hCy2
        rw [path3rightfn2] at hCy20
        rw [hCy20] at hCy21
        apply monsternotlastrow at hCy21
        · contradiction
        · simp

  · -- 2nd try, monster at (1, S - 1), use path3left
    simp [hx2] at hCy
    rw [path3left] at hCy
    simp only at hCy
    rw [path3leftfn] at hCy
    symm at hCy
    rw [ListFindSome2] at hCy
    have hx20: x.2.val = S - 1 := by simp at hx2; apply Fin.le_def.mp at hx2; simp at hx2; omega

    obtain hCy1 | hCy2 := hCy
    · obtain ⟨q, hCy10, hCy11, hCy12⟩ := hCy1
      rw [path3leftfn1] at hCy10
      rw [Path.firstMonster, s0] at h3
      rw [h3] at hCz
      simp at hCz
      rw [s02] at hCz
      simp [hV2, hMS20, hMS21, hx2] at hCz
      split_ifs at hCy10 with hqodd
      · -- 3nd try, monster at (k, S - 1 - k), use path4left, odd case
        have hyodd: 2 ≤ y.1.val ∧ y.1.val < S ∧ y.1.val + y.2.val = S - 1 := by
          rw [hCy10]; simp; constructor
          · by_contra hCq
            have hy20: y.2.val < S - 1 := by simp [hCy10]; omega
            have hxyneq: x ≠ y := by intro hCxy; rw [hCxy] at hx20; omega
            have : x.1.val = y.1.val := by simp [hx02, hCy10]; omega
            have hxy1: x.1 = y.1 := by simp [this, Fin.ext_iff]
            have := monsterdiffrow m x y hx03 hCy11 hxy1
            contradiction
          · constructor
            · omega
            · omega
        simp [hyodd] at hCz
        dsimp [path4left, path4leftfn] at hCz
        symm at hCz
        rw [ListFindSome3] at hCz
        obtain hCz1 | hCz2 := hCz
        · obtain ⟨r, hCz11, hCz12, _⟩ := hCz1
          dsimp [path4leftfn1, Restrict] at hCz11
          specialize hCy12 (Fin.castLE (by omega) r)
          apply hCy12
          · simp
            have : y.1.val = q.val / 2 + 1 := by simp [hCy10]
            have : r < 2 * y.1.val - 1 - 1 := by simp
            omega
          · rw [← hCz11]; exact hCz12
        · obtain ⟨_, hCz2⟩ := hCz2
          have : Odd (2 * y.1.val - 1) := by dsimp [Odd]; use y.1.val - 1; omega
          obtain hCz2 | hCz2 := hCz2
          · obtain ⟨r, hCz21, hCz22, _⟩ := hCz2
            convert monsterdiffrow m y z hCy11 hCz22
            simp
            constructor
            · rw [hCy10, hCz21, path4leftfn2, righttoedgefn]
              simp
              dsimp [path3leftfn1]
              simp [this]
              rw [hCy10]
              simp
              omega
            · intro hCyz
              rw [hCy10, hCz21, path4leftfn2, righttoedgefn] at hCyz
              apply_fun (·.2.val) at hCyz
              simp at hCyz
              dsimp [path3leftfn1] at hCyz
              simp [this] at hCyz
              simp [hCy10] at hCyz
              omega
          · obtain ⟨_, r, hCz21, hCz22, _⟩ := hCz2
            convert monsterdiffcol m x z hx03 hCz22
            simp
            constructor
            · rw [hCz21, path4leftfn3, rightedgedownfn]
              simp [hx20, Fin.ext_iff]
            · intro hCxz
              rw [hCz21, path4leftfn3, rightedgedownfn] at hCxz
              apply_fun (·.1.val) at hCxz
              simp at hCxz
              dsimp [path3leftfn1] at hCxz
              simp [this] at hCxz
              simp [hCy10] at hCxz
              omega
      · -- 3rd try, monster at (k - 1, S - 1 - k), use path4left, even case
        have hyodd: 2 ≤ y.1.val ∧ y.1.val < S - 1 ∧ y.1.val + y.2.val = S - 2 := by
          rw [hCy10]; simp; constructor
          · by_contra hCq
            have : q.val / 2 = 0 ∨ q.val / 2 = 1 := by omega
            obtain hq0 | hq1 := this
            · convert monsternotfirstrow m y _ hCy11
              simp [hCy10, hq0]
            · have hy20: y.2.val < S - 1 := by simp [hCy10, S_bigger_1]
              have hxyneq: x ≠ y := by intro hCxy; rw [hCxy] at hx20; omega
              have : x.1.val = y.1.val := by simp [hx02, hCy10]; omega
              have hxy1: x.1 = y.1 := by simp [this, Fin.ext_iff]
              have := monsterdiffrow m x y hx03 hCy11 hxy1
              contradiction
          · constructor
            · omega
            · omega
        have : S - 2 ≠ S - 1:= by have := S_bigger_1; omega
        simp [hyodd] at hCz
        simp [this] at hCz
        dsimp [path4left, path4leftfn] at hCz
        symm at hCz
        rw [ListFindSome3] at hCz
        obtain hCz1 | hCz2 := hCz
        · obtain ⟨r, hCz11, hCz12, _⟩ := hCz1
          dsimp [path4leftfn1, Restrict] at hCz11
          specialize hCy12 (Fin.castLE (by omega) r)
          apply hCy12
          · simp
            have : y.2.val = S - 1 - (q.val / 2 + 1) := by simp [hCy10]
            omega
          · rw [← hCz11]; exact hCz12
        · obtain ⟨_, hCz2⟩ := hCz2
          have : ¬ Odd (2 * y.1.val) := by simp [Odd]; intro x hx; omega
          obtain hCz2 | hCz2 := hCz2
          · obtain ⟨r, hCz21, hCz22, _⟩ := hCz2
            convert monsterdiffrow m y z hCy11 hCz22
            simp
            constructor
            · rw [hCy10, hCz21, path4leftfn2, righttoedgefn]
              simp
              dsimp [path3leftfn1]
              simp [this]
              rw [hCy10]
            · intro hCyz
              rw [hCy10, hCz21, path4leftfn2, righttoedgefn] at hCyz
              apply_fun (·.2.val) at hCyz
              simp at hCyz
              dsimp [path3leftfn1] at hCyz
              simp [this] at hCyz
              simp [hCy10] at hCyz
              omega
          · obtain ⟨_, r, hCz21, hCz22, _⟩ := hCz2
            convert monsterdiffcol m x z hx03 hCz22
            simp
            constructor
            · rw [hCz21, path4leftfn3, rightedgedownfn]
              simp [hx20, Fin.ext_iff]
            · intro hCxz
              rw [hCz21, path4leftfn3, rightedgedownfn] at hCxz
              apply_fun (·.1.val) at hCxz
              simp at hCxz
              dsimp [path3leftfn1] at hCxz
              simp [this] at hCxz
              simp [hCy10] at hCxz
              have : q.val / 2 ≥ 2 := by apply_fun (·.1.val) at hCy10; simp at hCy10; rw [hCy10] at hyodd; tauto
              omega
    · obtain ⟨_, i, hCy20, hCy21, _⟩ := hCy2
      rw [path3leftfn2] at hCy20
      rw [hCy20] at hCy21
      apply monsternotlastrow at hCy21
      · contradiction
      · simp

end PlayEndIn3

section PlayNotEndIn2

def rowatleast (i : ℕ) : Set Cell := {x : Cell | x.1.val ≥ i}

lemma pathhasrow (p : Path) (i : ℕ) (hiS : i ≤ S):
  letI Decidable := Classical.propDecidable
  (p.cells.find? (fun x ↦ (x ∈ rowatleast i : Bool))).isSome := by
  simp
  let x := p.cells.getLast p.nonempty
  have : x.1.val = S := by dsimp [x]; simp [p.last_last_row, Fin.last]
  use x.1, x.2
  have : x ∈ p.cells := by dsimp [x]; simp
  simp [this]
  dsimp [rowatleast]
  omega


lemma list_sep_last {T : Type*} (a : List T) (h : a ≠ []) : ∃ b x, a = b ++ [x] := by
  use a.dropLast, a.getLast h
  symm
  exact List.dropLast_append_getLast h

lemma adjbound1 (v x : Cell) (i : ℕ):  x.1.val ≥ i → x.1.val ≠ i → Adjacent v x → v.1.val ≥ i:= by dsimp [Adjacent, Nat.dist]; omega

lemma adjbound2 (v y : Cell) (a : Fin S):  y.1.val ≥ 2 → ¬(y.1.val = 2 ∧ a ≠ y.2) → Adjacent v y → ¬ v.1.val ≥ 2 → (v.1.val = 1 ∧ v.2.val = a) := by dsimp [Adjacent, Nat.dist]; omega

lemma firstmonster (s : Strategy) : ∃ (a : Fin S), ∀ (m : MonsterData), m rowoneindex = a → s.play m 1 0 = some (⟨1, valid_row_1⟩, a) := by
  let p := s Fin.elim0
  have := S_bigger_1
  have hS11: 1 ≤ S - 1 := by omega
  have hS10: 1 ≤ S := by omega

  letI Decidable := Classical.propDecidable
  have := pathhasrow p 1 hS10
  let x := Option.get (p.cells.find? (fun x ↦ (x ∈ rowatleast 1 : Bool))) this
  have : List.find? (fun x ↦ decide (x ∈ rowatleast 1)) p.cells = some x := by dsimp [x]; simp
  apply List.find?_eq_some_iff_append.mp at this
  obtain ⟨hxD, ps, qs, hxpq, hp⟩ := this
  simp at hxD
  have : x.1.val = 1 := by
    have : ps ≠ [] := by
      intro hps
      rw [hps] at hxpq
      simp at hxpq
      have := p.head_first_row
      simp [hxpq] at this
      dsimp [rowatleast] at hxD
      rw [this] at hxD
      contradiction
    obtain ⟨p1s, v, hps1⟩ := list_sep_last ps this
    rw [hps1] at hxpq
    simp at hxpq
    have := p.valid_move_seq
    rw [hxpq] at this
    simp at this
    obtain ⟨_, this, _⟩ := this
    by_contra hCx
    rw [rowatleast] at hxD; simp at hxD
    dsimp [Adjacent] at this
    have := adjbound1 v x 1 hxD hCx this
    have hvps : v ∈ ps := by simp [hps1]
    specialize hp v hvps
    simp at hp
    dsimp [rowatleast] at hp
    contradiction

  use x.2
  intro m hm
  dsimp [Strategy.play, Fin.snoc, Path.firstMonster]
  apply List.find?_eq_some_iff_append.mpr
  constructor
  · simp [MonsterData.monsterCells]
    use hS11
    exact hm
  · use ps, qs
    constructor
    · convert hxpq
      convert this.symm
    · intro z hz
      simp
      specialize hp z hz
      simp at hp
      intro hz
      apply monsternotfirstrow m at hz
      · contradiction
      · simp [rowatleast] at hp
        simp
        exact hp


lemma Fin2val (i : Fin 2) : i.val = 0 ∨ i.val = 1 := by omega

lemma notwinin2 (s : Strategy): ¬ s.ForcesWinIn 2 := by
  have := hS3
  intro h
  dsimp [Strategy.ForcesWinIn] at h
  dsimp [Strategy.WinsIn, Set.range] at h
  let ⟨a, ha⟩ := firstmonster s
  let x : Cell := (⟨1, valid_row_1⟩, a)
  let M1 (i : Fin 1) : Option Cell := some (⟨1, valid_row_1⟩, a)
  have hM1play (m : MonsterData) (hma : m rowoneindex = a): M1 = s.play m 1 := by
    ext i
    have : i = 0 := by omega
    rw [this, ha]
    exact hma
  let p2 := s M1
  by_cases hx : x ∈ p2.cells
  · let ⟨m, hm1, hm2⟩ := monsterpossible1 a hS3
    specialize h m
    specialize ha m hm2
    obtain ⟨i, hi⟩ := h
    have h210 := splaysucc1 s m 1 0
    simp at h210
    obtain y0 | y1 := Fin2val i
    · simp at y0
      rw [y0] at hi
      rw [hi, ha] at h210
      contradiction
    · have : 1 = (1 : Fin 2).val := by simp
      rw [this] at y1
      apply Fin.eq_of_val_eq at y1
      rw [y1, Strategy.play] at hi
      rw [← hM1play m hm2] at hi
      simp [Fin.snoc] at hi
      replace hi : p2.firstMonster m = none := by dsimp [p2]; exact hi
      rw [Path.firstMonster] at hi
      apply List.find?_eq_none.mp at hi
      specialize hi x hx
      simp at hi
      contradiction
  · have : 2 ≤ S := by omega
    have := pathhasrow p2 2 this
    letI Decidable := Classical.propDecidable
    let y := Option.get (p2.cells.find? (fun x ↦ (x ∈ rowatleast 2 : Bool))) this
    have : List.find? (fun x ↦ decide (x ∈ rowatleast 2)) p2.cells = some y := by dsimp [y]; simp
    have hymon := List.mem_of_find?_eq_some this

    apply List.find?_eq_some_iff_append.mp at this
    obtain ⟨hyD, ps, qs, hypq, hp⟩ := this
    simp at hyD
    have hyval: y.1.val = 2 ∧ a ≠ y.2 := by
      have : ps ≠ [] := by
        intro hps
        rw [hps] at hypq
        simp at hypq
        have := p2.head_first_row
        simp [hypq] at this
        dsimp [rowatleast] at hyD
        rw [this] at hyD
        contradiction
      obtain ⟨p1s, v, hps1⟩ := list_sep_last ps this
      rw [hps1] at hypq
      simp at hypq
      have := p2.valid_move_seq
      rw [hypq] at this
      simp at this
      obtain ⟨_, this, _⟩ := this
      by_contra hCy
      rw [rowatleast] at hyD; simp at hyD
      dsimp [Adjacent] at this
      have hvps : v ∈ ps := by simp [hps1]
      specialize hp v hvps
      simp at hp
      dsimp [rowatleast] at hp
      have := adjbound2 v y a hyD hCy this hp
      have hvcell : v ∈ p2.cells := by simp [hypq]
      have : v = x := by ext <;> simp [this, x]
      rw [this] at hvcell
      contradiction

    have : a ≠ y.2 := by tauto

    have ⟨m, hm1, hm2, hm3⟩ := monsterpossible2 a y.2 hS3 this
    specialize ha m hm3
    specialize hM1play m hm3
    specialize h m
    obtain ⟨i, hi⟩ := h
    have h210 := splaysucc1 s m 1 0
    simp at h210
    obtain y0 | y1 := Fin2val i
    · simp at y0
      rw [y0] at hi
      rw [hi, ha] at h210
      contradiction
    · have : 1 = (1 : Fin 2).val := by simp
      rw [this] at y1
      apply Fin.eq_of_val_eq at y1
      rw [y1, Strategy.play] at hi
      rw [← hM1play] at hi
      simp [Fin.snoc] at hi
      replace hi : p2.firstMonster m = none := by dsimp [p2]; exact hi
      rw [Path.firstMonster] at hi
      apply List.find?_eq_none.mp at hi
      specialize hi y hymon
      simp at hi
      have : y = (⟨2, valid_row_2⟩, y.2) := by
        ext
        · simp; tauto
        · simp
      rw [this] at hi
      contradiction


lemma winsucc (s : Strategy) (k : ℕ) : s.ForcesWinIn k → s.ForcesWinIn (k + 1) := by
  intro h
  dsimp [Strategy.ForcesWinIn] at *
  intro m
  specialize h m
  dsimp [Strategy.WinsIn, Set.range] at *
  obtain ⟨i, hi⟩ := h
  use i
  dsimp [Strategy.play]
  simp [hi]

lemma notwinin1 (s : Strategy): ¬ s.ForcesWinIn 1 := by
  intro h; exact notwinin2 s (winsucc s 1 h)

lemma notwinin0 (s : Strategy): ¬ s.ForcesWinIn 0 := by
  intro h; exact notwinin1 s (winsucc s 0 h)

end PlayNotEndIn2

def answer : ℕ := 3

theorem result : IsLeast {n | ∃ s : Strategy, s.ForcesWinIn n} answer := by
  rw [answer]
  constructor
  · simp; use s0; exact s0winsin3
  · dsimp [lowerBounds]
    intro L ⟨s, hsL⟩
    have := notwinin0 s
    have := notwinin1 s
    have := notwinin2 s
    have : L ≠ 0 := by by_contra hL; rw [hL] at hsL; contradiction
    have : L ≠ 1 := by by_contra hL; rw [hL] at hsL; contradiction
    have : L ≠ 2 := by by_contra hL; rw [hL] at hsL; contradiction
    omega


end IMO2024P5
