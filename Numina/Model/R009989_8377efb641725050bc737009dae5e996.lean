import Mathlib

def letter_value (c : Char) : ℤ := match (c.toNat - 'a'.toNat : ℤ) % 8 with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => -1
  | 5 => -2
  | 6 => -1
  | 7 => 0
  | _ => 0

theorem number_theory_12927 (str : List Char) (hStr: str = ['n', 'u', 'm', 'e', 'r', 'i', 'c']) :
    ∑ (i : Fin str.length), letter_value (str.get i) = -1 := by 
  rw [hStr]
  simp [Finset.sum_insert, Finset.sum_singleton, letter_value, List.get]
  <;> rfl