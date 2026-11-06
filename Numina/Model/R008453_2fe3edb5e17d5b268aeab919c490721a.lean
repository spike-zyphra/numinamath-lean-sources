import Mathlib

def dig_change : ℕ → ℕ 
| 0 => 0
| 1 => 1
| 2 => 3
| 3 => 4
| 4 => 5
| 5 => 6
| 6 => 7
| 7 => 8
| 8 => 9
| (n + 1) => 0

 
theorem number_theory_608445 : List.map dig_change (Nat.digits 9 2008) = [1, 8, 7 ,3] := by
  simp [Nat.digits, Nat.digitsAux, List.map, dig_change]
  <;> norm_num
  <;> rfl