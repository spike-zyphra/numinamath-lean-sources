import Mathlib

theorem number_theory_260926 : ∃ n, n > 0 ∧ (7 * 10 ^ (Nat.digits 10 n).length + n) % 7 = 0 := by 
  use 7
  constructor
  · norm_num 
  · norm_num