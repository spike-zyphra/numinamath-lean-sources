import Mathlib

theorem number_theory_105686 : ∃ n, n > 0 ∧ (Nat.digits 10 n).length = 3 ∧
    (Nat.digits 10 n).headI = 4 := by 
  use 124
  constructor
  · norm_num 
  constructor 
  · norm_num 
  · norm_num