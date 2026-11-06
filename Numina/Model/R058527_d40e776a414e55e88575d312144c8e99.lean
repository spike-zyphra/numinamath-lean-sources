import Mathlib

theorem number_theory_11521 : (Nat.digits 9 2014).length = 4 ∧ (Nat.digits 9 2014) = [7, 7, 6, 2] := by
  constructor
  · norm_num
  · norm_num