import Mathlib

theorem number_theory_259297 :
    ∃ a b, a * b = 111111 ∧ a % 10 ≠ 1 ∧ b % 10 ≠ 1 := by 
  use 7, 15873 
  constructor 
  · norm_num
  constructor
  · norm_num 
  · norm_num