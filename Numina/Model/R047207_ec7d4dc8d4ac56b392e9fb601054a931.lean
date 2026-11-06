import Mathlib

theorem number_theory_158450 :
  ∃ c x y z n, Nat.digits 10 n = [z, y, x] ∧ 2 * n = Nat.ofDigits c [z, y, x]  := by 
  use 15
  use 1, 5, 0, 150
  constructor
  · norm_num
  · native_decide