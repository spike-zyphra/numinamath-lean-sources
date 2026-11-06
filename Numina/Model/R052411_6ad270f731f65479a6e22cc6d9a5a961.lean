import Mathlib

theorem number_theory_12569 : (Nat.ofDigits 2 [1, 0, 0, 1]) * (Nat.ofDigits 3 [1, 2, 1]) = 144 := by 
  norm_num [Nat.ofDigits]