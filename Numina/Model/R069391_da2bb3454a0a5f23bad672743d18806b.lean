import Mathlib

theorem number_theory_2172 : (0b1001 : ℕ) * (Nat.ofDigits 3 [1, 2, 1]) = 144 := by
  norm_num [Nat.ofDigits]