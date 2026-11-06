import Mathlib

theorem number_theory_223222 :
    ∃ n, (Nat.digits 10 n).sum = 8 ∧ 8 ∣ n + 1 := by
  use 71
  constructor
  · norm_num
  · norm_num