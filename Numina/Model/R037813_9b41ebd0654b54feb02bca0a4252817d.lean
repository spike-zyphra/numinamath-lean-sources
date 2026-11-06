import Mathlib

theorem number_theory_187786 :
    ∃ n, (Nat.digits 10 n).sum = 8 ∧ 8 ∣ (n + 1) := by
  use 71
  constructor
  · -- The sum of digits of 71 is 8
    norm_num
  · -- 8 divides 72
    norm_num