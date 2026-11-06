import Mathlib

theorem number_theory_70103 : ∃ n, 1 ≤ n ∧ 2014 ∣ Nat.fib n := by 
  use 54
  constructor
  · norm_num
  · native_decide