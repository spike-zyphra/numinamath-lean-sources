import Mathlib

theorem number_theory_191673 :
    ∃ n, 7 ∣ (Nat.digits 10 n).sum ∧ 7 ∣ (Nat.digits 10 (n + 1)).sum := by 
  use 69999
  constructor
  · -- Verify that 7 divides the digit sum of 69999
    norm_num
  · -- Verify that 7 divides the digit sum of 70000
    norm_num