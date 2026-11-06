import Mathlib

def other_4662_solution : ℕ := 2929

theorem number_theory_4662 : ∃ n, 1 < n ∧ n ∣ (3 ^ n - 2) := by 
  use 2929
  constructor
  · norm_num
  · native_decide