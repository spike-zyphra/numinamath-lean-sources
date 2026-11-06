import Mathlib

def f (x : ℕ) := 3 * x + 2
theorem number_theory_243316 :
    ∃ m, 0 < m ∧ 2005 ∣ f^[100] m := by 
  use 380
  constructor 
  · norm_num 
  · native_decide