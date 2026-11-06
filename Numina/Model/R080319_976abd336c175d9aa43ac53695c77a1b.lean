import Mathlib

def f (n : ℕ) := n ^ 2

theorem number_theory_174568 : f 6 = 36 := by 
  unfold f 
  all_goals norm_num