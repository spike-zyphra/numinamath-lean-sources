import Mathlib

theorem number_theory_3848 : ∃ k, (3^k) % 1000000 = 81 := by 
  use 4
  all_goals norm_num