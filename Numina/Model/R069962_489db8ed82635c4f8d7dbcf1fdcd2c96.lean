import Mathlib

theorem number_theory_270428 : ∃ x, 1108 % x = 1453 % x ∧ 1453 % x = 1844 % x ∧ 1844 % x = 2281 % x := by 
  use 23
  repeat { constructor }
  all_goals norm_num