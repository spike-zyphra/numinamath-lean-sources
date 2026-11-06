import Mathlib

theorem algebra_9011 : (2.3 : ℝ)^(2.3 : ℝ) < (2.3 : ℝ)^(3.2 : ℝ) := by
  apply Real.rpow_lt_rpow_of_exponent_lt 
  all_goals norm_num -- proves both goals: 2.3 > 1 and 2.3 < 3.2