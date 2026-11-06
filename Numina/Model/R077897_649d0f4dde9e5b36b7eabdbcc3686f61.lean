import Mathlib

theorem algebra_3172 : |(|(|(2-3)|-5)|-7)|-11 = -8 := by 
  norm_num [abs_of_nonneg, abs_of_nonpos]