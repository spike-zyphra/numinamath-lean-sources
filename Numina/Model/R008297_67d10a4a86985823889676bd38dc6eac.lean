import Mathlib

theorem inequalities_45712 : (2010 / 2009 : ℝ)^2009 > 2 := by
  norm_num [pow_succ, mul_add, add_mul]