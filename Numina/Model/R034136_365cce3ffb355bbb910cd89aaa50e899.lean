import Mathlib

theorem algebra_268972 : √2011 < 2011 ∧ 2011 < 2011^2 := by
  constructor
  · -- Show that √2011 < 2011
    rw [Real.sqrt_lt] 
    all_goals
    norm_num
  · -- Show that 2011 < 2011^2
    norm_num