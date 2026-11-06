import Mathlib

theorem algebra_136138 : Real.sqrt (0.04 ^ 3) = 1 / 125 := by 
  rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num