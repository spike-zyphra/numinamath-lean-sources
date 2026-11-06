import Mathlib

theorem algebra_18737 : Real.sqrt ((-8)^2 + 6^2) = 10 := by
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> linarith