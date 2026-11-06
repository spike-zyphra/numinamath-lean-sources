import Mathlib

theorem algebra_2636 : Real.sqrt ((1998 * 1999 * 2000 * 2001 + 1) / 4 : ℝ) = 1998999.5 := by
  have h1 : (1998 * 1999 * 2000 * 2001 + 1 : ℝ) / 4 = (1998999.5 : ℝ) ^ 2 := by norm_num
  rw [h1]
  rw [Real.sqrt_sq]
  all_goals norm_num