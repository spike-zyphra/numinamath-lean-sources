import Mathlib
/- Compute $\sqrt{2022^{2}-12^{6}}$. -/
theorem algebra_610493 : √(2022 ^ 2 - 12 ^ 6) = 1050:= by
  -- First, compute the square of 1050
  norm_num
  -- Then, compute the square of 2022
  rw [show (1102500 : ℝ) = 1050 ^ 2 by ring]
  -- Now, compute the difference
  field_simp
