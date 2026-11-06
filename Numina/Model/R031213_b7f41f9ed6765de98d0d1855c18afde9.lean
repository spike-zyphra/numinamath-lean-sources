import Mathlib

theorem algebra_52475 : Real.sqrt ((31 * 30 * 29 * 28 + 1)) = 869 := by
  have h1 : (31 * 30 * 29 * 28 + 1 : ℝ) = (869 : ℝ) ^ 2 := by
    norm_num
  rw [h1]
  exact Real.sqrt_sq (by norm_num)