import Mathlib

theorem algebra_116 : √(50 * 51 * 52 * 53 + 1) = 2651 := by
  have h1 : (50 * 51 * 52 * 53 + 1 : ℝ) = (2651 : ℝ) ^ 2 := by norm_num
  rw [h1]
  exact Real.sqrt_sq (by norm_num)