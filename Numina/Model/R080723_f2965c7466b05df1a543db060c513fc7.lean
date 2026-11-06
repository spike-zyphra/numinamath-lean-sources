import Mathlib

theorem algebra_21559 : Real.sqrt (3 * 6 * 10 * 15 * 21 * 28) = 1260 := by
  have h1 : (3 * 6 * 10 * 15 * 21 * 28 : ℝ) = (1260 : ℝ) ^ 2 := by norm_num
  rw [h1]
  rw [Real.sqrt_sq]
  all_goals norm_num