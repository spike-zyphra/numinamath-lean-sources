import Mathlib

theorem algebra_17044 : Real.sqrt (7 * 2) * Real.sqrt (2^3 * 7^3) = 196 := by
  have h1 : Real.sqrt (7 * 2) * Real.sqrt (2^3 * 7^3) = Real.sqrt ((7 * 2) * (2^3 * 7^3)) := by
    rw [← Real.sqrt_mul (by norm_num)]
  rw [h1]
  have h2 : (7 * 2 : ℝ) * (2^3 * 7^3) = (196 : ℝ) ^ 2 := by
    norm_num
  rw [h2]
  rw [Real.sqrt_sq (by norm_num)]