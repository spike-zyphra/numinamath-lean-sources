import Mathlib

theorem algebra_16017 : √288 = 12 * √2 := by
  calc 
    √288 = √(12^2 * 2) := by norm_num 
    _ = √(12^2) * √2 := by rw [Real.sqrt_mul (by norm_num)]
    _ = (12 : ℝ) * √2 := by rw [Real.sqrt_sq (by norm_num)]
    _ = 12 * √2 := by ring