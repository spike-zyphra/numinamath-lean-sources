import Mathlib
theorem algebra_610493 : √(2022 ^ 2 - 12 ^ 6) = 1050:= by
  have h1 : (2022 ^ 2 - 12 ^ 6 : ℝ) = (1050 : ℝ) ^ 2 := by 
    norm_num
  rw [h1]
  rw [Real.sqrt_sq (by norm_num)]