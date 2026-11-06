import Mathlib

theorem algebra_20708 : Real.sqrt 720 = 12 * Real.sqrt 5 := by
  calc
    Real.sqrt 720 = Real.sqrt (12^2 * 5) := by norm_num
    _ = Real.sqrt (12^2) * Real.sqrt 5 := by rw [Real.sqrt_mul (by norm_num)]
    _ = (12 : ℝ) * Real.sqrt 5 := by rw [Real.sqrt_sq (by norm_num)]
    _ = 12 * Real.sqrt 5 := by ring