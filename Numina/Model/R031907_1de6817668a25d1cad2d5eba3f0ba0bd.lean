import Mathlib

theorem algebra_20300 : Real.sqrt 2940 = 14 * Real.sqrt 15 := by
  calc
    Real.sqrt 2940 = Real.sqrt (14^2 * (15 : ℝ)) := by
      norm_num
    _ = (Real.sqrt (14^2 : ℝ)) * Real.sqrt 15 := by
      rw [Real.sqrt_mul (by norm_num)]
    _ = (14 : ℝ) * Real.sqrt 15 := by
      rw [Real.sqrt_sq (by norm_num)]
    _ = 14 * Real.sqrt 15 := by
      ring