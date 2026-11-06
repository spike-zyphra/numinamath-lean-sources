import Mathlib

theorem algebra_18779 : Real.sqrt 242 = 11 * Real.sqrt 2 := by
  calc 
    Real.sqrt 242 = Real.sqrt (11 ^ 2 * (2 : ℝ)) := by 
      norm_num
    _ = (Real.sqrt (11 ^ 2)) * (Real.sqrt (2 : ℝ)) := by 
      rw [Real.sqrt_mul (by norm_num)]
    _ = (11 : ℝ) * (Real.sqrt (2 : ℝ)) := by 
      rw [Real.sqrt_sq (by norm_num)]
    _ = 11 * Real.sqrt 2 := by 
      ring