import Mathlib

theorem algebra_15496 : Real.sqrt 245 = 7 * Real.sqrt 5 := by
  calc
    Real.sqrt 245 = Real.sqrt (5 * (7: ℝ) ^ 2) := by
      norm_num
    _ = Real.sqrt (5 : ℝ) * Real.sqrt ((7: ℝ) ^ 2) := by
      rw [Real.sqrt_mul (by norm_num)]
    _ = Real.sqrt (5 : ℝ) * (7: ℝ) := by
      simp [Real.sqrt_sq (show (7 : ℝ) ≥ 0 by norm_num)]
    _ = 7 * Real.sqrt 5 := by
      ring