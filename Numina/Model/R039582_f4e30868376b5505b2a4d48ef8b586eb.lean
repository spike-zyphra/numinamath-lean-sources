import Mathlib

open Real

theorem geometry_98147 (x : ℝ) (hx : x = (1 - 1 / sqrt 2)) : 
  8 * (x^3 / 6) = (10 - 7 * sqrt 2) / 3 := by
  have h1 : x = (1 - 1 / sqrt 2) := hx
  rw [h1]
  have h2 : (sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h3 : (sqrt 2) ^ 3 = 2 * sqrt 2 := by 
    calc 
      (sqrt 2) ^ 3 = (sqrt 2) * (sqrt 2) ^ 2 := by ring
      _ = (sqrt 2) * (2 : ℝ) := by rw [h2]
      _ = 2 * sqrt 2 := by ring
  field_simp [h2, h3]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 2 - 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]