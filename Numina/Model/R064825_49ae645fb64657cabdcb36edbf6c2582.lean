import Mathlib

theorem algebra_98435 : Real.sqrt ((3 - 2 * Real.sqrt 3)^2) + Real.sqrt ((3 + 2 * Real.sqrt 3)^2) = 4 * Real.sqrt 3 := by
  have h1 : Real.sqrt ((3 - 2 * Real.sqrt 3) ^ 2) = |3 - 2 * Real.sqrt 3| := by
    rw [Real.sqrt_sq_eq_abs]
  have h2 : Real.sqrt ((3 + 2 * Real.sqrt 3) ^ 2) = |3 + 2 * Real.sqrt 3| := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h1, h2]
  
  have h3 : 3 - 2 * Real.sqrt 3 < 0 := by
    have h6 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_pos_of_pos (Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)), sq_nonneg (Real.sqrt 3 - 3 / 2)]
  
  have h6 : 3 + 2 * Real.sqrt 3 ≥ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (3 : ℝ) ≥ 0)]
  
  rw [abs_of_neg h3, abs_of_nonneg h6]
  ring