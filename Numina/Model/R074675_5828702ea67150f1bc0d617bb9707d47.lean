import Mathlib

open Real

theorem algebra_313056 : (sqrt 5 + 3 * sqrt 3 + 4 * sqrt 2) / ((sqrt 5 + sqrt 2) * (sqrt 2 + sqrt 3)) = sqrt 3 + sqrt 5 - 2 * sqrt 2 := by
  have h1 : (sqrt 5 + sqrt 2) * (sqrt 2 + sqrt 3) ≠ 0 := by
    apply mul_ne_zero
    · -- Show that $\sqrt{5} + \sqrt{2} \neq 0$.
      have h5 : sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
      have h2 : sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
      have h6 : sqrt 5 + sqrt 2 > 0 := by linarith
      linarith
    · -- Show that $\sqrt{2} + \sqrt{3} \neq 0$.
      have h2 : sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
      have h3 : sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
      have h6 : sqrt 2 + sqrt 3 > 0 := by linarith
      linarith
  field_simp [h1]
  have h5_pos : sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have h3_pos : sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have h2_pos : sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have h6 : sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show 0 ≤ 2 by norm_num)
  have h7 : sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (show 0 ≤ 3 by norm_num)
  have h8 : sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (show 0 ≤ 5 by norm_num)
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num)) (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)), mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)) (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)), mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num)) (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 5, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, sq (sqrt 5 - sqrt 2 - sqrt 3), sq (sqrt 5 * sqrt 2 - 1 * sqrt 3), sq (sqrt 5 * sqrt 3 - 2 * sqrt 2), sq (sqrt 3 * sqrt 2 - 1 * sqrt 5)]