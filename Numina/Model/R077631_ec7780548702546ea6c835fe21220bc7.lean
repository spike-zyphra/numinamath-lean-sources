import Mathlib

open Real

theorem algebra_2415 : sqrt (3 - 2 * sqrt 2) = sqrt 2 - 1 := by
  have h1 : 0 ≤ Real.sqrt 2 - 1 := by
    have h2 : 1 < Real.sqrt 2 := by
      rw [Real.lt_sqrt] <;> norm_num
    linarith
  have h2 : (sqrt 2 - 1) ^ 2 = 3 - 2 * sqrt 2 := by
    calc
      (sqrt 2 - 1) ^ 2 = (sqrt 2) ^ 2 - 2 * sqrt 2 + 1 := by ring
      _ = 2 - 2 * sqrt 2 + 1 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      _ = 3 - 2 * sqrt 2 := by ring
  have h3 : 3 - 2 * sqrt 2 ≥ 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  rw [←h2]
  rw [Real.sqrt_sq (by linarith [h1])]
  all_goals linarith [Real.sqrt_nonneg 2]