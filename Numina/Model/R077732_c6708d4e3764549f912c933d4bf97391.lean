import Mathlib

theorem algebra_301070 (x : ℝ) (hx : x = 2 * Real.sqrt 2 + 1) :
    (x^2 - 2 * x - 9) / (x^3 - 11 * x - 15) = 2 := by
  have h1 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 2 : ℝ) ^ 3 = Real.sqrt 2 * (2 : ℝ) := by
    calc
      (Real.sqrt 2 : ℝ) ^ 3 = (Real.sqrt 2 : ℝ) ^ 2 * (Real.sqrt 2 : ℝ) := by ring
      _ = (Real.sqrt 2 : ℝ) * (2 : ℝ) := by rw [h1]; all_goals ring
      _ = _ := by ring
  have eq1 : x ^ 2 - 2 * x - 9 = -2 := by
    rw [hx]
    nlinarith [h1, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), sq_nonneg (Real.sqrt 2 - 1)]
  have eq2 : x ^ 3 - 11 * x - 15 = -1 := by
    rw [hx]
    nlinarith [h1, h2, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), sq_nonneg (2 * Real.sqrt 2), sq_nonneg (2 * Real.sqrt 2 + 1), sq_nonneg (Real.sqrt 2 * 2 - 2 * (Real.sqrt 2 : ℝ) + 1)]
  rw [eq1, eq2]
  norm_num