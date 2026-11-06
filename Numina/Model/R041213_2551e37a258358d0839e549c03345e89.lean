import Mathlib

theorem algebra_323946 {m n a : ℝ} (hm : m = 1 + Real.sqrt 2) (hn : n = 1 - Real.sqrt 2)
    (h : (7 * m^2 - 14 * m + a) * (3 * n^2 - 6 * n - 7) = 8) : a = -9 := by
  have eq1 : 7 * m^2 - 14 * m + a = 7 + a := by
    rw [hm]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), 
            mul_self_nonneg (Real.sqrt 2 : ℝ)]
  have eq2 : 3 * n^2 - 6 * n - 7 = -4 := by
    rw [hn]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), 
            mul_self_nonneg (Real.sqrt 2 : ℝ)]
  rw [eq1, eq2] at h
  linarith