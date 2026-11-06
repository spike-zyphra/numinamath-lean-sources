import Mathlib

theorem algebra_280290 : (Real.sqrt 2 - 1) * (17 + 12 * Real.sqrt 2) ^ ((1 : ℝ) / 4) = 1 := by
  have h1 : 0 ≤ (17 + 12 * Real.sqrt 2 : ℝ) := by 
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h2 : (17 + 12 * Real.sqrt 2 : ℝ) = (Real.sqrt 2 + 1) ^ 4 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
            sq_nonneg (Real.sqrt 2 ^ 2 - 2), sq_nonneg ((Real.sqrt 2 + 1) ^ 2 - (3 + 2 * Real.sqrt 2))]
  have h3 : ((17 + 12 * Real.sqrt 2) : ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt 2 + 1 := by
    have h4 : ((17 + 12 * Real.sqrt 2) : ℝ) = (Real.sqrt 2 + 1) ^ 4 := h2
    rw [h4]
    have h5 : 0 ≤ (Real.sqrt 2 + 1 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2]
    have h6 : ((Real.sqrt 2 + 1 : ℝ) ^ 4) ^ ((1 : ℝ) / 4) = (Real.sqrt 2 + 1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    exact h6
  rw [h3]
  have h7 : (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) = 1 := by 
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  linarith [h7]