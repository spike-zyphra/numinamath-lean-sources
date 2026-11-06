import Mathlib

theorem algebra_185031 : (Real.sqrt 2 - 1) / (Real.sqrt 2 + 1) = (10 - 7 * Real.sqrt 2) ^ ((1 : ℝ) / 3) / (10 + 7 * Real.sqrt 2) ^ ((1 : ℝ) / 3) := by
  have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  have h2 : (Real.sqrt 2 + 1 : ℝ) ≠ 0 := by
    have h3 : Real.sqrt 2 > 0 := by positivity
    nlinarith
  have h3 : (Real.sqrt 2 - 1) / (Real.sqrt 2 + 1) = 3 - 2 * Real.sqrt 2 := by
    field_simp [h1, h2]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h4 : (10 - 7 * Real.sqrt 2) ^ ((1 : ℝ) / 3) / (10 + 7 * Real.sqrt 2) ^ ((1 : ℝ) / 3) = 3 - 2 * Real.sqrt 2 := by
    have h5 : (10 - 7 * Real.sqrt 2) / (10 + 7 * Real.sqrt 2) = (3 - 2 * Real.sqrt 2) ^ 3 := by
      have h12 : (10 + 7 * Real.sqrt 2) ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      field_simp [h12, show Real.sqrt 2 ^ 2 = 2 by exact h1]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - 3 / 2)]
    have h7 : (10 - 7 * Real.sqrt 2) ^ ((1: ℝ) / 3) / (10 + 7 * Real.sqrt 2) ^ ((1: ℝ) / 3) = ((10 - 7 * Real.sqrt 2) / (10 + 7 * Real.sqrt 2)) ^ ((1: ℝ) / 3) := by 
      rw [← Real.div_rpow]
      all_goals
        have h3 : 0 < (10 + 7 * Real.sqrt 2 : ℝ) := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h4 : 0 ≤ (10 - 7 * Real.sqrt 2 : ℝ) := by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        all_goals
          try linarith
    rw [h7, h5]
    have h13 : ((3 - 2 * Real.sqrt 2) ^ 3) ^ ((1 : ℝ) / 3) = (3 - 2 * Real.sqrt 2) := by
      have h14 : ((3 - 2 * Real.sqrt 2) ^ 3) ^ ((1 : ℝ) / 3) = (3 - 2 * Real.sqrt 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          have h15 : (3 - 2 * Real.sqrt 2 : ℝ) ≥ 0 := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          linarith
      exact h14
    linarith
  linarith [h3, h4]