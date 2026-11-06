import Mathlib

theorem algebra_325692 : (7 + 4 * Real.sqrt 3) ^ ((1 : ℝ) / 2) - (7 - 4 * Real.sqrt 3) ^ ((1 : ℝ) / 2) = 2 * Real.sqrt 3 := by
  have h1 : (7 + 4 * Real.sqrt 3 : ℝ) = (2 + Real.sqrt 3) ^ 2 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h2 : (7 - 4 * Real.sqrt 3 : ℝ) = (2 - Real.sqrt 3) ^ 2 := by 
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h3 : (7 + 4 * Real.sqrt 3 : ℝ) ^ ((1 : ℝ) / 2) = (2 + Real.sqrt 3) := by 
    have h4 : (7 + 4 * Real.sqrt 3 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (7 + 4 * Real.sqrt 3) := by 
      rw [← Real.sqrt_eq_rpow]
    rw [h4]
    rw [h1]
    have h5 : Real.sqrt ((2 + Real.sqrt 3) ^ 2) = (2 + Real.sqrt 3 : ℝ) := by 
      rw [Real.sqrt_sq (by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      )]
    exact h5
  have h6 : (7 - 4 * Real.sqrt 3 : ℝ) ^ ((1 : ℝ) / 2) = (2 - Real.sqrt 3) := by
    have h7 : (7 - 4 * Real.sqrt 3 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (7 - 4 * Real.sqrt 3) := by 
      rw [← Real.sqrt_eq_rpow]
    rw [h7]
    rw [h2]
    have h8 : Real.sqrt ((2 - Real.sqrt 3) ^ 2) = (2 - Real.sqrt 3 : ℝ) := by
      have h9 : 2 - Real.sqrt 3 ≥ 0 := by
        have h10 : Real.sqrt 3 ≤ (2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - 2)]
        nlinarith
      rw [Real.sqrt_sq (h9)]
    exact h8
  rw [h3, h6]
  all_goals nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]