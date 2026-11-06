import Mathlib

theorem inequalities_150558 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a > 0.7 ∨ b^2 > 0.7 ∨ 1 / (a^2 + b) > 0.7 := by
  by_contra h
  push_neg at h
  have h1 : a ≤ (0.7 : ℝ) := by
    linarith
  have h2 : b ^ 2 ≤ (0.7 : ℝ) := by
    linarith
  have h3 : 1 / (a^2 + b) ≤ (0.7 : ℝ) := by
    linarith
  have h4 : 0 < a^2 + b := by
    nlinarith
  have h5 : 1 ≤ (0.7 : ℝ) * (a^2 + b) := by
    have h6 : 1 / (a^2 + b) ≤ (0.7 : ℝ) := by
      linarith
    have h7 : (1 / (a^2 + b) : ℝ) * (a^2 + b) ≤ (0.7 * (a^2 + b) : ℝ) := by
      nlinarith
    have h8 : (1 / (a^2 + b) : ℝ) * (a^2 + b) = 1 := by
      field_simp
      all_goals nlinarith
    nlinarith
  have h6 : a ^ 2 ≤ (0.49 : ℝ) := by
    nlinarith [h1, show (0.7 : ℝ) ^ 2 = 0.49 by norm_num]
  nlinarith [sq_nonneg (a - (0.7 : ℝ)), sq_nonneg (b ^ 2 - 0.7), sq_nonneg (b - Real.sqrt 0.7), Real.sqrt_pos.mpr (by norm_num : (0.7 : ℝ) > 0), Real.sq_sqrt (show (0.7 : ℝ) ≥ 0 by norm_num), sq_nonneg (a ^ 2 + b - (0.7 : ℝ) * b), sq_nonneg (b ^ 2 - 0.7), Real.sqrt_pos.mpr (by norm_num : (0.7 : ℝ) > 0), Real.sqrt_nonneg (0.7 : ℝ), h1, h2, Real.sqrt_nonneg (0.7 : ℝ)]