import Mathlib

theorem algebra_198329 : Real.sqrt (abs (12 * Real.sqrt 5 - 29)) - Real.sqrt (12 * Real.sqrt 5 + 29) = -6 := by
  have h1 : 12 * Real.sqrt 5 < (29 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (4 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 4, Real.sq_sqrt (show (0 : ℝ) ≤ (4 : ℝ) by norm_num), Real.sqrt_nonneg 1, Real.sqrt_nonneg (4 : ℝ), Real.sqrt_nonneg (4 : ℝ)]
  have h2 : abs (12 * Real.sqrt 5 - 29) = 29 - 12 * Real.sqrt 5 := by
    rw [abs_of_neg]
    linarith
    all_goals nlinarith
  have h3 : Real.sqrt (abs (12 * Real.sqrt 5 - 29)) = 2 * Real.sqrt 5 - 3 := by
    rw [h2]
    have h4 : (2 * Real.sqrt 5 - 3 : ℝ) ^ 2 = (29 - 12 * Real.sqrt 5 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 3/2)]
    have h5 : (2 * Real.sqrt 5 - 3 : ℝ) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 1, sq_nonneg (Real.sqrt 5 - 3/2), Real.sqrt_nonneg 5]
    have h6 : Real.sqrt (29 - 12 * Real.sqrt 5) = (2 * Real.sqrt 5 - 3 : ℝ) := by
      rw [← h4]
      field_simp [Real.sqrt_sq, h5]
    linarith [h6]
  have h7 : Real.sqrt (12 * Real.sqrt 5 + 29) = 3 + 2 * Real.sqrt 5 := by
    have h8 : (3 + 2 * Real.sqrt 5) ^ 2 = 12 * Real.sqrt 5 + 29 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 3/2)]
    have h9 : 0 ≤ (3 + 2 * Real.sqrt 5 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 1]
    have h10 : Real.sqrt (12 * Real.sqrt 5 + 29) = (3 + 2 * Real.sqrt 5 : ℝ) := by
      rw [← h8]
      field_simp [Real.sqrt_sq, h9]
    linarith [h10]
  rw [h3, h7]
  nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 1, Real.sqrt_nonneg (4 : ℝ), sq_nonneg (Real.sqrt 5 - 3/2), sq_nonneg (2 * Real.sqrt 5 - 3/2)]
  all_goals nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 1, Real.sqrt_nonneg (4 : ℝ), sq_nonneg (Real.sqrt 5 - 3/2), sq_nonneg (2 * Real.sqrt 5 - 3/2)]