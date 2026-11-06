import Mathlib

theorem algebra_192525 : √(abs (40 * √2 - 57)) - √(40 * √2 + 57) = -10 := by

  have h1 : (40 * Real.sqrt 2 : ℝ) < (57 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]
  have h3 : abs (40 * Real.sqrt 2 - 57) = (57 - 40 * Real.sqrt 2 : ℝ) := by
    rw [abs_of_neg]
    linarith
    all_goals linarith
  have h4 : √(abs (40 * √2 - 57)) = (4 * √2 - 5 : ℝ) := by
    rw [h3]
    have h5 : (4 * Real.sqrt 2 - 5 : ℝ) ^ 2 = (57 - 40 * Real.sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]
    have h6 : (4 * Real.sqrt 2 - 5 : ℝ) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
    rw [←h5]
    field_simp [Real.sqrt_sq (show (4 * Real.sqrt 2 - 5 : ℝ) ≥ 0 by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)])]
    all_goals linarith
  have h7 : √(40 * √2 + 57) = (4 * √2 + 5 : ℝ) := by
    have h8 : (4 * Real.sqrt 2 + 5 : ℝ) ^ 2 = (40 * Real.sqrt 2 + 57 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]
    have h9 : (4 * Real.sqrt 2 + 5 : ℝ) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [←h8]
    field_simp [Real.sqrt_sq (show (4 * Real.sqrt 2 + 5 : ℝ) ≥ 0 by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])]
    all_goals linarith
  rw [h4, h7]
  nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]