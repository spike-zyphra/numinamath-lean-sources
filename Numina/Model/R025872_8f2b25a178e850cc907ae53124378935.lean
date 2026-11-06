import Mathlib

theorem algebra_192505 : ∃ n : ℤ, Real.sqrt (abs (40 * Real.sqrt 2 - 57)) - Real.sqrt (40 * Real.sqrt 2 + 57) = n := by
  have h1 : abs (40 * Real.sqrt 2 - 57) = 57 - 40 * Real.sqrt 2 := by
    have h2 : 40 * Real.sqrt 2 < (57 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 * 40 - 57), Real.sqrt_nonneg (2 : ℝ)]
    rw [abs_of_neg (by linarith)]
    all_goals linarith
  have h2 : Real.sqrt (abs (40 * Real.sqrt 2 - 57)) = 4 * Real.sqrt 2 - 5 := by
    rw [h1]
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (4 * Real.sqrt 2 - 5), sq_nonneg (57 - 40 * Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h3 : Real.sqrt (40 * Real.sqrt 2 + 57) = 5 + 4 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (5 + 4 * Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  use -10
  have h4 : Real.sqrt (abs (40 * Real.sqrt 2 - 57)) - Real.sqrt (40 * Real.sqrt 2 + 57) = (-10 : ℝ) := by
    rw [h2, h3]
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  norm_num at h4 ⊢
  all_goals linarith