import Mathlib

theorem algebra_191623 : Real.sqrt ((Real.sqrt 3 - 3)^2) - (Real.sqrt 3 - 3) = 6 - 2 * Real.sqrt 3 := by
  have h2 : Real.sqrt ((Real.sqrt 3 - 3) ^ 2) = 3 - Real.sqrt 3 := by
    have h3 : Real.sqrt ((Real.sqrt 3 - 3) ^ 2) = abs (Real.sqrt 3 - 3) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h3]
    have h4 : Real.sqrt 3 < (3 : ℝ) := by
      have h5 : Real.sqrt (3 : ℝ) < (3 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), show (3 : ℝ) > 0 by norm_num, show (Real.sqrt 3) ^ 2 = 3 by rw [Real.sq_sqrt]; all_goals norm_num]
      linarith
    have h6 : (Real.sqrt 3 : ℝ) - 3 < (0 : ℝ) := by linarith
    rw [abs_of_neg (h6)]
    all_goals 
      linarith
  rw [h2]
  all_goals 
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]