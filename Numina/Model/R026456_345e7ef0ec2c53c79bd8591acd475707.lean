import Mathlib

theorem inequalities_221607 (x y : ℝ) (h : x ^ 4 + y ^ 4 ≥ 2) :
    |x ^ 16 - y ^ 16| + 4 * x ^ 8 * y ^ 8 ≥ 4 := by
  by_cases h1 : x ^ 16 - y ^ 16 ≥ 0
  · -- |x ^ 16 - y ^ 16| = x ^ 16 - y ^ 16 
    have h2 : |x ^ 16 - y ^ 16| = x ^ 16 - y ^ 16 := by
      apply abs_of_nonneg
      linarith
    rw [h2]
    nlinarith [sq_nonneg (x ^ 8 - y ^ 8), sq_nonneg (x ^ 8 + y ^ 8 - 2), sq_nonneg (x ^ 4 - y ^ 4), sq_nonneg (x ^ 4 * y ^ 4 - 1), sq_nonneg (x ^ 4 + y ^ 4 - 2), sq_nonneg (x ^ 8 - y ^ 8), sq_nonneg (x * y), sq_nonneg (x ^ 4 - y ^ 4), mul_nonneg (show (0 : ℝ) ≤ x ^ 4 by positivity) (show (0 : ℝ) ≤ y ^ 4 by positivity)]
  · -- |x ^ 16 - y ^ 16| = y ^ 16 - x ^ 16
    have h2 : |x ^ 16 - y ^ 16| = y ^ 16 - x ^ 16 := by
      rw [abs_of_neg]
      linarith
      all_goals nlinarith
    rw [h2]
    nlinarith [sq_nonneg (x ^ 8 - y ^ 8), sq_nonneg (x ^ 8 + y ^ 8 - 2), sq_nonneg (x ^ 4 - y ^ 4), sq_nonneg (x ^ 4 * y ^ 4 - 1), sq_nonneg (x ^ 4 + y ^ 4 - 2), sq_nonneg (x ^ 8 - y ^ 8), sq_nonneg (x * y), sq_nonneg (x ^ 4 - y ^ 4), mul_nonneg (show (0 : ℝ) ≤ x ^ 4 by positivity) (show (0 : ℝ) ≤ y ^ 4 by positivity)]