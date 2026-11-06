import Mathlib

theorem inequalities_205419 (x : ℝ) (hx : 1 ≤ x) : x^5 - 1 / x^4 ≥ 9 * (x - 1) := by
  have h1 : x ≥ 1 := by linarith
  have h2 : x ^ 4 ≥ 1 := by
    calc
      x^4 ≥ (1:ℝ)^4 := by apply pow_le_pow_left; all_goals linarith; all_goals nlinarith
      _ = 1 := by norm_num
  have h3 : x ^ 4 > 0 := by
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1), sq_nonneg (x + 1)]
  have h4 : x ^ 5 - 1 / x ^ 4 - 9 * (x - 1) ≥ 0 := by
    have h5 : (x ^ 5 - 1 / x ^ 4 - 9 * (x - 1)) * x ^ 4 ≥ 0 := by
      have h6 : (x ^ 5 - 1 / x ^ 4 - 9 * (x - 1)) * x ^ 4 =
        (x ^ 9 - 1 - 9 * (x - 1) * x ^ 4) := by
        field_simp
        ring
      rw [h6]
      have h7 : x ^ 9 - 1 - 9 * (x - 1) * x ^ 4 ≥ 0 := by
        nlinarith [sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - 3), sq_nonneg (x ^ 3 - 1), 
                  sq_nonneg (x ^ 3 - 3), sq_nonneg (x - 1), sq_nonneg (x ^ 4 - x), 
                  sq_nonneg (x ^ 3 - x), mul_nonneg (show (0 : ℝ) ≤ x - 1 by linarith) 
                  (show (0 : ℝ) ≤ x by linarith), mul_nonneg (show (0 : ℝ) ≤ x - 1 by nlinarith) 
                  (show (0 : ℝ) ≤ x ^ 2 by nlinarith), mul_nonneg (show (0 : ℝ) ≤ x - 1 by nlinarith) 
                  (show (0 : ℝ) ≤ x ^ 3 by nlinarith), mul_nonneg (show (0 : ℝ) ≤ x - 1 by nlinarith) 
                  (show (0 : ℝ) ≤ x ^ 4 by nlinarith)]
      linarith
    nlinarith [h3, h1, h2]
  linarith