import Mathlib

theorem algebra_319076 (a b : ℝ) (h : a > abs b) : a ^ 2 > b ^ 2 := by
  cases' le_or_lt 0 b with h1 h1
  · -- Case where b ≥ 0
    have h2 : abs b = b := by
      simp [abs_of_nonneg h1]
    have h3 : a > b := by linarith [h, h2]
    have h4 : a + b > 0 := by linarith [h3, h1]
    nlinarith [h3, h4, sq_nonneg (a - b), sq_nonneg (a + b), h1]
  · -- Case where b < 0
    have h2 : abs b = -b := by
      simp [abs_of_neg h1]
    have h3 : a > -b := by linarith [h, h2]
    have h4 : a + b > 0 := by linarith [h3, h1]
    have h5 : a - b > 0 := by linarith [h3, h1]
    nlinarith [h4, h5, sq_nonneg (a - b), sq_nonneg (a + b), h1]