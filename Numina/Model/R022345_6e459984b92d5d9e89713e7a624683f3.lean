import Mathlib

theorem algebra_186128 {x : ℝ} (hx : 0 ≤ x) (h : 2021 * (x ^ 2020) ^ ((1 : ℝ) / 202) - 1 = 2020 * x) :
    x = 1 := by
  have h1 : (x ^ 2020 : ℝ) ^ ((1 : ℝ) / 202) = x ^ 10 := by
    have h2 : (x ^ 2020 : ℝ) ^ ((1 : ℝ) / 202) = (x ^ (2020 * (1 / 202 : ℝ))) := by 
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h2]
    have h3 : (2020 * (1 / 202 : ℝ)) = (10 : ℝ) := by
      norm_num
    rw [h3]
    all_goals norm_cast
  rw [h1] at h
  have h2 : 2021 * (x ^ 10) - 1 = 2020 * x := by
    nlinarith 
  have h3 : 2021 * (x ^ 10) - 2020 * x - 1 = 0 := by
    linarith
  have h4 : (x - 1) * (2021 * (x ^ 9) + 2021 * (x ^ 8) + 2021 * (x ^ 7) + 2021 * (x ^ 6) + 2021 * (x ^ 5) + 2021 * (x ^ 4) + 2021 * (x ^ 3) + 2021 * (x ^ 2) + 2021 * x + 1) = 0 := by
    nlinarith [sq_nonneg (x ^ 5), sq_nonneg (x ^ 4 - x ^ 3), sq_nonneg (x ^ 3 - x ^ 2), sq_nonneg (x ^ 2 - x), sq_nonneg (x - 1), sq_nonneg (x ^ 9 - x ^ 8), sq_nonneg (x ^ 8 - x ^ 7), sq_nonneg (x ^ 7 - x ^ 6), sq_nonneg (x ^ 6 - x ^ 5), sq_nonneg (x ^ 5 - x ^ 4), sq_nonneg (x ^ 4 - x ^ 3), sq_nonneg (x ^ 3 - x ^ 2), sq_nonneg (x ^ 2 - x), sq_nonneg (x - 1)]
  cases' (mul_eq_zero.mp h4) with h5 h6 
  · -- Case x - 1 = 0, so x = 1
    linarith 
  · -- Show that the second factor can not be zero since all terms are non-negative.
    nlinarith [sq_nonneg (x ^ 4), sq_nonneg (x ^ 3), sq_nonneg (x ^ 2 - x), sq_nonneg (x - 1), sq_nonneg (x ^ 5), sq_nonneg (x ^ 4 - x ^ 3), sq_nonneg (x ^ 3 - x ^ 2), sq_nonneg (x ^ 2 - x), sq_nonneg (x - 1)]