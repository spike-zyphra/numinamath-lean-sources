import Mathlib

theorem algebra_301846 {x y : ℝ} (h : (2 * x + 1)^2 + y^2 + (y - 2 * x)^2 = 1 / 3) : x + y = -2 / 3 := by
  have h1 : (x + 1 / 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (2 * x + 1 - 1 / 3), sq_nonneg (y + 1 / 3), sq_nonneg (y - 2 * x + 2 / 3), sq_nonneg (3 * x + 1), sq_nonneg (3 * y + 1)]
  have h2 : x + 1 / 3 = 0 := by
    rw [sq_eq_zero_iff] at h1
    linarith
  have h3 : x = -1 / 3 := by
    linarith
  have h4 : y = -1 / 3 := by
    rw [h3] at h
    nlinarith
  linarith [h3, h4]