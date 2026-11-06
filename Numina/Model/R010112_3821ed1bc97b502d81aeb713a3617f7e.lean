import Mathlib

theorem algebra_14177 {x y : ℝ} (h : x^2 + y^2 = 10 * x - 6 * y - 34) : x + y = 2 := by
  have h1 : (x - 5) ^ 2 + (y + 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 5), sq_nonneg (y + 3)]
  have h2 : (x - 5) ^ 2 = 0 := by
    linarith [sq_nonneg (x - 5), sq_nonneg (y + 3)]
  have h3 : (y + 3) ^ 2 = 0 := by
    linarith [sq_nonneg (x - 5), sq_nonneg (y + 3)]
  have h4 : x - 5 = 0 := by
    rwa [sq_eq_zero_iff] at h2
  have h5 : y + 3 = 0 := by
    rwa [sq_eq_zero_iff] at h3
  have hx : x = 5 := by
    linarith
  have hy : y = -3 := by
    linarith
  linarith [hx, hy]