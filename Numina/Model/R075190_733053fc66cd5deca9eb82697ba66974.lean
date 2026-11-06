import Mathlib

theorem algebra_2464 {x y : ℝ} (h : 2*x + x^2 + x^2*y^2 + 2 = -2*x*y) : x + y = 0 := by
  have h1 : (x + 1)^2 + (x * y + 1)^2 = 0 := by
    nlinarith [sq_nonneg (x * y + 1), sq_nonneg (x + 1)]
  have h2 : (x + 1)^2 = 0 := by
    linarith [sq_nonneg (x + 1), sq_nonneg (x * y + 1)]
  have h3 : (x * y + 1)^2 = 0 := by
    linarith [sq_nonneg (x + 1), sq_nonneg (x * y + 1)]
  have h4 : x + 1 = 0 := by
    rw [sq_eq_zero_iff] at h2
    linarith
  have hx : x = -1 := by
    linarith
  have h5 : x * y + 1 = 0 := by
    rw [sq_eq_zero_iff] at h3
    linarith
  have hy : y = 1 := by
    rw [hx] at h5
    have : (-1) * y + 1 = 0 := by linarith
    linarith
  linarith [hx, hy]