import Mathlib

theorem algebra_284584 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 + 1 / 27 = x * y) :
    1 / x = 3 := by
  have h1 : (x - 1 / 3)^2 + (y - 1 / 3)^2 + (x - y) ^2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3),
      sq_nonneg (x * y - 1 / 9), h, mul_pos hx hy, mul_pos (show (0 : ℝ) < y from by linarith) (show (0 : ℝ) < x from by linarith)]
  have h2 : (x - 1 / 3)^2 = 0 := by
    nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg (x - y), h1]
  have h3 : (y - 1 / 3)^2 = 0 := by
    nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg (x - y), h1]
  have h4 : (x - y) ^2 = 0 := by
    nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg (x - y), h1]
  have h5 : x - 1 / 3 = 0 := by
    rwa [sq_eq_zero_iff] at h2
  have h6 : y - 1 / 3 = 0 := by
    rwa [sq_eq_zero_iff] at h3
  have h7 : x - y = 0 := by
    rwa [sq_eq_zero_iff] at h4
  have hx1 : x = 1 / 3 := by linarith
  rw [hx1]
  norm_num