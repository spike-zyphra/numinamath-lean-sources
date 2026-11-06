import Mathlib

theorem algebra_319137 (x y z : ℝ) (h : x^2 + 4 * y^2 + 9 * z^2 = 2009) :
    x + 2 * y + 3 * z ≤ 7 * Real.sqrt 123 := by
  have h1 : (x + 2 * y + 3 * z) ^ 2 ≤ 6027 := by
    nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (2 * y - 3 * z), sq_nonneg (x - 3 * z),
      sq_nonneg (x), sq_nonneg (y - z), sq_nonneg (6 * x - 6 * z), sq_nonneg (2 * x - 3 * z)]
  have h2 : (x + 2 * y + 3 * z) ≤ Real.sqrt 6027 := by
    have h3 : (x + 2 * y + 3 * z) ^ 2 ≤ 6027 := h1
    have h4 : Real.sqrt 6027 ≥ 0 := by positivity
    have h5 : Real.sqrt 6027 ^ 2 = (6027 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    nlinarith [Real.sqrt_nonneg 6027]
  have h6 : Real.sqrt 6027 = 7 * Real.sqrt 123 := by
    calc
      Real.sqrt 6027 = Real.sqrt (7 ^ 2 * 123) := by norm_num
      _ = (Real.sqrt (7 ^ 2)) * Real.sqrt 123 := by rw [Real.sqrt_mul (by norm_num)]
      _ = (7) * Real.sqrt 123 := by
        rw [Real.sqrt_sq (by norm_num)]
  rw [h6] at h2
  linarith