import Mathlib

theorem algebra_319067 {x y : ℝ} (h : (x + Real.sqrt (x ^ 2 + 2)) * (y + Real.sqrt (y ^ 2 + 4)) = 16) :
    x * Real.sqrt (y ^ 2 + 4) + y * Real.sqrt (x ^ 2 + 2) = 31 / 4 := by
  have h1 : (Real.sqrt (x^2 + 2)) ^ 2 = x^2 + 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h2 : (Real.sqrt (y^2 + 4)) ^ 2 = y^2 + 4 := by
    rw [Real.sq_sqrt]
    positivity
  have h3 : (x + Real.sqrt (x ^ 2 + 2)) * (Real.sqrt (x ^ 2 + 2) - x) = 2 := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 2), h1]
  have h4 : (y + Real.sqrt (y ^ 2 + 4)) * (Real.sqrt (y ^ 2 + 4) - y) = 4 := by
    nlinarith [Real.sqrt_nonneg (y ^ 2 + 4), h2]
  have h5 : (Real.sqrt (x^2 + 2) - x) * (Real.sqrt (y^2 + 4) - y) = 1 / 2 := by
    have h6 : (x + Real.sqrt (x ^ 2 + 2)) * (y + Real.sqrt (y ^ 2 + 4)) = 16 := h
    have h7 : (x + Real.sqrt (x ^ 2 + 2)) * (Real.sqrt (x ^ 2 + 2) - x) = 2 := h3
    have h8 : (y + Real.sqrt (y ^ 2 + 4)) * (Real.sqrt (y ^ 2 + 4) - y) = 4 := h4
    nlinarith [sq_nonneg (x + Real.sqrt (x ^ 2 + 2)), sq_nonneg (y + Real.sqrt (y ^ 2 + 4)), sq_nonneg (Real.sqrt (x^2 + 2) - x), sq_nonneg (Real.sqrt (y^2 + 4) - y), h6, h7, h8, Real.sqrt_nonneg (x ^ 2 + 2), Real.sqrt_nonneg (y ^ 2 + 4)]
  have eq1 : (x + Real.sqrt (x ^ 2 + 2)) * (y + Real.sqrt (y ^ 2 + 4)) =
    x * y + x * Real.sqrt (y ^ 2 + 4) + y * Real.sqrt (x^2 + 2) + Real.sqrt (x ^ 2 + 2) * Real.sqrt (y ^ 2 + 4) := by ring
  rw [eq1] at h
  have eq2 : (Real.sqrt (x ^ 2 + 2) - x) * (Real.sqrt (y ^ 2 + 4) - y) =
    Real.sqrt (x ^ 2 + 2) * Real.sqrt (y ^ 2 + 4) - (y * Real.sqrt (x ^ 2 + 2) + x * Real.sqrt (y ^ 2 + 4)) + (x * y) := by ring
  rw [eq2] at h5
  nlinarith [Real.sqrt_nonneg (x ^ 2 + 2), Real.sqrt_nonneg (y ^ 2 + 4), sq_nonneg (Real.sqrt (x ^ 2 + 2) * Real.sqrt (y ^ 2 + 4)), sq_nonneg (x * Real.sqrt (y ^ 2 + 4) + y * Real.sqrt (x ^ 2 + 2)), sq_nonneg (x - (-y / 2)), sq_nonneg (y - (-x / 2)), Real.sqrt_nonneg (x ^ 2 + 2), Real.sqrt_nonneg (y ^ 2 + 4)]