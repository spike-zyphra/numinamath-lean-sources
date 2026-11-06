import Mathlib

theorem algebra_5450 (x y : ℝ) (hxy : x * y ≥ 0) (h1 : x + y + Real.sqrt (x * y) = 19) (h2 : x ^ 2 + y ^ 2 + x * y = 119) :
    False := by
  have h3 : 0 ≤ Real.sqrt (x * y) := Real.sqrt_nonneg (x * y)
  have h4 : (Real.sqrt (x * y)) ^ 2 = x * y := by
    rw [Real.sq_sqrt]
    linarith
  have h5 : Real.sqrt (x * y) = 121 / 19 := by
    nlinarith [h1, h2, h4, Real.sqrt_nonneg (x * y)]
  have h6 : x * y = (121 / 19) ^ 2 := by
    have h7 : (Real.sqrt (x * y)) ^ 2 = x * y := by
      rw [Real.sq_sqrt]
      linarith
    rw [show Real.sqrt (x * y) = (121 / 19) by linarith [h5]] at h7
    nlinarith
  have h7 : x + y = 240 / 19 := by
    nlinarith [h1, h5]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 240 / 19), sq_nonneg (x * y - (121 / 19) ^ 2)]