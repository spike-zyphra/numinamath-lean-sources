import Mathlib

theorem algebra_227122 (x y : ℝ) (h : (Real.sqrt (x ^ 2 + 1) - x + 1) * (Real.sqrt (y ^ 2 + 1) - y + 1) = 2) :
    x * y = 1 := by
  have h1 : Real.sqrt (x ^ 2 + 1) ≥ 0 := by positivity
  have h2 : Real.sqrt (y ^ 2 + 1) ≥ 0 := by positivity
  have hx1 : Real.sqrt (x ^ 2 + 1) ^ 2 = x ^ 2 + 1 := Real.sq_sqrt (by nlinarith)
  have hy1 : Real.sqrt (y ^ 2 + 1) ^ 2 = y ^ 2 + 1 := Real.sq_sqrt (by nlinarith)
  nlinarith [sq_nonneg (Real.sqrt (x ^ 2 + 1) - Real.sqrt (y ^ 2 + 1)), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 1), sq_nonneg (Real.sqrt (x ^ 2 + 1) - (x + 1)), sq_nonneg (Real.sqrt (y ^ 2 + 1) - (y + 1)), mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 1)) (Real.sqrt_nonneg (y ^ 2 + 1)), sq_nonneg (x * y -1)]