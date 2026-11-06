import Mathlib

theorem algebra_8731
    (x y : ℝ)
    (h : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1) :
    x + y = 0 := by

  have h1 : 0 ≤ Real.sqrt (x^2 + 1) := Real.sqrt_nonneg (x^2 + 1)
  have h2 : Real.sqrt (x^2 + 1) ≥ 0 := Real.sqrt_nonneg (x^2 + 1)
  have h3 : Real.sqrt (x^2 + 1) ^2 = x^2 + 1 := Real.sq_sqrt (by positivity)
  have h4 : 0 ≤ Real.sqrt (y^2 + 1) := Real.sqrt_nonneg (y^2 + 1)
  have h5 : Real.sqrt (y^2 + 1) ≥ 0 := Real.sqrt_nonneg (y^2 + 1)
  have h6 : Real.sqrt (y^2 + 1) ^2 = y^2 + 1 := Real.sq_sqrt (by positivity)
  have h7 : (Real.sqrt (x^2 + 1) - x) * (Real.sqrt (y^2 + 1) - y) = 1 := by
    nlinarith [h, Real.sqrt_nonneg (x^2 + 1), Real.sqrt_nonneg (y^2 + 1), sq_nonneg (Real.sqrt (x^2 + 1) - x), sq_nonneg (Real.sqrt (y^2 + 1) - y), Real.sq_sqrt (show (0: ℝ) ≤ x^2 + 1 by positivity), Real.sq_sqrt (show (0: ℝ) ≤ y^2 + 1 by positivity)]
  have h8 : x + y = 0 := by
    nlinarith [Real.sqrt_nonneg (x^2 + 1), Real.sqrt_nonneg (y^2 + 1), Real.sq_sqrt (show (0: ℝ) ≤ x^2 + 1 by positivity), Real.sq_sqrt (show (0: ℝ) ≤ y^2 + 1 by positivity), sq_nonneg (x + y), sq_nonneg (Real.sqrt (x^2 + 1) - Real.sqrt (y^2 + 1)), sq_nonneg (x - y)]
  exact h8