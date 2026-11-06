import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_319694 {x y : ℝ} (h : x^2 + y^2 = 169) :
    sqrt (24 * y - 10 * x + 338) + sqrt (24 * y + 10 * x + 338) ≤ 10 * sqrt 26 := by

  have h1 : 24 * y - 10 * x + 338 ≥ 0 := by
    nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 12), sq_nonneg (x + 5), sq_nonneg (y + 12),
      h, sq_nonneg (24 * y - 10 * x + 338)]

  have h2 : 24 * y + 10 * x + 338 ≥ 0 := by
    nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 12), sq_nonneg (x + 5), sq_nonneg (y + 12),
      h, sq_nonneg (24 * y + 10 * x + 338)]

  have h3 : (sqrt (24 * y - 10 * x + 338) + sqrt (24 * y + 10 * x + 338)) ^ 2 ≤ (10 * sqrt 26) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (24 * y - 10 * x + 338), Real.sqrt_nonneg (24 * y + 10 * x + 338),
      sq_nonneg (sqrt (24 * y - 10 * x + 338) - sqrt (24 * y + 10 * x + 338)), 
      sq_nonneg (x), sq_nonneg (y - 13), sq_nonneg (y + 13), sq_nonneg (x - 0), sq_nonneg (y - 12), 
      Real.sq_sqrt (show (24 * y - 10 * x + 338) ≥ 0 by linarith), 
      Real.sq_sqrt (show (24 * y + 10 * x + 338) ≥ 0 by linarith), 
      h, mul_nonneg (Real.sqrt_nonneg (24 * y - 10 * x + 338)) (Real.sqrt_nonneg (24 * y + 10 * x + 338)), 
      Real.sqrt_nonneg 26, Real.sq_sqrt (show (26 : ℝ) ≥ 0 by norm_num)]

  have h4 : sqrt (24 * y - 10 * x + 338) + sqrt (24 * y + 10 * x + 338) ≤ 10 * sqrt 26 := by
    have h5 : (sqrt (24 * y - 10 * x + 338) + sqrt (24 * y + 10 * x + 338)) ^ 2 ≤ (10 * sqrt 26) ^ 2 := h3
    have h6 : sqrt (24 * y - 10 * x + 338) + sqrt (24 * y + 10 * x + 338) ≥ 0 := by 
      positivity
    have h7 : (10 * sqrt 26) ≥ 0 := by 
      positivity
    nlinarith [Real.sqrt_nonneg 26, Real.sq_sqrt (show (26 : ℝ) ≥ 0 by norm_num)]

  exact h4