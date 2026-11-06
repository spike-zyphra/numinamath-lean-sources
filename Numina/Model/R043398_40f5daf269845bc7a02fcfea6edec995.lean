import Mathlib

open Real Set

theorem algebra_277355 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^2 + 4 * y^2 + 4 * x * y + 4 * x^2 * y^2 = 32) :
    sqrt 7 * (x + 2 * y) + 2 * x * y ≤ 16 := by
  have h1 : (x + 2 * y) ^ 2 + (2 * x * y) ^ 2 = 32 := by 
    nlinarith
  nlinarith [sq_nonneg ((x + 2 * y) - 2 * Real.sqrt 7), sq_nonneg ((2 * x * y) - 2), 
          sq_nonneg ((x + 2 * y) * (2 * x * y) - 4 * Real.sqrt 7), 
          mul_nonneg hx (show 0 ≤ y by linarith), 
          Real.sqrt_nonneg 7, 
          sq_nonneg ((x + 2 * y) - 2 * Real.sqrt 7), 
          sq_nonneg ((2 * x * y) - 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), 
          sq_nonneg ((2 * x * y) ^ 2 - 4), 
          sq_nonneg ((x + 2 * y) ^ 2 - 28), 
          mul_nonneg (Real.sqrt_nonneg 7) (show 0 ≤ (x + 2 * y : ℝ) by nlinarith)]