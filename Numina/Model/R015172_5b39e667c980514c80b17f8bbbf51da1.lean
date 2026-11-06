import Mathlib

open Real Set

theorem algebra_311592 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x - 3 * sqrt (x + 1) = 3 * sqrt (y + 2) - y) :
    x + y ≤ 9 + 3 * sqrt 15 := by
  have h1 : 0 < x + 1 := by linarith
  have h2 : 0 < y + 2 := by nlinarith
  have h_eq : x + y = 3 * (sqrt (x + 1) + sqrt (y + 2)) := by
    nlinarith [h]

  nlinarith [h_eq, sq_nonneg (sqrt (x + 1) - (3 + Real.sqrt 15) / 2), sq_nonneg (sqrt (y + 2) - (3 + Real.sqrt 15) / 2), 
            Real.sqrt_nonneg 15, 
            Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num), 
            mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (y + 2)), 
            sq_nonneg (sqrt (x + 1) ^ 2 - sqrt (y + 2) ^ 2), 
            sq_nonneg (sqrt (x + 1) - sqrt (y + 2)), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (x + 1) by positivity), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (y + 2) by positivity)]