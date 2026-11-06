import Mathlib

open Real

theorem algebra_1542 {x y : ℝ}
    (hx : x = (1 - sqrt 2 + sqrt 3) / 2)
    (hy : y = (1 + sqrt 2 - sqrt 3) / 2) :
    ((x^2 - y^2) / 2)^2 + x * y = 1 / 4 := by
  rw [hx, hy]
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), 
          Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, 
          sq_nonneg (sqrt 2 - sqrt 3), 
          Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3),
          sq_nonneg (sqrt 2 ^ 2 - 1), sq_nonneg (sqrt 3 ^ 2 - 1),
          Real.sqrt_le_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
          Real.sqrt_le_sqrt (show 0 ≤ (3 : ℝ) by norm_num),
          mul_self_nonneg (sqrt 2), mul_self_nonneg (sqrt 3)
          ]