import Mathlib

open Real

theorem inequalities_121646 (x y : ℝ) (hx : x > sqrt 2) (hy : y > sqrt 2) :
    x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4 > x^2 + y^2 := by
  have h1 : x ^ 2 > 2 := by
    have h2 : x > Real.sqrt 2 := hx
    have h3 : x ^ 2 > (Real.sqrt 2) ^ 2 := by nlinarith [Real.sqrt_nonneg 2, h2]
    have h4 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith
  have h2 : y ^ 2 > 2 := by
    have h3 : y > Real.sqrt 2 := hy
    have h4 : y ^ 2 > (Real.sqrt 2) ^ 2 := by nlinarith [Real.sqrt_nonneg 2, h3]
    have h5 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x*y - 2), sq_nonneg (x - 2), sq_nonneg (y - 2),
          sq_pos_of_pos (show 0 < x ^ 2 - 2 by nlinarith),
          sq_pos_of_pos (show 0 < y ^ 2 - 2 by nlinarith),
          mul_pos (show 0 < x ^ 2 - 2 by nlinarith) (show 0 < y ^ 2 - 2 by nlinarith),
          mul_pos (show 0 < x - Real.sqrt 2 by linarith) (show 0 < y - Real.sqrt 2 by linarith),
          Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]