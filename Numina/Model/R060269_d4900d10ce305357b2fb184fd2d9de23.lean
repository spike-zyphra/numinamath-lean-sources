import Mathlib

open Real Set

theorem algebra_325122 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + 3 * b + c = 9) :
    a + b ^ 2 + c ^ 3 ≥ (243 - 8 * √3) / 36 := by
  nlinarith [sq_nonneg (a - (9 / 2 - Real.sqrt 3 / 3)), sq_nonneg (b - 3 / 2), sq_nonneg (c - Real.sqrt 3 / 3), sq_nonneg (c ^ 2 - 1 / 3), sq_nonneg (b - 3 / 2), sq_nonneg (c - Real.sqrt 3 / 3), 
          sq_nonneg (a - (9 / 2 - Real.sqrt 3 / 3)), 
          Real.sqrt_nonneg 3, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3),
          Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3),
          sq_nonneg (b * √3 - 3 / 2 * √3), 
          sq_nonneg (c * √3 - 1 / 3 * √3)]