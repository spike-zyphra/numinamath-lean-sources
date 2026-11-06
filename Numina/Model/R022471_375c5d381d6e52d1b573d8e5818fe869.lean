import Mathlib

theorem algebra_227821 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b * (a + b) = 4) :
    2 * a + b ≥ 2 * Real.sqrt 3 := by 
  nlinarith [sq_nonneg (a - (Real.sqrt 3 - 1)), sq_nonneg (b - 2),
    sq_nonneg (a + b - (Real.sqrt 3 + 1)), 
    sq_nonneg (a - (Real.sqrt 3 - 1)), sq_nonneg (b - 2),
    Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0),
    Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
    mul_pos ha hb, 
    sq_nonneg (a * b - (Real.sqrt 3 - 1) * 2), 
    mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
    sq_nonneg (a - (Real.sqrt 3 - 1)), sq_nonneg (b - 2),
    sq_nonneg (a * b - 2 * (Real.sqrt 3 - 1)), 
    mul_pos ha hb, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]