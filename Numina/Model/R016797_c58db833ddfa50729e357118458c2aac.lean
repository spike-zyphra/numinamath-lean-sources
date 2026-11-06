import Mathlib

theorem algebra_307576 (x y : ℝ) (h : x^2 - 8 * x + y^2 - 6 * y + 24 = 0) :
    x - 2 * y ≤ Real.sqrt 5 - 2 := by
  have h1 : (x - 4) ^ 2 + (y - 3) ^ 2 = 1 := by
    nlinarith
  -- write $x - 2 * y$ in terms of $(x - 4), (y - 3)$
  have h6 : (x - 4) - 2 * (y - 3) ≤ Real.sqrt 5 := by
    have h11 : ((x - 4) - 2 * (y - 3)) ^ 2 ≤ 5 := by
      nlinarith [sq_nonneg ((x - 4) + 2 * (y - 3) / 5), sq_nonneg (2 * (x - 4) - (y - 3) * 1), sq_nonneg ((x - 4) * 2 + (y - 3) * 1), sq_nonneg ((x - 4) * 2 + (y - 3) * 1), Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    have h5 : Real.sqrt 5 ≥ 0 := by positivity
    have h9 : ((x - 4) - 2 * (y - 3)) ^ 2 ≤ (Real.sqrt 5) ^ 2 := by
      nlinarith [h11, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  -- Finally must write the inequality
  have h7 : x - 2 * y ≤ Real.sqrt 5 - 2 := by
    nlinarith [h6]
  linarith