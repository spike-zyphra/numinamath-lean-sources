import Mathlib

theorem inequalities_599260 (a b : ℝ) (h : a + b = 1) :
    a * b * (a^4 + b^4) ≤ (5 * Real.sqrt 10 - 14) / 27 := by 
  have h1 : b = 1 - a := by linarith 
  rw [h1]
  nlinarith [sq_nonneg (a - (1 - a)), sq_nonneg (a - (4 - Real.sqrt 10) / 6), sq_nonneg ((1 - a) - (4 - Real.sqrt 10) / 6), sq_nonneg (a * (1 - a) - (4 - Real.sqrt 10) / 6), sq_nonneg (a - 1 / 2), sq_nonneg ((1 - a) - 1 / 2), sq_nonneg (a - (1 - a)), Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)]