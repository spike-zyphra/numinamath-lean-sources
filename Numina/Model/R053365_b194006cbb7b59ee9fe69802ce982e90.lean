import Mathlib

theorem algebra_143276 (x y : ℝ) (h : x^2 - 2 * x + y^2 - 2 * Real.sqrt 3 * y = -4)
    (h' : (x - 1)^2 + (y - Real.sqrt 3)^2 = 0) :
    x^2 + y^2 + 2 * x = 6 := by
  have hx1 : (x - 1) ^ 2 = 0 := by 
    have h1 : (x - 1) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h2 : (y - Real.sqrt 3) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith
  have hy2 : (y - Real.sqrt 3) ^ 2 = 0 := by
    have h1 : (x - 1) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h2 : (y - Real.sqrt 3) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith
  have hx : x = 1 := by
    nlinarith
  have hy : y = Real.sqrt 3 := by
    nlinarith
  rw [hx, hy]
  have h4 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith [h4]