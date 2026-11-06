import Mathlib

theorem algebra_21642 (x y : ℝ) (h : 2*x^2 - 8*x + 3*y^2 + 6*y + 5 = 0) :
    x ≤ 2 + Real.sqrt 3 := by
  have h1 : 2 * (x - 2) ^ 2 + 3 * (y + 1) ^ 2 = 6 := by
    nlinarith
  have h2 : (x - 2) ^ 2 ≤ 3 := by
    nlinarith [sq_nonneg (y + 1), sq_nonneg (x - 2)]
  have h6 : x - 2 ≤ Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (x - 2 - Real.sqrt 3)]
  linarith