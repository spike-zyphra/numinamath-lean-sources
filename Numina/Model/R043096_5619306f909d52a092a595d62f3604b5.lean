import Mathlib

theorem algebra_263344 (x y : ℝ) (h : x^2 + y^2 + 25 = 10 * (x + y)) :
    x^2 + 8 * y + y^2 + 14 * x - 6 ≥ 29 := by
  have h1 : (x - 5) ^ 2 + (y - 5) ^ 2 = 25 := by 
    nlinarith 
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - 5 - (y - 5)), sq_nonneg (x - 5 + (y - 5)), sq_nonneg (x + 7 - (y + 4)), 
          sq_nonneg (x - 5 - (y - 5)), sq_nonneg (x + 7 + y + 4), 
          sq_nonneg (x - 1), sq_nonneg (y - 1)]