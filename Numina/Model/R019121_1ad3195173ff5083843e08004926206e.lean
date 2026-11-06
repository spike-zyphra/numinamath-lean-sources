import Mathlib

theorem algebra_115212 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : x^2 - y^2 = 1) (h' : (x + 2)^2 + y^2 = 4 * 6 / 9) :
    x = Real.sqrt 3 := by
  have h1 : y^2 = x^2 - 1 := by 
    nlinarith
  have h2 : y^2 = (8 / 3 : ℝ) - (x + 2)^2 := by
    nlinarith
  have eq1 : x^2 - 1 = (8 / 3 : ℝ) - (x + 2)^2 := by
    nlinarith [h1, h2]
  have eq3 : 6 * x^2 + 12 * x + 1 = 0 := by
    nlinarith
  nlinarith [sq_nonneg (x + 1), sq_nonneg (y), sq_nonneg (x - 0), sq_nonneg (x * x), sq_nonneg ((x + 2) * (x + 2)), sq_nonneg (y * y), sq_pos_of_pos hx, sq_pos_of_pos hy]