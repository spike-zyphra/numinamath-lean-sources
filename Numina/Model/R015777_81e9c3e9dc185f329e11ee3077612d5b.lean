import Mathlib

theorem algebra_237790 {x y : ℝ} (hx : x^3-3*x^2+2026*x=2023) (hy : y^3+6*y^2+2035*y=-4053) :
    x+y=-1 := by 
  have h4 : y = -1 - x := by
    nlinarith [sq_nonneg (y + x + 1), sq_nonneg (y + 1), sq_nonneg (x + 1), sq_nonneg (y + x + 1), sq_nonneg (y + 2), sq_nonneg (x - 1), sq_nonneg (y - (-1 - x)), sq_nonneg (x^2 - x), sq_nonneg (y^2 - y), sq_nonneg (x - y -1), sq_nonneg ((y +1 + x) ^ 2), sq_nonneg (x * y)]
  linarith [h4]