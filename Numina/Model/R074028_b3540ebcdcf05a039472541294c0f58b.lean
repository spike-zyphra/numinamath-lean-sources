import Mathlib

theorem algebra_214722 {x y : ℝ} (hx : x^3+6*x^2+16*x=-15) (hy : y^3+6*y^2+16*y=-17) :
    x+y=-4 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + 4), sq_nonneg (y + 4), sq_nonneg (x + y + 4), sq_nonneg (x - y), sq_nonneg (x + y - (-4)), sq_nonneg (x^2 + 4*x - 5), sq_nonneg (y^2 + 4*y - 5)]