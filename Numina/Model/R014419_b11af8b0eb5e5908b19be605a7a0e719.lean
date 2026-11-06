import Mathlib


theorem inequalities_600187
    (x y : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (h : x^3 + y^3 = x - y) :
    x^2 + 4 * y^2 < 1 := by
  have h1 : x > y := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_pos_of_pos hx, sq_pos_of_pos hy, sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y)]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y - 1/2), sq_nonneg (x - 1), sq_nonneg (y - x/2), sq_nonneg (y^2 -1/4), mul_pos hx hy, mul_pos (sub_pos.mpr h1) (show 0 < y by linarith)]