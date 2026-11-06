import Mathlib

theorem inequalities_2601
    (x y : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (h : x - y = x ^ 3 + y ^ 3) :
    x ^ 2 + 4 * y ^ 2 < 1 := by
  have h1 : 0 < x - y := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - y ^ 2), sq_pos_of_pos hx, sq_pos_of_pos hy, h]
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1 / 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1 / 4), sq_nonneg (x + y - 1), sq_nonneg (x - 2 * y), sq_nonneg (x - 1), sq_nonneg (y - 1 / 2), 
            mul_pos hx hy, mul_pos h1 (show 0 < x by linarith), sq_pos_of_pos hx, sq_pos_of_pos hy]