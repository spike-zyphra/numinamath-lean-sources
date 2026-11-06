import Mathlib

theorem inequalities_316169 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^3 + y^3 = x - y) : x^2 + 4 * y^2 < 1 := by
  have h1 : x < 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y), sq_nonneg (y + 1), sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1/4), 
        sq_nonneg (x * y), mul_pos hx hy, sq_nonneg (x - y), sq_nonneg (x + y)]

  have h2 : x^2 + 4 * y^2 < 1 := by
    nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1/4), sq_nonneg (x - 2 * y), sq_nonneg (x + 2 * y - 1), sq_nonneg (x - 1/2), sq_nonneg (y - 1/4), sq_nonneg (x - 2 * y), 
        mul_pos hx hy, h, h1, sq_nonneg (x * y - 1/4), mul_pos hx (show 0 < 1 - x by nlinarith)]
  linarith