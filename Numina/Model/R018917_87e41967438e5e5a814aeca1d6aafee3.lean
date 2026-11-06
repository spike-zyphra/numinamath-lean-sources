import Mathlib

theorem inequalities_132445 {x y : ℝ} (hx : x^3 > y^2) (hy : y^3 > x^2) : y > 1 := by
  have h1 : y > 0 := by
    nlinarith [sq_nonneg (y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y ^ 2 - x ^ 2), sq_nonneg (y - 1), sq_nonneg (x ^ 3 - y ^ 3)]
  have h2 : x > 0 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y ^ 2 - x ^ 2), sq_nonneg (y - 1), sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x)]
  have h3 : 0 < x := h2
  have h4 : 0 < y := h1
  have h5 : (x * y) ^ 3 > (x * y) ^ 2 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos h2 h1, hx, hy, sq_nonneg (x * y - 1)]
  have h6 : x * y > 1 := by
    nlinarith [h5, mul_pos h2 h1]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), mul_pos h2 h1, h6]