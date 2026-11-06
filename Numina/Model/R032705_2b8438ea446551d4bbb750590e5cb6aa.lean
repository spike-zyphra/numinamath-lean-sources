import Mathlib

theorem algebra_180755 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^3 + y^3 = (4 * x - 5 * y) * y) :
    y ≤ 1 / 3 := by
  nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (x - 2 / 3), sq_nonneg (y - 1 / 3), 
          sq_nonneg (x ^ 2 - 4 * y), sq_nonneg (x * y - 2 / 3 * y), 
          sq_nonneg ((x - 2 / 3) * (y - 1 / 3)), 
          mul_pos hx hy, mul_pos hx (show 0 < x ^ 2 by positivity), 
          mul_pos hy (show 0 < y ^ 2 by positivity), 
          mul_pos (show 0 < x ^ 2 by positivity) (show 0 < y ^ 2 by positivity), 
          mul_pos hx (show 0 < y ^ 3 by positivity)
        ]