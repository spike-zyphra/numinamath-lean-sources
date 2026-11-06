import Mathlib

theorem inequalities_174857 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^3 + y^3 = x - y) : x^2 + y^2 < 1 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + y - 1),
            sq_nonneg (x - y), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - y),
            mul_pos hx hy, sq_nonneg (x + y),
            mul_pos hx (show (0 : ℝ) < y by linarith),
            mul_pos hy (show (0 : ℝ) < x by linarith)]