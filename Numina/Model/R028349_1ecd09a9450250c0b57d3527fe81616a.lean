import Mathlib

theorem inequalities_229760 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x^4 + y^3 + x^2 + y + 1 > (9 / 2) * x * y := by
  nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (y - 1), sq_nonneg (x - y), sq_nonneg (x^2 - y), sq_nonneg (x - 1), sq_nonneg (y^2 - 1), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - 1), 
          mul_pos hx hy, 
          sq_nonneg (x^2 - x), sq_nonneg (y - x^2), sq_nonneg (y^2 - x^2)]