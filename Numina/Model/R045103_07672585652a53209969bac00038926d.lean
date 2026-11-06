import Mathlib

theorem inequalities_200521 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 + y^3 ≥ x^3 + y^4) : x^3 + y^3 ≤ 2 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1),
          sq_nonneg (x^2 - y), sq_nonneg (y^2 - x),
          sq_nonneg (x - y), sq_nonneg (x + y - 2),
          sq_nonneg (x * (x - 1)), sq_nonneg (y * (y - 1)),
          mul_pos hx hy, sq_nonneg (x * y - 1)]