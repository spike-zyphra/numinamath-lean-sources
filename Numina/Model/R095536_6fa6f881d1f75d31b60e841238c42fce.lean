import Mathlib

theorem inequalities_601154 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x^4 + y^4 + (x^2 + 1) * (y^2 + 1) ≥
    x^3 * (1 + y) + y^3 * (1 + x) + x + y := by
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x*y - 1),
            sq_nonneg (x - 1), sq_nonneg (y - 1),
            mul_pos hx hy
  ]