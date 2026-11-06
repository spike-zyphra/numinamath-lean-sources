import Mathlib

theorem algebra_13860 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : x^3 - y^3 + (x - y)^3 - 36 * x * y = 3456) :
    x - y = 12 := by
  have h1 : x^3 - y^3 + (x - y)^3 - 36 * x * y = 3456 := h
  have h2 : x - y = 12 := by
    nlinarith [sq_nonneg (x - y - 12), sq_nonneg (x + y - 24), sq_nonneg (x - 2 * y), sq_nonneg (x^2 - (y + 12)^2), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy, sq_nonneg (x^2 - y^2), sq_nonneg ((x - y) * (x + y) - 144)]
  exact h2