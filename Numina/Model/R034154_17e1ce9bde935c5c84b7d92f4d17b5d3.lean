import Mathlib

theorem algebra_177751 (x y : ℝ) (h : x^2 + y^2 - 2 * x + 4 * y = 0) :
    x - 2 * y ≤ 10 := by
  have h1 : (x - 1)^2 + (y + 2)^2 = 5 := by
    nlinarith
  have h2 : (x - 1 - 2 * (y + 2)) ^2 ≤ 25 := by
    have h3 : (x - 1)^2 + (y + 2)^2 = 5 := h1
    nlinarith [sq_nonneg ((x - 1) * (-2) - (y + 2) * 1), sq_nonneg ((x - 1) - 2 * (y + 2)), sq_nonneg ((x - 1) + 2 * (y + 2))]
  have h3 : (x - 1) - 2 * (y + 2) ≤ 5 := by
    nlinarith [show (x - 1 - 2 * (y + 2)) ^2 ≥ 0 by apply sq_nonneg]
  nlinarith