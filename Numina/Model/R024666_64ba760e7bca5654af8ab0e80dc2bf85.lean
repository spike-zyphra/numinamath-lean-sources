import Mathlib

theorem algebra_196576 {x y : ℝ} (h : (x - 13)^2 + (y - 14)^2 + (x - y)^2 = 1 / 3) :
    x = 13 + 1 / 3 ∧ y = 13 + 2 / 3 := by
  have h1 : (x - (13 + 1 / 3)) ^ 2 + (y - (13 + 2 / 3)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y - 1 / 3), sq_nonneg (x - (13 + 1 / 3)), sq_nonneg (y - (13 + 2 / 3)), sq_nonneg (x - y - 1 / 3)]
  have hx1 : x - (13 + 1 / 3) = 0 := by
    nlinarith [sq_nonneg (x - (13 + 1 / 3)), sq_nonneg (y - (13 + 2 / 3)), h1]
  have hy1 : y - (13 + 2 / 3) = 0 := by
    nlinarith [sq_nonneg (x - (13 + 1 / 3)), sq_nonneg (y - (13 + 2 / 3)), h1]
  constructor
  · linarith [hx1]
  · linarith [hy1]