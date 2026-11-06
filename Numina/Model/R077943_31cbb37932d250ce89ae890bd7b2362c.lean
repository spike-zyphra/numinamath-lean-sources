import Mathlib

theorem algebra_196084 {x y : ℝ} (h : (x - 7) ^ 2 + (y - 8) ^ 2 + (x - y) ^ 2 = 1 / 3) :
    x = 7 + 1 / 3 ∧ y = 7 + 2 / 3 := by 
  have eq1 : (x - 22 / 3) ^ 2 + (y - 23 / 3) ^ 2 = 0 := by
    nlinarith
  have hx : x - 22 / 3 = 0 := by
    nlinarith [sq_nonneg (x - 22 / 3), sq_nonneg (y - 23 / 3)]
  have hy : y - 23 / 3 = 0 := by
    nlinarith [sq_nonneg (x - 22 / 3), sq_nonneg (y - 23 / 3)]
  constructor
  · -- Show that x = 7 + 1/3
    linarith
  · -- Show that y = 7 + 2/3
    linarith