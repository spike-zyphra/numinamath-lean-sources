import Mathlib

theorem algebra_96898 {x : ℝ} (hx : x * 5 = 4 * y) (hy : 0 < y) (h : 3 * x - 4 * y = 100) :
x = 240 := by 
  nlinarith [sq_nonneg (x + 50), sq_nonneg (y + 62.5), sq_nonneg (5 * x - 4 * y)]