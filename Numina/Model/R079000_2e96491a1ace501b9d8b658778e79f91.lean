import Mathlib

theorem algebra_141723 {x : ℝ} (hx : x > 0) (h : 4 * x * (1 + x / 100) = 429) :
    4 * x = 260 := by
  nlinarith [sq_nonneg (x - 65), sq_nonneg (x + 165)]