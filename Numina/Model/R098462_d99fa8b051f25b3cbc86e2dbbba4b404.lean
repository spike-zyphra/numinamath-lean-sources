import Mathlib

theorem algebra_321477 (x : ℝ) (hx : 0 < x) (h : (1 + 22 / 100) * x * (1 + 10 / 100) = x - (1 + 1 / 100)) :
    x = 4 := by
  nlinarith