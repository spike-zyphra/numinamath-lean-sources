import Mathlib

theorem algebra_262433 {x : ℝ} (hx : x ≠ 0) (h1 : 40 / 100 * x + 50 / 100 * (x - 40 / 100 * x) + (1 - 1 / 3) * 40 / 100 * x = x - 10) :
    x = 300 := by
  nlinarith