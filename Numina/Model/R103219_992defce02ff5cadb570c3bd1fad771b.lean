import Mathlib

theorem algebra_2319 {a : ℝ} (ha : 0 < a) (x : ℝ) (hx : x = a * (2 / 3) * (3 / 4) * (1 / 2)) :  x = a * (1 / 4) := by
  rw [hx]
  ring