import Mathlib

theorem algebra_281970 {x y t b : ℝ} (hx : x = t + b * y) (ht : t = 7) (hb : b = 10) : x = 10 * y + 7 := by
  rw [ht, hb] at hx
  linarith