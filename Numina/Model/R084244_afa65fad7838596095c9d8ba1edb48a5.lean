import Mathlib

theorem algebra_16294 {x y : ℝ} (hx : x = -5) (hxy : x ^ 2 = y - 3) : y = 28 := by
  rw [hx] at hxy
  linarith