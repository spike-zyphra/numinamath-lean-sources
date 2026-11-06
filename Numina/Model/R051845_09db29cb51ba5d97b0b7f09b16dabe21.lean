import Mathlib

theorem algebra_262960 {x y : ℝ} (hxy : x = 2 * y ∧ y ≠ 0) : (x - y) * (2 * x + y) = 5 * y ^ 2 := by
  have hx : x = 2 * y := hxy.1
  rw [hx]
  ring