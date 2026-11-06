import Mathlib

theorem algebra_114804 {x y : ℝ} (hx : x = 300 * (1 - 30 / 100)) (hy : y = x * (1 + 30 / 100)) :
    x + y = 483 := by
  rw [hy, hx]
  norm_num