import Mathlib

theorem algebra_271747 {x : ℝ} (hx : x ≠ 0) (h : x = -2) : (x) * (x^2) * (1 / x) = 4 := by
  rw [h]
  norm_num