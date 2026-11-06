import Mathlib

theorem algebra_218835 (x : ℝ) (hx : x > 0) (h : 3 * x * 3 = 3) :
    5 * x * 5 = 8 + 1 / 3 := by
  have hx_eq : x = 1 / 3 := by
    linarith
  rw [hx_eq]
  norm_num