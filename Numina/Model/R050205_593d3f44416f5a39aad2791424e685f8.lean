import Mathlib

theorem algebra_13881 {x : ℝ} (hx : x ≠ 0) (h : x - 1/x = 4) : x^3 - 1/x^3 = 76 := by 
  have h1 : x^3 - 1 / x^3 = (x - 1 / x) ^ 3 + 3 * (x - 1 / x) := by
    field_simp [hx]
    ring
  rw [h1, h]
  norm_num