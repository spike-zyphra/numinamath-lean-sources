import Mathlib

theorem algebra_4965 {x : ℝ} (hx : x ≠ 0) (h : x - 1/x = 6) : x^2 + 1/x^2 = 38 := by
  have h1 : x^2 + 1/x^2 = (x - 1/x)^2 + 2 := by
    field_simp [hx]
    ring
  rw [h1, h]
  norm_num