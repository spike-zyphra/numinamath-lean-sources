import Mathlib

theorem algebra_5757 {x : ℝ} (hx : x ≠ 0) (h : x + 1 / x = 11) : x ^ 2 + 1 / x ^ 2 = 119 := by
  have h1 : x ^ 2 + 1 / x ^ 2 = (x + 1 / x)^2 - 2 := by
    field_simp [hx]
    ring
  rw [h1, h]
  norm_num