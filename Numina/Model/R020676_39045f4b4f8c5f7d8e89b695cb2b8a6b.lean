import Mathlib

theorem algebra_5198 {x : ℝ} (hx : x ≠ 0) (h : x ^ 2 - 1 / x ^ 2 = 16) :
    x ^ 4 + 1 / x ^ 4 = 258 := by
  have h1 : x ^ 4 + 1 / x ^ 4 = (x ^ 2 - 1 / x ^ 2) ^ 2 + 2 := by
    field_simp [hx]
    ring
  rw [h1, h]
  norm_num