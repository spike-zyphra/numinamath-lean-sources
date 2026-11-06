import Mathlib

theorem algebra_9781 {x : ℝ} (hx : x ≠ 0) (h : x - 1 / x = 16) : x ^ 3 - 1 / x ^ 3 = 4144 := by
  have h1 : x ^ 3 - 1 / x ^ 3 = (x - 1 / x) ^ 3 + 3 * (x - 1 / x) := by
    field_simp [hx]
    ring
  rw [h1, h]
  norm_num