import Mathlib

theorem algebra_6854 {x : ℝ} (hx : x > 0) (h : x + 1/x = 4) : x^3 + 1/x^3 = 52 := by
  have h1 : x ≠ 0 := by linarith
  have h2 : x^3 + 1 / x^3 = (x + 1 / x)^3 - 3 * (x + 1 / x) := by
    field_simp [h1]
    ring
  rw [h2, h]
  norm_num