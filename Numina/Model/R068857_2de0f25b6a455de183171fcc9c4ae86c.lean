import Mathlib

theorem algebra_3579 {x : ℝ} (hx : x ≠ 0) (h : x + 1/x = 10) :
    x^3 + 1 / x^3 = 970 := by
  have h1 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
    field_simp
    ring
  rw [h1, h]
  norm_num