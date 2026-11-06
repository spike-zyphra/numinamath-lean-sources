import Mathlib

theorem algebra_13417 {x : ℚ} (hx : x ≠ 0) (h : x + 1/x = 23) :
    x^3 + 1/x^3 = 12098 := by
  have h1 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
    field_simp
    ring
  rw [h1, h]
  norm_num