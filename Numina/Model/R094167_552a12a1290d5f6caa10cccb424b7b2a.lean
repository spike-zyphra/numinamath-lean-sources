import Mathlib

theorem algebra_4671 {x : ℚ} (hx : x ≠ 0) (h : x + 1/x = 5) :
    x^2 + 1/x^2 = 23 := by
  have h1 : x^2 + 1/x^2 = (x + 1/x) ^ 2 - 2 := by
    field_simp
    <;> ring
  rw [h1, h]
  norm_num