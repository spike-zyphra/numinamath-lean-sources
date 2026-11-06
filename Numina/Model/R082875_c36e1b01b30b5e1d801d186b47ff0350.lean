import Mathlib

theorem algebra_192383 {a : ℝ} (ha : a ≠ 0) (h : a + 1 / a = 3) :
    a ^ 3 + 1 / a ^ 3 = 18 := by
  have h1 : a ^ 3 + 1 / a ^ 3 = (a + 1 / a) ^ 3 - 3 * (a + 1 / a) := by
    field_simp [pow_two, pow_three, ha]
    ring
  rw [h1, h]
  norm_num