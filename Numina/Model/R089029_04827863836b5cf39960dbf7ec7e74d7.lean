import Mathlib

theorem algebra_1516 {a : ℝ} (h : a ≠ 0) (h1 : a + 1 / a = 3) :
    a ^ 6 + 1 / a ^ 6 = 322 := by
  have h2 : a ^ 2 + 1 / a ^ 2 = 7 := by
    have : a ^ 2 + 1 / a ^ 2 = (a + 1 / a) ^ 2 - 2 := by
      field_simp
      ring
    rw [this, h1]
    norm_num
  have h3 : a ^ 3 + 1 / a ^ 3 = 18 := by
    have : a ^ 3 + 1 / a ^ 3 = (a + 1 / a) ^ 3 - 3 * (a + 1 / a) := by
      field_simp
      ring
    rw [this, h1]
    norm_num
  have h6 : a ^ 6 + 1 / a ^ 6 = (a ^ 3 + 1 / a ^ 3) ^ 2 - 2 := by
    field_simp
    ring
  rw [h6, h3]
  all_goals norm_num