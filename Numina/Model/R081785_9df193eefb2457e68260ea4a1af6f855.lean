import Mathlib

theorem algebra_2614 : (78 ^ 3 + 22 ^ 3 : ℝ) / (78 ^ 2 - 78 * 22 + 22 ^ 2) = 100 := by
  have h1 : (78 : ℝ) ^ 3 + (22 : ℝ) ^ 3 = (78 + 22) * ((78 : ℝ) ^ 2 - 78 * 22 + (22 : ℝ) ^ 2) := by
    ring
  rw [h1]
  field_simp
  <;> norm_num