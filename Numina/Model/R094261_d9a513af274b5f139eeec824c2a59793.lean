import Mathlib

theorem algebra_6478 {a b : ℝ} (ha : a + b = 11) (hb : a * b = 8) :
    a ^ 3 * b + a * b ^ 3 = 840 := by
  have h1 : a ^ 3 * b + a * b ^ 3 = (a * b) * (a ^ 2 + b ^ 2) := by
    ring
  have h2 : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by
    ring
  rw [h1]
  rw [h2, ha, hb]
  norm_num