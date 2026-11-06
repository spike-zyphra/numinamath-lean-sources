import Mathlib

theorem algebra_1712 (v : ℝ) (h : 0 < v) (h' : 25 / v = (55 - 25) / (2 * v) + 1) :
    v = 10 := by
  have h1 : 25 / v - (55 - 25) / (2 * v) = 1 := by linarith
  have h2 : 25 / v - (55 - 25) / (2 * v) = 10 / v := by
    field_simp
    ring
  rw [h2] at h1
  have : v ≠ 0 := by linarith
  field_simp at h1
  linarith