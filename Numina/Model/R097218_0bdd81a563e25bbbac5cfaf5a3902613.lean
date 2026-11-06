import Mathlib

theorem algebra_239396 (v : ℝ) (h : v > 0) (h1 : 1 / v = 30) (h2 : 2 / v = 18) :
    3 / v = 24 ∨ 3 / v = 72 := by
  have h3 : v ≠ 0 := by linarith
  have h4 : v = 1 / 30 := by
    field_simp [h3] at h1
    linarith
  have h5 : v = 1 / 9 := by
    field_simp [h3] at h2
    linarith
  exfalso
  linarith [h4, h5]