import Mathlib

theorem algebra_178234 (v : ℝ) (h : v > 0) (h' : (60 / (v + 15)) = (60 / v) - 12 / 60) :
    v = 60 := by
  have h1 : v + 15 ≠ 0 := by
    by_contra h2
    have : v = -15 := by linarith
    linarith
  have h2 : v ≠ 0 := by linarith
  field_simp [h1, h2] at h'
  nlinarith [sq_nonneg (v - 60), sq_nonneg (v + 75), h]