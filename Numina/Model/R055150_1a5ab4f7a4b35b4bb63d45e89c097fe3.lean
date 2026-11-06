import Mathlib

theorem algebra_140538 (v : ℝ) (h : v > 0) (h' : 40 / (v + 20) = 40 / v - 20 / 60) :
    v = 40 := by
  have h1 : v + 20 ≠ 0 := by nlinarith 
  have h2 : v ≠ 0 := by nlinarith
  field_simp [h1, h2] at h'
  nlinarith [sq_nonneg (v + 10), h]