import Mathlib

theorem algebra_166599 (d : ℝ) (h : d = 24) (v1 v2 : ℝ)
    (h1 : v1 = 8) (h2 : v2 > 0) :
    (d / (d * (2 / 3) / v1 + d * (1 / 3) / v2)) ≠ 12 := by
  rw [h]
  rw [h1]
  intro h'
  field_simp at h'
  nlinarith