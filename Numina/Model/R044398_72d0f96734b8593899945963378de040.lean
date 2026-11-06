import Mathlib

theorem algebra_250753 (d : ℝ) (h : d > 0) (h1 : d / 80 = d / 70 - 15 / 60) :
    d = 140 := by 
  field_simp at h1 ⊢
  linarith