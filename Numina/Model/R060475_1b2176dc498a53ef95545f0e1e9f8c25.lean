import Mathlib

theorem algebra_738 (t : ℝ) (ht : t > 0) (h : 10/1.2 = 10 - 40/60 + 10/t) : t = 68 := by
  field_simp at h
  nlinarith