import Mathlib

theorem algebra_32502 (x : ℝ) (hx : x ≠ 0) (h : 3 / x = 8 / 24) :
    x = 9 := by 
  field_simp [hx] at h
  linarith