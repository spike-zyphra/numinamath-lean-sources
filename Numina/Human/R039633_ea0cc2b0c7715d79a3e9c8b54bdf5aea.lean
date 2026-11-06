import Mathlib

theorem algebra_264674 (x : ℝ) (h : x ≠ -1) (h' : 6 / (x + 1) = 3 / 2) : x = 3 := by
  have h1 : x + 1 ≠ 0 := by
    intro hx
    apply h
    linarith
  field_simp [h1] at h'
  linarith