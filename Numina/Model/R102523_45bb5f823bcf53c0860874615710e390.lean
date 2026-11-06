import Mathlib

theorem algebra_20677 (x : ℝ) (hx : x = 14 * 5) (h : 105 / x = y / (16 * 13)) :
    y = 312 := by
  rw [hx] at h
  field_simp at h ⊢
  linarith