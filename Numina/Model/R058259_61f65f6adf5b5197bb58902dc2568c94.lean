import Mathlib

theorem algebra_175060 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a / b = 3 / 2) (h1 : a * 7 = b * 9) :
    a * 13 = b * 15 := by
  have h2 : a = 3 / 2 * b := by
    have h_pos : 0 < b := hb
    field_simp at h
    linarith
  rw [h2] at h1
  nlinarith