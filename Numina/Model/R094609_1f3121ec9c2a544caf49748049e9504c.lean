import Mathlib

theorem algebra_2163 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : (1 + a / 100) * (1 - b / 100) = 1) :
    b = 100 * a / (100 + a) := by
  have h1 : (1 + a / 100) * (1 - b / 100) = 1 := h
  have h2 : 100 * a = 100 * b + a * b := by
    have h3 : (1 + a / 100) * (1 - b / 100) - 1 = 0 := by
      linarith 
    have h4 : a / 100 - b / 100 - a * b / 10000 = 0 := by
      have h5 : (1 + a / 100) * (1 - b / 100) - 1 = 0 := h3
      linarith [h5]
    have h5 : 100 * a - 100 * b - a * b = 0 := by
      field_simp at h4
      linarith 
    linarith 
  have h3 : 100 + a ≠ 0 := by
    linarith [show 0 < a from ha]
  field_simp at *
  nlinarith