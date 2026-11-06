import Mathlib

theorem algebra_169307 (v : ℝ) (h : v > 0) (h' : (15 / v) * (1 - 120 / 100) = 15) :
    (15 / v) * (1 - 120 / 100) + 15 = 75 := by
  have h1 : v > 0 := h
  field_simp at h' ⊢
  nlinarith [h']