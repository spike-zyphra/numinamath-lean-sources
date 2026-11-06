import Mathlib

theorem algebra_234509 (v : ℝ) (h : v > 0) (h1 : 5 / v = 5 / (1.25 * v) + 5 / v) :
    5 / v = 4 := by
  have h2 : v > 0 := h
  have h3 : v > 0 := h
  field_simp [h2] at h1 ⊢
  norm_num at h1 ⊢
  nlinarith [h2, h1]