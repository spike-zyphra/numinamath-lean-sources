import Mathlib

theorem algebra_52269 (d1 d2 v1 v2 : ℝ) (h1 : d1 / v1 = 9) (h2 : d2 / v2 = 17)
    (h3 : v2 = v1 + 6.5) (h4 : (d1 + d2) / (d1 / v1 + d2 / v2) = 30) :
    d1 + d2 = 780 := by
  have h5 : d1 / v1 + d2 / v2 = 26 := by
    have h6 : d1 / v1 = 9 := h1
    have h7 : d2 / v2 = 17 := h2
    linarith
  have h8 : (d1 + d2) / (d1 / v1 + d2 / v2) = 30 := h4
  rw [show d1 / v1 + d2 / v2 = (26 : ℝ) by linarith [h5]] at h8
  have h9 : d1 + d2 = 780 := by
    field_simp at h8 ⊢
    linarith
  linarith