import Mathlib

theorem algebra_274076 (v : ℝ) (h : v > 0) (h' : 250 / (10 + v) = 3 * 60 + 18) :
    v = 3 := by
  have h1 : 250 / (10 + v) = 198 := by
    norm_num at h' ⊢
    linarith
  have h2 : 10 + v ≠ 0 := by
    linarith [show v > 0 from h]
  have h3 : 250 = (3 * 60 + 18) * (10 + v) := by
    have h4 : 10 + v ≠ 0 := h2
    field_simp [h4] at h1 ⊢
    linarith
  norm_num at h3
  nlinarith