import Mathlib

theorem algebra_117055 (x : ℝ) (hx : x > 0) (h : (1 / 3) / x = 185 / (1.2 * x)) :
    (2 / 3) / x = 180 := by 
  have h1 : x ≠ 0 := by linarith
  have h3 : (1 / 3 : ℝ) = 185 / (1.2 : ℝ) := by
    have h4 : x ≠ 0 := h1
    field_simp at h ⊢
    nlinarith
  norm_num at h3
  all_goals linarith