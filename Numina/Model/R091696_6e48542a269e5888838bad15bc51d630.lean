import Mathlib

theorem algebra_171855 (d : ℝ) (h : d > 0) (h1 : (2 * d) / (1.5 * 1000) = 8) :
    d = 6000 := by
  have h2 : 2 * d = 8 * (1.5 * 1000) := by
    field_simp at h1
    linarith 
  have h3 : 2 * d = 12000 := by
    norm_num at h2 ⊢
    linarith 
  have h4 : d = 6000 := by 
    linarith 
  linarith