import Mathlib

theorem algebra_5347 (v : ℝ) (h : 15 / (v + 2) = 9 / (v - 2)) : v = 8 := by 
  have h1 : v + 2 ≠ 0 := by 
    by_contra h2 
    have : v = -2 := by linarith 
    rw [this] at h 
    norm_num at h 
    all_goals linarith 
  have h2 : v - 2 ≠ 0 := by 
    by_contra h3 
    have : v = 2 := by linarith 
    rw [this] at h 
    norm_num at h 
    all_goals linarith 
  field_simp [(show v + 2 ≠ 0 by assumption), (show v - 2 ≠ 0 by assumption)] at h
  linarith