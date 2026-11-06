import Mathlib

theorem algebra_258196 (d : ℝ) (h : d > 0) (h1 : 4 / d = 2 / (d - 4)) :
    d = 8 := by

  have h2 : d ≠ 0 := by linarith
  have h3 : d - 4 ≠ 0 := by 
    by_contra h4
    have h4' : d = 4 := by linarith
    rw [h4'] at h1
    field_simp [h4'] at h1
    all_goals linarith [h4']
    
  field_simp [h2, h3] at h1
  
  nlinarith [h1, h2, h3, h]