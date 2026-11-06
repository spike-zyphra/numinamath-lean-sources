import Mathlib

theorem algebra_260256 (d : ℝ) (h₀ : d > 0) (h₁ : 120 / d = 140 / (d - 120)) (h₂ : 126 / (d - 120) = 140 / d) :
    d = 210 := by
  have h3 : d ≠ 0 := by linarith 
  have h4 : d - 120 ≠ 0 := by
    by_contra h
    have h5 : d = 120 := by linarith 
    rw [h5] at h₁ h₂ 
    norm_num [h5] at h₁ h₂ 
    all_goals linarith 
  field_simp [h3, h4] at h₁ h₂ 
  nlinarith [sq_pos_of_ne_zero (show d ≠ 0 by linarith), sq_pos_of_ne_zero (show d - 120 ≠ 0 by 
    intro h
    apply h4 
    linarith 
  ) ]