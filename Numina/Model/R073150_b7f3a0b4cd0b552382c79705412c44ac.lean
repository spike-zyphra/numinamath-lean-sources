import Mathlib

theorem algebra_194361 (d v : ℝ) (h₀ : d = 60) (h₁ : v > 0) (h₂ : d / (20 + v) + d / (20 - v) = 6.25) :
    v = 4 := by
  rw [h₀] at h₂
  have h3 : (20 + v) ≠ 0 := by
    by_contra h4
    have : v = -20 := by linarith
    rw [this] at h₂
    norm_num at h₂
    all_goals linarith
  
  have h4 : (20 - v) ≠ 0 := by
    by_contra h5
    have : v = 20 := by linarith
    rw [this] at h₂
    norm_num at h₂
  
  have eq1 : 60 / (20 + v) + 60 / (20 - v) - 6.25 = 0 := by 
    linarith
  
  have eq2 : 60 * (20 - v) + 60 * (20 + v) - 6.25 * ((20 + v) * (20 - v)) = 0 := by 
    have h5 : (20 + v) ≠ 0 := h3
    have h6 : (20 - v) ≠ 0 := h4
    field_simp [(show (20 + v) ≠ 0 by exact h5), (show (20 - v) ≠ 0 by exact h6)] at eq1 ⊢
    nlinarith
  
  have h5 : v^2 = 16 := by 
    nlinarith
  
  have h6 : v = 4 := by 
    nlinarith [h₁]

  exact h6